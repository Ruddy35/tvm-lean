-- Wallet v5r1 (ton-blockchain/wallet-contract-v5, wallet_v5.fc; tools/txoracle/contracts.txt#wallet5.code):
-- the data is `is_signature_allowed:int1 seqno:uint32 wallet_id:uint32 public_key:uint256
-- extensions:(HashmapE 256 ...)`. Invariant: the data is such a cell with the public key `key`, the
-- wallet id `wid` and a seqno of at least `n`, its extensions (if any) a well-formed dictionary of
-- 256-bit keys (`Dict.WF`: what `udict_add_builder?`, `udict_delete?` and `udict_get?` need to be read
-- as a map), and signatures allowed when there is no extension. For every `n` it holds after every
-- transaction when it held before: the key and the wallet id never change, the seqno never
-- decreases, signatures are disallowed only while there are extensions
-- (`error::disable_signature_when_extensions_is_empty`,
-- `error::remove_last_extension_when_signature_disabled`; a signed request allows them again), and
-- the code never changes.
-- contract-check: invariant Inv key wid n
-- contract-check: params (key wid n : Nat)
-- contract-check: hints Data.bits, extract_bit_empty, extract_bit_past, extract_bit_all, loadIntValue_bit, twosBits_true, twosBits_false, twosBits_ite
-- contract-check: loop 2 SendList
-- contract-check: loop 1 Actions key wid n

/-- The fields of the data before the dictionary of extensions. -/
structure Data where
  signatureAllowed : Bool
  seqno : Nat
  walletId : Nat
  publicKey : Nat

/-- The flag in one bit, `seqno` and `wallet_id` in 32 bits each, `public_key` in 256. -/
def Data.bits (d : Data) : BitString :=
  #[d.signatureAllowed] ++ natToBits d.seqno 32 ++ natToBits d.walletId 32 ++ natToBits d.publicKey 256

/-! The run reads the data as `extract`s of the concatenation (`Array.extract_append`); the lemmas
of `ran_case` reduce those of the `natToBits` fields (`extract_natToBits_*`,
TvmLean/Proofs/Check/Tactic.lean), these those of a one-bit field `#[b]` (the flag of signatures,
the flag of the dictionary). Without them the reads of the fields after the flag stay
`bitsToNat (#[b].extract 0 0 ++ natToBits ..)` and the run stops at `CHKSIGNU`. -/

theorem extract_bit_empty (b : Bool) (i j : Nat) (h : j ≤ i) : (#[b] : BitString).extract i j = #[] :=
  Array.extract_eq_empty_of_le (by simp; omega)

theorem extract_bit_past (b : Bool) (i j : Nat) (h : 1 ≤ i) : (#[b] : BitString).extract i j = #[] :=
  Array.extract_eq_empty_of_le (by simp; omega)

theorem extract_bit_all (b : Bool) (j : Nat) (h : 1 ≤ j) : (#[b] : BitString).extract 0 j = #[b] :=
  Array.extract_eq_self_of_le (by simp; omega)

/-- The flag read by `load_int(1)`: `-1` or `0`. -/
theorem loadIntValue_bit (b : Bool) : Spec.loadIntValue false #[b] = if b then -1 else 0 := by
  cases b <;> rfl

/-- The flag `store_int(true, 1)` and `store_int(0, 1)` write (`STI 1` of `-1`, of `0`). -/
theorem twosBits_true : twosBits (-1) 1 = #[true] := rfl

theorem twosBits_false : twosBits 0 1 = #[false] := rfl

/-- The flag read back (`store_int(is_signature_allowed, 1)` of a flag `load_int(1)` read). -/
theorem twosBits_ite (b : Bool) : twosBits (if b then -1 else 0) 1 = #[b] := by
  cases b <;> rfl

/-- The data is the fields within their widths, with the key `key`, the wallet id `wid` and a seqno
of at least `n`, then no extension (the bit `0`; signatures allowed) or a well-formed dictionary of
them (the bit `1` and its root). -/
def Inv (key wid n : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, d.seqno < 2 ^ 32 ∧ d.walletId < 2 ^ 32 ∧ d.publicKey < 2 ^ 256 ∧
    d.publicKey = key ∧ d.walletId = wid ∧ n ≤ d.seqno ∧
    ((data = some (Cell.mkOrdinary (d.bits ++ #[false]) #[]) ∧ d.signatureAllowed = true) ∨
      ∃ e : Cell, data = some (Cell.mkOrdinary (d.bits ++ #[true]) #[e]) ∧ Dict.WF (some e) 256)

/-- The head of the loop over the send-message actions of the action list (`verify_c5_actions`,
its stack `cs count`): the rest of the list a slice, the count an integer. -/
def SendList (cs count : Value) : Prop :=
  (∃ s, cs = .slice s) ∧ ∃ m : Int, count = .int (.num m)

/-- The head of the loop over the other actions (`process_actions`, `while (true)`, its top stack
entry the rest of the actions): a slice, and the data, which each action may set (an extension
added or removed, signatures allowed or not), satisfying the invariant. -/
def Actions (key wid n : Nat) (cs : Value) (data : Cell) : Prop :=
  (∃ s, cs = .slice s) ∧ Inv key wid n (some data)

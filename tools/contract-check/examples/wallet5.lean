-- Wallet v5r1 (ton-blockchain/wallet-contract-v5, wallet_v5.fc; tools/txoracle/contracts.txt#wallet5.code):
-- the data is `is_signature_allowed:int1 seqno:uint32 wallet_id:uint32 public_key:uint256
-- extensions:(HashmapE 256 ...)`. Invariant: the data is such a cell with the public key `key`, the
-- wallet id `wid` and a seqno of at least `n`. For every `n` it holds after every transaction when it
-- held before: the key and the wallet id never change and the seqno never decreases (and the code
-- never changes).
-- contract-check: invariant Inv key wid n
-- contract-check: params (key wid n : Nat)
-- contract-check: hints Data.encode, extract_bit_empty, extract_bit_past, extract_bit_all, loadIntValue_bit

/-- The fields of the data; `extensions` is the root of the dictionary of extensions, if any. -/
structure Data where
  signatureAllowed : Bool
  seqno : Nat
  walletId : Nat
  publicKey : Nat
  extensions : Option Cell

/-- The data cell: the flag in one bit, `seqno`, `wallet_id` in 32 bits, `public_key` in 256, the
dictionary as `Maybe ^Cell`. -/
def Data.encode (d : Data) : Cell :=
  Cell.mkOrdinary (#[d.signatureAllowed] ++ natToBits d.seqno 32 ++ natToBits d.walletId 32 ++
    natToBits d.publicKey 256 ++ #[d.extensions.isSome]) d.extensions.toArray

/-! The run reads the data as `extract`s of the concatenation (`Array.extract_append`); the lemmas
of `ran_case` reduce those of the `natToBits` fields (`extract_natToBits_*`,
TvmLean/Proofs/Check/Tactic.lean), these those of a one-bit field `#[b]`. Without them the reads of
the fields before the bit stay `bitsToNat (natToBits .. ++ #[b].extract 0 0)` and the run stops at
`CHKSIGNU`. -/

theorem extract_bit_empty (b : Bool) (i j : Nat) (h : j ≤ i) : (#[b] : BitString).extract i j = #[] :=
  Array.extract_eq_empty_of_le (by simp; omega)

theorem extract_bit_past (b : Bool) (i j : Nat) (h : 1 ≤ i) : (#[b] : BitString).extract i j = #[] :=
  Array.extract_eq_empty_of_le (by simp; omega)

theorem extract_bit_all (b : Bool) (j : Nat) (h : 1 ≤ j) : (#[b] : BitString).extract 0 j = #[b] :=
  Array.extract_eq_self_of_le (by simp; omega)

/-- The flag read by `load_int(1)`: `-1` or `0`. -/
theorem loadIntValue_bit (b : Bool) : Spec.loadIntValue false #[b] = if b then -1 else 0 := by
  cases b <;> rfl

/-- The data is `encode` of fields within their widths, with the key `key`, the wallet id `wid` and a
seqno of at least `n`. -/
def Inv (key wid n : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.seqno < 2 ^ 32 ∧ d.walletId < 2 ^ 32 ∧ d.publicKey < 2 ^ 256 ∧
    d.publicKey = key ∧ d.walletId = wid ∧ n ≤ d.seqno

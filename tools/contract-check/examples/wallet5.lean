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
-- contract-check: hints Data.bits, extract_bit_empty, extract_bit_past, extract_bit_all, loadIntValue_bit, twosBits_true, twosBits_false, twosBits_ite, twosBits_readBit, SafeActs.walk_start, SafeActs.walk_sdbegins, SafeActs.walk_sdbegins_const
-- contract-check: loop 4 ActionWalk
-- contract-check: loop 1 Actions key wid n

/-- The fields of the data that may change, before the wallet id and the key. -/
structure Data where
  signatureAllowed : Bool
  seqno : Nat

/-- The flag in one bit, `seqno` and the wallet id `wid` in 32 bits each, the key `key` in 256. The
wallet id and the key are the parameters themselves (not fields equal to them): a data the action
loop sets is compared with the invariant field by field (`Actions`). -/
def Data.bits (wid key : Nat) (d : Data) : BitString :=
  #[d.signatureAllowed] ++ natToBits d.seqno 32 ++ natToBits wid 32 ++ natToBits key 256

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

/-- The flag of a request stored as read (`action_set_signature_auth_allowed`: `load_int(1)` of the
request, then `store_int(is_signature_allowed, 1)` of it): the bit read. A slice of no bit left
reads `#[]`, `0`, stored as the bit `false`, which `[0]!` of `#[]` is too. -/
theorem twosBits_readBit (s : Slice) :
    twosBits (Spec.loadIntValue false (s.readBits 1)) 1 = #[(s.readBits 1)[0]!] := by
  have h : (s.readBits 1).size ≤ 1 := by simp [Slice.readBits]; omega
  generalize s.readBits 1 = bs at h ⊢
  rcases bs with ⟨_ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · decide
  · cases b <;> decide
  · simp at h

/-- The data is the flag, a seqno of at least `n` within 32 bits, the wallet id `wid` and the key
`key` (within their widths), then no extension (the bit `0`; signatures allowed) or a well-formed
dictionary of them (the bit `1` and its root). -/
def Inv (key wid n : Nat) (data : Option Cell) : Prop :=
  wid < 2 ^ 32 ∧ key < 2 ^ 256 ∧ ∃ d : Data, d.seqno < 2 ^ 32 ∧ n ≤ d.seqno ∧
    ((data = some (Cell.mkOrdinary (d.bits wid key ++ #[false]) #[]) ∧ d.signatureAllowed = true) ∨
      ∃ e : Cell, data = some (Cell.mkOrdinary (d.bits wid key ++ #[true]) #[e]) ∧ Dict.WF (some e) 256)

/-! The action list of a request (`c5_actions`, a reference of the message) is checked node by
node (`verify_c5_actions`: the tag of `action_send_msg`, `x{0ec3c86d} SDBEGINS`, 8 bits and 2
references after it, down to an empty slice) before it becomes the action list: a list of
`SafeActs` (TvmLean/Proofs/Tx/NoSetCode.lean: `SafeActs.sendTag`, `SafeActs.terminal`), which has
no `SETCODE`. The loop of the walk keeps `SafeActs node → SafeActs c` (`ActionWalk`), from the start
(`SafeActs.walk_start`) node by node (`SafeActs.walk_sdbegins`, `SafeActs.walk_sdbegins_const` with
the tag as the step of `SDBEGINS` states it) to the end of the list
(`SafeActs.of_walk_end`; TvmLean/Proofs/Check/Tactic.lean). -/

/-- The head of the walk over the action list (`verify_c5_actions`, its stack `c5_actions
is_external cs count`): the list `c`, the slice of the node `node` the walk is at with
`SafeActs node → SafeActs c`, the flag and the count integers. -/
def ActionWalk (d x s count : Value) : Prop :=
  (∃ c node : Cell, d = .cell c ∧ s = .slice (Slice.ofCell node) ∧ (SafeActs node → SafeActs c)) ∧
    (∃ e : Int, x = .int (.num e)) ∧ ∃ m : Int, count = .int (.num m)

/-- The head of the loop over the other actions (`process_actions`, `while (true)`, its top stack
entry the rest of the actions): a slice, and the data, which each action may set (an extension
added or removed, signatures allowed or not), satisfying the invariant. -/
def Actions (key wid n : Nat) (cs : Value) (data : Cell) : Prop :=
  (∃ s, cs = .slice s) ∧ Inv key wid n (some data)

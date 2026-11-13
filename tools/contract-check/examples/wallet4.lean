-- Wallet v4r2 (ton-blockchain/wallet-contract, wallet-v4-code.fc; tools/txoracle/contracts.txt#wallet4.code):
-- the data is `seqno:uint32 subwallet_id:uint32 public_key:uint256 plugins:(HashmapE 264 ...)`.
-- Invariant: the data is such a cell with the public key `key`, the subwallet `sub` and a seqno of at
-- least `n`, and its plugins (if any) a well-formed dictionary of 264-bit keys (`Dict.WF`: what
-- `dict_add_builder?`, `dict_delete?` and `dict_get?` need to be read as a map). For every `n` it
-- holds after every transaction when it held before: the key and the subwallet never change, the
-- seqno never decreases, and the code never changes.
-- contract-check: invariant Inv key sub n
-- contract-check: params (key sub n : Nat)
-- contract-check: hints Data.bits, extract_bit_empty, extract_bit_past, extract_bit_all

/-- The fields of the data before the dictionary of plugins. -/
structure Data where
  seqno : Nat
  subwallet : Nat
  publicKey : Nat

/-- `seqno` and `subwallet_id` in 32 bits each, `public_key` in 256. -/
def Data.bits (d : Data) : BitString :=
  natToBits d.seqno 32 ++ natToBits d.subwallet 32 ++ natToBits d.publicKey 256

/-! The run reads the data as `extract`s of the concatenation (`Array.extract_append`); the lemmas
of `ran_case` reduce those of the `natToBits` fields (`extract_natToBits_*`,
TvmLean/Proofs/Check/Tactic.lean), these those of the one-bit field `#[b]` (the flag of the
dictionary). -/

theorem extract_bit_empty (b : Bool) (i j : Nat) (h : j ≤ i) : (#[b] : BitString).extract i j = #[] :=
  Array.extract_eq_empty_of_le (by simp; omega)

theorem extract_bit_past (b : Bool) (i j : Nat) (h : 1 ≤ i) : (#[b] : BitString).extract i j = #[] :=
  Array.extract_eq_empty_of_le (by simp; omega)

theorem extract_bit_all (b : Bool) (j : Nat) (h : 1 ≤ j) : (#[b] : BitString).extract 0 j = #[b] :=
  Array.extract_eq_self_of_le (by simp; omega)

/-- The data is the fields within their widths, with the key `key`, the subwallet `sub` and a seqno
of at least `n`, then no plugin (the bit `0`) or a well-formed dictionary of them (the bit `1` and
its root). -/
def Inv (key sub n : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, d.seqno < 2 ^ 32 ∧ d.subwallet < 2 ^ 32 ∧ d.publicKey < 2 ^ 256 ∧
    d.publicKey = key ∧ d.subwallet = sub ∧ n ≤ d.seqno ∧
    (data = some (Cell.mkOrdinary (d.bits ++ #[false]) #[]) ∨
      ∃ p : Cell, data = some (Cell.mkOrdinary (d.bits ++ #[true]) #[p]) ∧ Dict.WF (some p) 264)

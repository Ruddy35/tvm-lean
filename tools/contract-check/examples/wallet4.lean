-- Wallet v4r2 (ton-blockchain/wallet-contract, wallet-v4-code.fc; tools/txoracle/contracts.txt#wallet4.code):
-- the data is `seqno:uint32 subwallet_id:uint32 public_key:uint256 plugins:(HashmapE 264 ...)`.
-- Invariant: the data is such a cell with the public key `key`, the subwallet `sub` and a seqno of at
-- least `n`. For every `n` it holds after every transaction when it held before: the key and the
-- subwallet never change and the seqno never decreases (and the code never changes).
-- contract-check: invariant Inv key sub n
-- contract-check: params (key sub n : Nat)
-- contract-check: hints Data.encode, extract_bit_empty, extract_bit_past, extract_bit_all

/-- The fields of the data; `plugins` is the root of the dictionary of plugins, if any. -/
structure Data where
  seqno : Nat
  subwallet : Nat
  publicKey : Nat
  plugins : Option Cell

/-- The data cell: `seqno`, `subwallet_id` in 32 bits, `public_key` in 256, the dictionary as
`Maybe ^Cell`. -/
def Data.encode (d : Data) : Cell :=
  Cell.mkOrdinary (natToBits d.seqno 32 ++ natToBits d.subwallet 32 ++ natToBits d.publicKey 256 ++
    #[d.plugins.isSome]) d.plugins.toArray

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

/-- The data is `encode` of fields within their widths, with the key `key`, the subwallet `sub` and a
seqno of at least `n`. -/
def Inv (key sub n : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.seqno < 2 ^ 32 ∧ d.subwallet < 2 ^ 32 ∧ d.publicKey < 2 ^ 256 ∧
    d.publicKey = key ∧ d.subwallet = sub ∧ n ≤ d.seqno

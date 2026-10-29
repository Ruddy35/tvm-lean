-- Restricted wallet v3 (crypto/smartcont/restricted-wallet3-code.fc): before its first message the
-- data is `seqno:uint32 subwallet:uint32 public_key:uint256 final_public_key:uint256` (seqno 0);
-- the first message (seqno 0, signed by `public_key`) installs `final_public_key` and the
-- `start_at:uint32 rdict:(HashmapE 32 Grams)` it carries; after it the data is `seqno:uint32
-- subwallet:uint32 public_key:uint256 start_at:uint32 rdict`, and an external message signed by the
-- key reserves the part of the balance the dictionary still locks and sends the messages of its
-- references. Invariant: the subwallet never changes, the final key (before the first message) and
-- the key (after it) is `key`, and the dictionary is any root.
-- contract-check: invariant Inv key sub
-- contract-check: params (key sub : Nat)
-- contract-check: hints Data.bits

/-- The fields of the data after the first message, before the dictionary. -/
structure Data where
  seqno : Nat
  subwallet : Nat
  publicKey : Nat
  startAt : Nat

/-- `seqno` and `subwallet` in 32 bits each, `public_key` in 256, `start_at` in 32. -/
def Data.bits (d : Data) : BitString :=
  natToBits d.seqno 32 ++ natToBits d.subwallet 32 ++ natToBits d.publicKey 256 ++ natToBits d.startAt 32

/-- The data: before the first message (seqno `0`, the subwallet `sub`, any key `k`, the final key
`key`), or after it (the fields within their widths, the subwallet `sub`, the key `key`, no
dictionary or one). -/
def Inv (key sub : Nat) (data : Option Cell) : Prop :=
  (∃ k : Nat, k < 2 ^ 256 ∧ key < 2 ^ 256 ∧ sub < 2 ^ 32 ∧
    data = some (Cell.mkOrdinary (natToBits 0 32 ++ natToBits sub 32 ++ natToBits k 256 ++ natToBits key 256) #[])) ∨
  ∃ d : Data, d.seqno < 2 ^ 32 ∧ d.subwallet < 2 ^ 32 ∧ d.publicKey < 2 ^ 256 ∧ d.startAt < 2 ^ 32 ∧
    d.subwallet = sub ∧ d.publicKey = key ∧
    (data = some (Cell.mkOrdinary (d.bits ++ #[false]) #[]) ∨
      ∃ r : Cell, data = some (Cell.mkOrdinary (d.bits ++ #[true]) #[r]))

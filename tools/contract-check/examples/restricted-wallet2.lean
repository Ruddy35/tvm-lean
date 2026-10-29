-- Restricted wallet v2 (crypto/smartcont/restricted-wallet2-code.fc): the data is `seqno:uint32
-- public_key:uint256 start_at:uint32 rdict:(HashmapE 32 Grams)`; an external message signed by the
-- key (or the first, with seqno 0) reserves the part of the balance the dictionary still locks
-- (`idict_get_preveq?` at the seconds since `start_at`, or since configuration parameter -13) and
-- sends the messages of its references (`send_raw_message` in a loop), then stores the data with the
-- seqno incremented. Invariant: the data is such a cell with the public key `key`: whatever messages
-- arrive, the key never changes, and the dictionary is the one stored before (any root).
-- contract-check: invariant Inv key
-- contract-check: params (key : Nat)
-- contract-check: hints Data.bits

/-- The fields of the data before the dictionary. -/
structure Data where
  seqno : Nat
  publicKey : Nat
  startAt : Nat

/-- `seqno` in 32 bits, `public_key` in 256, `start_at` in 32. -/
def Data.bits (d : Data) : BitString :=
  natToBits d.seqno 32 ++ natToBits d.publicKey 256 ++ natToBits d.startAt 32

/-- The data: the fields within their widths, the key `key`, and no dictionary (the bit `0`) or a
dictionary (the bit `1` and its root, any cell). -/
def Inv (key : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, d.seqno < 2 ^ 32 ∧ d.publicKey < 2 ^ 256 ∧ d.startAt < 2 ^ 32 ∧ d.publicKey = key ∧
    (data = some (Cell.mkOrdinary (d.bits ++ #[false]) #[]) ∨
      ∃ r : Cell, data = some (Cell.mkOrdinary (d.bits ++ #[true]) #[r]))

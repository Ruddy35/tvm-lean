-- Highload wallet v1 (crypto/smartcont/highload-wallet-code.fc): the data is `seqno:uint32
-- subwallet:uint32 public_key:uint256`; an external message signed by the key sends up to 254
-- messages, one per entry of a dictionary in the message (`idict_get_next?` in a loop). Invariant:
-- the data is such a cell with the public key `key` and the subwallet `sub`: whatever messages
-- arrive, the key and the subwallet never change (and the code never does).
-- contract-check: invariant Inv key sub
-- contract-check: params (key sub : Nat)
-- contract-check: hints Data.encode

/-- The fields of the data. -/
structure Data where
  seqno : Nat
  subwallet : Nat
  publicKey : Nat

/-- The data cell: `seqno` and `subwallet` in 32 bits each, `public_key` in 256 bits. -/
def Data.encode (d : Data) : Cell :=
  Cell.mkOrdinary (natToBits d.seqno 32 ++ natToBits d.subwallet 32 ++ natToBits d.publicKey 256) #[]

/-- The data is `encode` of fields within their widths, with the key `key` and the subwallet `sub`. -/
def Inv (key sub : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.seqno < 2 ^ 32 ∧ d.subwallet < 2 ^ 32 ∧ d.publicKey < 2 ^ 256 ∧
    d.publicKey = key ∧ d.subwallet = sub

-- The simple wallet with procedures (crypto/smartcont/simple-wallet-ext-code.fc: `load_state`,
-- `do_verify_message`, `save_state` called by `CALLDICT`): the data is `seqno:uint32
-- public_key:uint256`. Invariant: the data is such a cell with the public key `key`: whatever
-- messages arrive, the key never changes (and the code never does).
-- contract-check: invariant Inv key
-- contract-check: params (key : Nat)
-- contract-check: hints Data.encode

/-- The fields of the data. -/
structure Data where
  seqno : Nat
  publicKey : Nat

/-- The data cell: `seqno` in 32 bits, `public_key` in 256 bits. -/
def Data.encode (d : Data) : Cell :=
  Cell.mkOrdinary (natToBits d.seqno 32 ++ natToBits d.publicKey 256) #[]

/-- The data is `encode` of fields within their widths, with the public key `key`. -/
def Inv (key : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.seqno < 2 ^ 32 ∧ d.publicKey < 2 ^ 256 ∧ d.publicKey = key

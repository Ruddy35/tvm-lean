-- An upgradable wallet (upgradable-wallet.fif, assembled into upgradable-wallet.boc): the data is
-- `seqno:uint32 public_key:uint256`; an external message signed with the key may install a new code
-- (SETCODE). Invariant: while the code is this one, the data is such a cell with the public key
-- `key`. The condition on a new code: only a message whose body is signed with that key (its first
-- 512 bits: the signature of the hash of the rest) installs one, the first reference of the body.
-- contract-check: invariant Inv key
-- contract-check: params (key : Nat)
-- contract-check: hints Data.encode
-- contract-check: code Signed key

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

/-- The code `c` is installed by a message whose body `b` is signed with the key `key`: its first 512
bits (`(b.readBits 512).extract 0 512`, as the signature slice `LDSLICEX` cuts reads them) are a
signature (`CHKSIGNU`, at some global version) of the hash of the rest of the body, and `c` is the
first reference of the body. Tick-tock (no body) installs none. -/
def Signed (key : Nat) (body : Option Slice) (c : Cell) : Prop :=
  ∃ b, body = some b ∧ c = b.cell.refs[b.refPos]! ∧
    ∃ gv, chkSignU gv (cellHash ({ b with bitPos := b.bitPos + 512 } : Slice).toCellRemaining) key
      ((b.readBits 512).extract 0 512) = true

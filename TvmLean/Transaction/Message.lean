import TvmLean.Transaction.Account
import TvmLean.Transaction.StorageStat

/-!
# The inbound message

C++ `Transaction::unpack_input_msg` (`crypto/block/transaction.cpp`): the header
(`int_msg_info` or `ext_in_msg_info`), the optional `StateInit` and the body.
-/

namespace TvmLean.Tx

/-- `MsgAddressInt` (`addr_std$10` or `addr_var$11`, with an optional anycast), kept as the bits it
occupies (C++ keeps the slice). -/
def Reader.msgAddressInt : Reader BitString := do
  let start ← Reader.peek
  let tag ← Reader.uint 2
  if tag < 2 then Reader.fail
  let pfx ← Reader.maybe (do
    let depth ← Reader.uint 5
    if depth = 0 ∨ depth > 30 then Reader.fail
    Reader.bits depth)
  let pfxLen := 1 + (pfx.map (fun p => 5 + p.size)).getD 0
  if tag == 2 then
    let _ ← Reader.bits (8 + 256)
    return start.readBits (2 + pfxLen + 8 + 256)
  else
    let len ← Reader.uint 9
    let _ ← Reader.bits (32 + len)
    return start.readBits (2 + pfxLen + 9 + 32 + len)

/-- `MsgAddressExt`: `addr_none$00` or `addr_extern$01 len:(## 9) external_address:(bits len)`. -/
def Reader.msgAddressExt : Reader BitString := do
  let start ← Reader.peek
  let tag ← Reader.uint 2
  if tag == 0 then return start.readBits 2
  if tag != 1 then Reader.fail
  let len ← Reader.uint 9
  let _ ← Reader.bits len
  return start.readBits (2 + 9 + len)

/-- The fields of `int_msg_info$0` (C++ `CommonMsgInfo::Record_int_msg_info`); for an external
message C++ fills `src`, `dest` and zeros. -/
structure IntMsgInfo where
  ihrDisabled : Bool := false
  bounce : Bool := false
  bounced : Bool := false
  src : BitString
  dest : BitString
  value : Currencies := { grams := 0 }
  extraFlags : Nat := 0
  fwdFee : Nat := 0
  createdLt : Nat := 0
  createdAt : Nat := 0

def Reader.intMsgInfo : Reader IntMsgInfo := do
  if (← Reader.bool) then Reader.fail
  let ihrDisabled ← Reader.bool
  let bounce ← Reader.bool
  let bounced ← Reader.bool
  let src ← Reader.msgAddressInt
  let dest ← Reader.msgAddressInt
  let value ← Reader.currencies
  let extraFlags ← Reader.grams
  let fwdFee ← Reader.grams
  let createdLt ← Reader.uint 64
  let createdAt ← Reader.uint 32
  return { ihrDisabled, bounce, bounced, src, dest, value, extraFlags, fwdFee, createdLt, createdAt }

/-- `ext_in_msg_info$10 src:MsgAddressExt dest:MsgAddressInt import_fee:Grams`. -/
def Reader.extInMsgInfo : Reader (BitString × BitString × Nat) := do
  if (← Reader.uint 2) != 2 then Reader.fail
  return (← Reader.msgAddressExt, ← Reader.msgAddressInt, ← Reader.grams)

/-- The destination of an inbound message as `(wc, addr)` (C++ `t_MsgAddressInt.extract_std_address`
with the anycast rewrite applied). -/
def stdAddressOf (addr : BitString) : Option (Int × BitString) := do
  let ((pfx, wc, a), _) ← (do
      let tag ← Reader.uint 2
      let pfx ← Reader.maybe (do let d ← Reader.uint 5; Reader.bits d)
      if tag == 2 then return (pfx, ← Reader.int 8, ← Reader.bits 256)
      else if tag == 3 then
        let len ← Reader.uint 9
        if len != 256 then Reader.fail
        return (pfx, ← Reader.int 32, ← Reader.bits 256)
      else Reader.fail) (Slice.ofCell (Cell.mkOrdinary addr))
  let p := pfx.getD #[]
  return (wc, p ++ a.extract p.size 256)

end TvmLean.Tx

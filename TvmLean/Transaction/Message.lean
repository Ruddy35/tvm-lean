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
  /-- `extra_flags` has no leading zero byte (`block::tlb::t_Grams.as_integer` reads it) -/
  extraFlagsCanonical : Bool := true

def Reader.intMsgInfo : Reader IntMsgInfo := do
  if (← Reader.bool) then Reader.fail
  let ihrDisabled ← Reader.bool
  let bounce ← Reader.bool
  let bounced ← Reader.bool
  let src ← Reader.msgAddressInt
  let dest ← Reader.msgAddressInt
  let value ← Reader.currencies
  let (extraFlags, extraFlagsCanonical) ← Reader.gramsC
  let fwdFee ← Reader.grams
  let createdLt ← Reader.uint 64
  let createdAt ← Reader.uint 32
  return { ihrDisabled, bounce, bounced, src, dest, value, extraFlags, fwdFee, createdLt, createdAt,
           extraFlagsCanonical }

/-- `ext_in_msg_info$10 src:MsgAddressExt dest:MsgAddressInt import_fee:Grams`. -/
def Reader.extInMsgInfo : Reader (BitString × BitString × Nat) := do
  if (← Reader.uint 2) != 2 then Reader.fail
  return (← Reader.msgAddressExt, ← Reader.msgAddressInt, ← Reader.grams)

/-! ## `block::tlb` validation of a message (`block-parse.cpp`)

`Transaction::serialize` validates the new transaction with the hand-written TL-B code
(`block::tlb::t_Transaction.validate_ref`); the inbound message in it is the only part the
transaction does not build. -/

/-- `block::tlb::MsgAddressInt::validate_skip`: `addr_std` or `addr_var` (not in workchain 0 or -1, and
not of 256 bits in a workchain that fits 8 bits), an anycast of depth 1..30. -/
def Reader.msgAddressIntValid : Reader Unit := do
  let tag ← Reader.uint 2
  if tag < 2 then Reader.fail
  if ← Reader.bool then
    let depth ← Reader.uint 5
    if depth = 0 ∨ depth > 30 then Reader.fail
    let _ ← Reader.bits depth
  if tag == 2 then
    let _ ← Reader.bits (8 + 256)
  else
    let len ← Reader.uint 9
    let wc ← Reader.int 32
    let _ ← Reader.bits len
    if !((wc < -0x80 || wc > 0x7f || len != 256) && wc != 0 && wc != -1) then Reader.fail

/-- `block::tlb::StateInit::validate_skip`: the five optional fields, the references not looked into. -/
def Reader.stateInitValid : Reader Unit := do
  let _ ← Reader.maybe (Reader.uint 5)
  let _ ← Reader.maybe (Reader.uint 2)
  for _ in [0:3] do
    let _ ← Reader.maybe Reader.ref

/-- `block::tlb::t_Message.validate_ref`: the header with `block::tlb` amounts (no leading zero byte,
positive extra currencies), `init:(Maybe (Either StateInit ^StateInit))`, `body:(Either X ^X)`, the
cell read to its end. -/
def messageValid (msg : Cell) : Bool :=
  let r : Reader Unit := do
    if ← Reader.bool then
      if !(← Reader.bool) then
        -- ext_in_msg_info$10 src:MsgAddressExt dest:MsgAddressInt import_fee:Grams
        let _ ← Reader.msgAddressExt
        Reader.msgAddressIntValid
        let _ ← Reader.gramsStrict
      else
        -- ext_out_msg_info$11 src:MsgAddressInt dest:MsgAddressExt created_lt created_at
        Reader.msgAddressIntValid
        let _ ← Reader.msgAddressExt
        let _ ← Reader.bits 96
    else
      let _ ← Reader.bits 3
      Reader.msgAddressIntValid
      Reader.msgAddressIntValid
      let value ← Reader.currencies
      if !value.valid then Reader.fail
      let _ ← Reader.gramsStrict
      let _ ← Reader.gramsStrict
      let _ ← Reader.bits 96
    if ← Reader.bool then
      if ← Reader.bool then
        let c ← Reader.ref
        if c.special || (Reader.runExact Reader.stateInitValid c).isNone then Reader.fail
      else Reader.stateInitValid
    if ← Reader.bool then
      let _ ← Reader.ref
      let rest ← Reader.peek
      if rest.bitsRemaining != 0 || rest.refsRemaining != 0 then Reader.fail
    else
      let _ ← Reader.rest
  !msg.special && (Reader.runExact r msg).isSome

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

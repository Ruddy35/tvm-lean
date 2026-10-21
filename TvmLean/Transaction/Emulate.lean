import TvmLean.Transaction.Action

namespace TvmLean.Tx

/-! ## The emulator (`transaction_emulator_emulate_transaction`) -/

/-- `compute_state` ends with `FAIL_UNLESS(block::tlb::t_Account.validate_ref(new_total_state))`
(transaction.cpp:3733): the address of the new account must pass `block::tlb::MsgAddressInt` (the rest
of the account C++ builds from parts already validated). It does not for an anycast account in
workchain 127, whose address `compute_my_addr` makes `addr_var` of 256 bits. -/
def accountAddrValid (acc : Cell) : Bool :=
  let s := Slice.ofCell acc
  !(s.haveBits 1 && (s.readBits 1)[0]!) || (Reader.run Reader.msgAddressIntValid (s.advanceBits 1).toCellRemaining).isSome

/-- `Account::unpack` of the account at `(wc, addr)`, `fetch_config_params` and the `Transaction`
constructor (`block_lt` is `lt` rounded down to the block). -/
def newTx (cfg : Config) (shardAccount inMsg : Cell) (kind : TxKind) (wc : Int) (addr addrBits : BitString)
    (lt now : Nat) (libs : Option Cell) : Except String (Tx × Array StoragePrices × SizeLimits × GasPrices × MsgPrices) := do
  let special := wc == -1 && cfg.isSpecialSmc addr
  let some account := Account.unpack shardAccount wc addr special | throw "account"
  let account := { account with blockLt := lt - lt % 1000000 }
  -- `fetch_config_params`
  let some pricing := cfg.storagePrices | throw "storage prices"
  let some sl := cfg.sizeLimits | throw "size limits"
  let mc := wc == -1
  let some gas := cfg.gasPrices mc | throw "gas prices"
  let some fwd := cfg.msgPrices mc | throw "msg prices"
  let some _ := cfg.msgPrices (!mc) | throw "msg prices"
  -- the Transaction constructor
  let startLt := Nat.max lt account.lastTransEndLt
  let t : Tx :=
    { cfg, kind, globalLibs := libs, gv := cfg.globalVersion, account, now, startLt, endLt := startLt + 1,
      accStatus := if account.status == .nonexist then .uninit else account.status,
      myAddr := account.myAddr, myAddrExact := account.myAddrExact, balance := account.balance.grams,
      balanceExtra := account.balance.extra, originalBalance := account.balance.grams,
      originalExtra := account.balance.extra, msgBalanceRemaining := 0, msgBalanceValid := kind == .ord,
      duePayment := account.duePayment,
      lastPaid := account.lastPaid, inMsg, inMsgInfo := { src := #[], dest := addrBits },
      inMsgBody := Slice.ofCell Cell.empty, newCode := account.code, newData := account.data,
      newLibrary := account.library, newTick := account.tick, newTock := account.tock,
      newFixedPrefixLength := account.fixedPrefixLength, frozenHash := account.stateHash }
  return (t, pricing, sl, gas, fwd)

/-- The run of an ordinary transaction as the transaction emulator does it: the account at the
address of the `ShardAccount` (or of the message's destination for `account_none`), the
configuration `configRoot`, the time `now`, the logical time `lt`, the block's random seed
`randSeed` (256 bits, not zero), the emulator's libraries `libs`. Returns the transaction and the new
account. -/
def emulate (configRoot shardAccount inMsg : Cell) (now lt : Nat) (randSeed : BitString) (libs : Option Cell := none) :
    Outcome := Id.run do
  let some cfg := Config.decode configRoot | return .failed "config"
  -- the address: of the account, or of the message's destination
  let some (acc, _, _) := Reader.runExact (do return (← Reader.ref, ← Reader.bits 256, ← Reader.uint 64)) shardAccount
    | return .failed "shard account"
  let accS := Slice.ofCell acc
  let addrBits? : Option BitString :=
    if accS.haveBits 1 && (accS.readBits 1)[0]! then
      (Reader.msgAddressInt (accS.advanceBits 1)).map (·.1)
    else
      let m := Slice.ofCell inMsg
      if !m.haveBits 1 then none
      else if !(m.readBits 1)[0]! then (Reader.intMsgInfo m).map (·.1.dest)
      else (Reader.extInMsgInfo m).map (·.1.2.1)
  let some addrBits := addrBits? | return .failed "address"
  let some (wc, addr) := stdAddressOf addrBits | return .failed "address"
  let (t, pricing, sl, gas, fwd) ← match newTx cfg shardAccount inMsg .ord wc addr addrBits lt now libs with
    | .ok r => pure r
    | .error e => return .failed e
  let external := (Slice.ofCell inMsg).haveBits 1 && ((Slice.ofCell inMsg).readBits 1)[0]!
  let t ← match t.unpackInputMsg sl fwd with
    | none => return .failed (if external then "external message rejected" else "cannot unpack the message")
    | some (.error e) => return .unsupported e
    | some (.ok t) => pure t
  let needCredit := !external
  -- storage and credit phases, credit first unless the message bounces
  let credit (t : Tx) : Except String (Option Tx) := if needCredit then t.creditPhaseRun else .ok (some t)
  let t? : Except String (Option Tx) :=
    if t.bounceEnabled then
      match t.storagePhaseRun pricing gas false with
      | none => .ok none
      | some t => credit t
    else
      match credit t with
      | .ok (some t) => .ok (t.storagePhaseRun pricing gas needCredit)
      | r => r
  let t ← match t? with
    | .error e => return .unsupported e
    | .ok none => return .failed "storage or credit phase"
    | .ok (some t) => pure t
  let t ← match t.computePhaseRun gas sl randSeed with
    | .error e => return .unsupported e
    | .ok none => return .failed "compute phase"
    | .ok (some t) => pure t
  if !t.computePhase.accepted && !external && t.computePhase.skipReason == 0 then
    return .failed "not accepted"
  let t ← if t.computePhase.success then
      match t.actionPhaseRun sl with
      | .error e => return .unsupported e
      | .ok none => return .failed "action phase"
      | .ok (some t) => pure t
    else pure t
  let t ← if t.bounceEnabled && (!t.computePhase.success ||
        (t.actionPhase.map (fun ap => ap.stateExceedsLimits || ap.bounce)).getD false) then
      match t.bouncePhaseRun with
      | .error e => return .unsupported e
      | .ok none => return .failed "bounce phase"
      | .ok (some t) => pure t
    else pure t
  if !t.computePhase.accepted && t.inMsgExtern then
    return .externalNotAccepted t.computePhase.exitCode
  -- `serialize` validates the transaction with `block::tlb`: the inbound message must pass (a
  -- `fwd_fee` or an extra currency C++ reads differently fails here, whatever happened before)
  if !messageValid inMsg then return .failed "the transaction fails block::tlb validation"
  let (t, newState) := t.computeState sl
  if !accountAddrValid newState then return .failed "compute_state: the new account fails block::tlb validation"
  let some tx := t.serialize newState | return .failed "serialize"
  return .ok tx newState

/-! ## Tick-tock (`transaction_emulator_emulate_tick_tock_transaction`) -/

/-- A tick (`isTock` false) or tock transaction of the account in `shardAccount` (not `account_none`)
as the emulator runs it: no message, no credit, the storage phase without adjusting a message's
value, the compute and action phases, no bounce. -/
def emulateTickTock (configRoot shardAccount : Cell) (isTock : Bool) (now lt : Nat) (randSeed : BitString)
    (libs : Option Cell := none) : Outcome := Id.run do
  let some cfg := Config.decode configRoot | return .failed "config"
  let some (acc, _, _) := Reader.runExact (do return (← Reader.ref, ← Reader.bits 256, ← Reader.uint 64)) shardAccount
    | return .failed "shard account"
  let accS := Slice.ofCell acc
  if !(accS.haveBits 1 && (accS.readBits 1)[0]!) then return .failed "tick-tock on account_none"
  let some addrBits := (Reader.msgAddressInt (accS.advanceBits 1)).map (·.1) | return .failed "address"
  let some (wc, addr) := stdAddressOf addrBits | return .failed "address"
  let (t, pricing, sl, gas, _) ← match newTx cfg shardAccount Cell.empty (if isTock then .tock else .tick) wc addr
      addrBits lt now libs with
    | .ok r => pure r
    | .error e => return .failed e
  let some t := t.storagePhaseRun pricing gas false | return .failed "storage phase"
  let t ← match t.computePhaseRun gas sl randSeed with
    | .error e => return .unsupported e
    | .ok none => return .failed "compute phase"
    | .ok (some t) => pure t
  if !t.computePhase.accepted && t.computePhase.skipReason == 0 then
    return .failed "not accepted"
  let t ← if t.computePhase.success then
      match t.actionPhaseRun sl with
      | .error e => return .unsupported e
      | .ok none => return .failed "action phase"
      | .ok (some t) => pure t
    else pure t
  let (t, newState) := t.computeState sl
  if !accountAddrValid newState then return .failed "compute_state: the new account fails block::tlb validation"
  let some tx := t.serialize newState | return .failed "serialize"
  return .ok tx newState

end TvmLean.Tx

import TvmLean.Transaction.Action

namespace TvmLean.Tx

/-! ## The emulator (`transaction_emulator_emulate_transaction`) -/

/-- The run of an ordinary transaction as the transaction emulator does it: the account at the
address of the `ShardAccount` (or of the message's destination for `account_none`), the
configuration `configRoot`, the time `now`, the logical time `lt`, the block's random seed
`randSeed` (256 bits, not zero). Returns the transaction and the new account. -/
def emulate (host : Host) (configRoot shardAccount inMsg : Cell) (now lt : Nat) (randSeed : BitString) : Outcome := Id.run do
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
  let special := wc == -1 && cfg.isSpecialSmc addr
  let some account := Account.unpack shardAccount wc addr special | return .failed "account"
  let account := { account with blockLt := lt - lt % 1000000 }
  -- `fetch_config_params`
  let some pricing := cfg.storagePrices | return .failed "storage prices"
  let some sl := cfg.sizeLimits | return .failed "size limits"
  let mc := wc == -1
  let some gas := cfg.gasPrices mc | return .failed "gas prices"
  let some fwd := cfg.msgPrices mc | return .failed "msg prices"
  let some _ := cfg.msgPrices (!mc) | return .failed "msg prices"
  if account.balance.extra.isSome then return .unsupported "extra currencies"
  -- the Transaction constructor
  let startLt := Nat.max lt account.lastTransEndLt
  let t : Tx :=
    { cfg, gv := cfg.globalVersion, account, now, startLt, endLt := startLt + 1,
      accStatus := if account.status == .nonexist then .uninit else account.status,
      myAddr := account.myAddr, myAddrExact := account.myAddrExact, balance := account.balance.grams,
      originalBalance := account.balance.grams, msgBalanceRemaining := 0, duePayment := account.duePayment,
      lastPaid := account.lastPaid, inMsg, inMsgInfo := { src := #[], dest := addrBits },
      inMsgBody := Slice.ofCell Cell.empty, newCode := account.code, newData := account.data,
      newLibrary := account.library, newTick := account.tick, newTock := account.tock,
      newFixedPrefixLength := account.fixedPrefixLength, frozenHash := account.stateHash }
  let external := (Slice.ofCell inMsg).haveBits 1 && ((Slice.ofCell inMsg).readBits 1)[0]!
  let t ← match t.unpackInputMsg sl fwd with
    | none => return .failed (if external then "external message rejected" else "cannot unpack the message")
    | some (.error e) => return .unsupported e
    | some (.ok t) => pure t
  let needCredit := !external
  -- storage and credit phases, credit first unless the message bounces
  let t? : Option Tx :=
    if t.bounceEnabled then do
      let t ← t.storagePhaseRun pricing gas false
      return if needCredit then t.creditPhaseRun else t
    else
      let t := if needCredit then t.creditPhaseRun else t
      t.storagePhaseRun pricing gas needCredit
  let some t := t? | return .failed "storage phase"
  let t ← match t.computePhaseRun host gas sl randSeed with
    | .error e => return .unsupported e
    | .ok t => pure t
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
  let (t, newState) := t.computeState sl
  let some tx := t.serialize newState | return .failed "serialize"
  return .ok tx newState

end TvmLean.Tx

import TvmLean.Semantics
import TvmLean.Semantics.Contract
import TvmLean.Transaction.Message
import TvmLean.Transaction.Extra

/-!
# An ordinary transaction

C++ `block::transaction::Transaction` (`crypto/block/transaction.cpp`) for an ordinary transaction
(`tr_ord`) on an inbound message, in the order of the transaction emulator
(`emulator/transaction-emulator.cpp`, `create_transaction`): the inbound message, the storage and
credit phases (credit first unless the message bounces), the compute phase, the action phase and
the bounce phase, then the new state (`compute_state`), the transaction cell (`serialize`) and the
account after it (`commit`).

Balances are `CurrencyCollection`s: grams here, the extra currencies as the roots of their
dictionaries beside them (`TvmLean.Transaction.Extra`). The action and bounce phases are in
`TvmLean.Transaction.Action`.
-/

namespace TvmLean.Tx

/-- `StoragePhase`. -/
structure StoragePhase where
  feesCollected : Nat
  feesDue : Nat
  lastPaidUpdated : Nat
  frozen : Bool := false
  deleted : Bool := false

/-- `ComputePhase` (skip reasons `sk_no_state` 1, `sk_bad_state` 2, `sk_no_gas` 3, `sk_suspended` 4). -/
structure ComputePhase where
  skipReason : Nat := 0
  success : Bool := false
  msgStateUsed : Bool := false
  accountActivated : Bool := false
  outOfGas : Bool := false
  accepted : Bool := false
  gasFees : Nat := 0
  gasUsed : Nat := 0
  gasMax : Nat := 0
  gasLimit : Nat := 0
  gasCredit : Nat := 0
  exitCode : Int := 0
  exitArg : Int := 0
  vmSteps : Nat := 0
  newData : Option Cell := none
  actions : Option Cell := none
  precompiledGasUsage : Option Nat := none

/-- `ActionPhase`. -/
structure ActionPhase where
  success : Bool := false
  valid : Bool := false
  noFunds : Bool := false
  accStatusChange : Nat := 0
  totalFwdFees : Nat := 0
  totalActionFees : Nat := 0
  resultCode : Int := -1
  resultArg : Int := 0
  totActions : Nat := 0
  specActions : Nat := 0
  skippedActions : Nat := 0
  msgsCreated : Nat := 0
  actionListHash : BitString := natToBits 0 256
  totMsgCells : Nat := 0
  totMsgBits : Nat := 0
  stateExceedsLimits : Bool := false
  bounce : Bool := false
  actionListInvalid : Bool := false
  accDeleteReq : Bool := false
  remainingBalance : Nat := 0
  remainingExtra : Option Cell := none
  reservedBalance : Nat := 0
  reservedExtra : Option Cell := none
  endLt : Nat := 0
  actionFine : Nat := 0
  failActionFine : Nat := 0
  needBounceOnFail : Bool := false
  newCode : Option Cell := none
  outMsgs : Array Cell := #[]

/-- `BouncePhase`: `ok` (message cells and bits, fees collected, forwarding fees) or `nofunds`. -/
structure BouncePhase where
  ok : Bool
  msgCells : Nat
  msgBits : Nat
  fwdFees : Nat
  fwdFeesCollected : Nat := 0

/-- C++ `Transaction::trans_type`: an ordinary transaction on an inbound message, or a tick or tock
transaction (no message; the collator runs them for special accounts). -/
inductive TxKind where
  | ord
  | tick
  | tock
  deriving BEq, Inhabited

/-- The state of the transaction (C++ `Transaction` fields). A `CurrencyCollection` is its grams and
the root of its extra currencies (`balance` and `balanceExtra`, ...). -/
structure Tx where
  cfg : Config
  kind : TxKind := .ord
  /-- the libraries of the emulator (`set_libs`, the masterchain's public libraries): `HashmapE 256 ^Cell` -/
  globalLibs : Option Cell := none
  gv : Nat
  account : Account
  now : Nat
  startLt : Nat
  endLt : Nat
  accStatus : AccStatus
  myAddr : Cell
  myAddrExact : Cell
  balance : Nat
  balanceExtra : Option Cell := none
  originalBalance : Nat
  originalExtra : Option Cell := none
  /-- `original_balance` became invalid: below zero grams before version 9 -/
  originalInvalid : Bool := false
  msgBalanceRemaining : Nat
  /-- `msg_balance_remaining.is_valid()`: a tick-tock transaction has no inbound message and leaves it
  default-constructed (null grams, transaction.h:388) until mode 128 or 64 sets it to zero -/
  msgBalanceValid : Bool := true
  msgExtra : Option Cell := none
  duePayment : Nat
  lastPaid : Nat
  totalFees : Nat := 0
  inFwdFee : Nat := 0
  bounceEnabled : Bool := false
  inMsgExtern : Bool := false
  inMsg : Cell
  inMsgInfo : IntMsgInfo
  inMsgState : Option Cell := none
  inMsgBody : Slice
  inMsgLibrary : Option Cell := none
  newCode : Option Cell
  newData : Option Cell
  newLibrary : Option Cell
  newTick : Bool
  newTock : Bool
  newFixedPrefixLength : Nat
  useMsgState : Bool := false
  wasActivated : Bool := false
  wasFrozen : Bool := false
  wasDeleted : Bool := false
  wasCreated : Bool := false
  frozenHash : BitString
  storagePhase : Option StoragePhase := none
  creditPhase : Option Currencies := none
  computePhase : ComputePhase := {}
  actionPhase : Option ActionPhase := none
  bouncePhase : Option BouncePhase := none
  outMsgs : Array Cell := #[]

/-- What C++ produces: the transaction and the new `Account` cell (as the emulator returns them),
an external message not accepted (with the VM exit code), a failure, or a path not modelled yet. -/
inductive Outcome where
  | ok (transaction : Cell) (account : Cell)
  | externalNotAccepted (exitCode : Int)
  | failed (reason : String)
  | unsupported (what : String)

/-! ## Fees and gas (`ComputePhaseConfig`, `MsgPrices`) -/

/-- `td::rshift(x, 16, 1)`: division by 2^16 rounding up. -/
def ceilShr16 (x : Nat) : Nat := (x + 0xffff) / 0x10000

/-- `MsgPrices::compute_fwd_fees`. -/
def MsgPrices.fwdFees (p : MsgPrices) (cells bits : Nat) : Nat :=
  p.lumpPrice + ceilShr16 (p.bitPrice * bits + p.cellPrice * cells)

/-- `compute_max_gas_threshold`. -/
def GasPrices.maxGasThreshold (g : GasPrices) (gasLimit : Nat) : Nat :=
  if gasLimit > g.flatGasLimit then ceilShr16 (g.gasPrice * (gasLimit - g.flatGasLimit)) + g.flatGasPrice
  else g.flatGasPrice

/-- `ComputePhaseConfig::gas_bought_for` with the gas limit `gasLimit`. -/
def GasPrices.gasBoughtFor (g : GasPrices) (gasLimit : Nat) (nanograms : Nat) : Nat :=
  if nanograms ≥ g.maxGasThreshold gasLimit then gasLimit
  else if nanograms < g.flatGasPrice then 0
  else (nanograms - g.flatGasPrice) * 0x10000 / g.gasPrice + g.flatGasLimit

/-- `ComputePhaseConfig::compute_gas_price`. -/
def GasPrices.gasPriceOf (g : GasPrices) (gasUsed : Nat) : Nat :=
  if gasUsed ≤ g.flatGasLimit then g.flatGasPrice
  else ceilShr16 (g.gasPrice * (gasUsed - g.flatGasLimit)) + g.flatGasPrice

/-- `override_gas_limit`: accounts whose gas limit was raised (`(wc, addr)`, limit, from version,
until). -/
def gasLimitOverrides : List (Int × Nat × Nat × Nat × Nat) :=
  [(0, 0xFFBFD8F5AE5B2E1C7C3614885CB02145483DFAEE575F0DD08A72C366369211CD, 70000000, 5, 1709164800),
   (0, 0x5e4a5f9dba638789e6770c990d2959237aca3bc19d15a734782c26cb19343cc6, 70000000, 9, 1740787200),
   (0, 0xb755c43ee37925c30f547e2991e7c4c18c1ce4ec63eea5743708dbad868369fa, 70000000, 9, 1740787200),
   (0, 0x61c016fc8efa241af7eb787451a1e571236dfb3eb389832aec0212c0fb8ac10b, 70000000, 9, 1740787200),
   (0, 0xa4a11a78384f92154a0c12761f2f7bc5e374f703335f5bc8f24c2e32ce4f1c26, 70000000, 9, 1740787200),
   (0, 0x4de480ab6acefd53c158126ef5c2cdf89fe64d210d0b44da5c90e52c215dce79, 70000000, 9, 1740787200),
   (0, 0x436a76c2794a88e3fbfec6b9c0374fc8db046f10868b835420d9937973a665d4, 225000000, 9, 1740787200)]

/-- `Transaction::gas_bought_for`: with the overridden limit for the accounts above. -/
def Tx.gasBoughtFor (t : Tx) (g : GasPrices) (nanograms : Nat) : Nat :=
  let a := bitsToNat t.account.addr
  match gasLimitOverrides.find? (fun (wc, addr, _, v, u) =>
      wc == t.account.workchain && addr == a && t.gv ≥ v && t.now < u) with
  | some (_, _, limit, _, _) => g.gasBoughtFor limit nanograms
  | none => g.gasBoughtFor g.gasLimit nanograms

/-! ## Storage phase -/

/-- `StoragePrices::compute_storage_fees`. -/
def storageFees (now lastPaid : Nat) (special mc : Bool) (used : StorageUsed) (pricing : Array StoragePrices) : Nat :=
  if now ≤ lastPaid ∨ lastPaid = 0 ∨ special ∨ pricing.isEmpty ∨ now ≤ pricing[0]!.validSince then 0
  else Id.run do
    let n := pricing.size
    -- the last price valid at `last_paid` (or the first)
    let start := ((List.range n).filter (fun j => pricing[j]!.validSince ≤ lastPaid)).getLast?.getD 0
    let mut upto := Nat.max lastPaid pricing[0]!.validSince
    let mut total := 0
    for i in [start:n] do
      if upto < now then
        let validUntil := if i < n - 1 then Nat.min now pricing[i + 1]!.validSince else now
        if upto < validUntil then
          let p := pricing[i]!
          let (cp, bp) := if mc then (p.mcCellPrice, p.mcBitPrice) else (p.cellPrice, p.bitPrice)
          total := total + (used.cells * cp + used.bits * bp) * (validUntil - upto)
        upto := validUntil
    return ceilShr16 total

/-- `Transaction::prepare_storage_phase` (`force_collect` true, as the emulator calls it). -/
def Tx.storagePhaseRun (t : Tx) (pricing : Array StoragePrices) (gas : GasPrices) (adjustMsgValue : Bool) : Option Tx := do
  if t.now < t.account.lastPaid then none
  let toPay := storageFees t.now t.account.lastPaid t.account.isSpecial t.account.isMasterchain t.account.storageUsed pricing
    + t.duePayment
  let lastPaid := if t.account.isSpecial then 0 else t.now
  let t := { t with lastPaid }
  let (t, sp) :=
    if toPay = 0 then (t, ({ feesCollected := 0, feesDue := 0, lastPaidUpdated := lastPaid } : StoragePhase))
    else if toPay ≤ t.balance then
      ({ t with balance := t.balance - toPay, duePayment := if t.gv ≥ 7 then 0 else t.duePayment },
       { feesCollected := toPay, feesDue := 0, lastPaidUpdated := lastPaid })
    else
      let due := toPay - t.balance
      let sp0 : StoragePhase := { feesCollected := t.balance, feesDue := due, lastPaidUpdated := lastPaid }
      let t := { t with balance := 0 }
      if t.account.isSpecial then (t, sp0)
      else
        let (t, sp) :=
          match t.accStatus with
          | .uninit | .frozen =>
              -- an account with extra currencies is kept
              if due > gas.deleteDueLimit && t.balanceExtra.isNone then
                ({ t with accStatus := .deleted, wasDeleted := t.wasDeleted || t.gv ≥ 13 }, { sp0 with deleted := true })
              else (t, sp0)
          | .active =>
              if due > gas.freezeDueLimit then ({ t with accStatus := .frozen, wasFrozen := true }, { sp0 with frozen := true })
              else (t, sp0)
          | _ => (t, sp0)
        ({ t with duePayment := if t.gv ≥ 4 then due else t.duePayment }, sp)
  let t := if adjustMsgValue && t.msgBalanceRemaining > t.balance then { t with msgBalanceRemaining := t.balance } else t
  return { t with totalFees := t.totalFees + sp.feesCollected, storagePhase := some sp }

/-- `Transaction::prepare_credit_phase`: `.ok none` if the extra currencies do not add up (C++
fails). -/
def Tx.creditPhaseRun (t : Tx) : Except String (Option Tx) :=
  match extraAdd t.balanceExtra t.msgExtra with
  | .error _ => .error "malformed extra currencies"
  | .ok none => .ok none
  | .ok (some e) =>
      .ok (some { t with creditPhase := some { grams := t.msgBalanceRemaining, extra := t.msgExtra },
                         balance := t.balance + t.msgBalanceRemaining, balanceExtra := e })


/-! ## The inbound message (`Transaction::unpack_input_msg`) -/

/-- `StateInitWithLibs` validated: a `StateInit` whose library is a dictionary of
`simple_lib$_ public:Bool root:^Cell`. -/
def validStateInitWithLibs (c : Cell) : Bool :=
  match Reader.runExact Account.Reader.stateInit c with
  | none => false
  | some si =>
      match dictEntries si.library 256 with
      | none => false
      | some es => es.all fun (_, v) => v.bitsRemaining == 1 && v.refsRemaining == 1

/-- The extent of a `StateInit` stored inline (`t_StateInit.fetch_to`), as a cell. -/
def Reader.stateInitCell : Reader Cell := do
  let start ← Reader.peek
  let _ ← Account.Reader.stateInit
  let after ← Reader.peek
  return Cell.mkOrdinary (start.cell.bits.extract start.bitPos after.bitPos)
    (start.cell.refs.extract start.refPos after.refPos)

/-- `Transaction::unpack_input_msg` (not delivered by IHR): `none` where C++ fails (an external
message is then rejected), `some (Except.error _)` for a path not modelled. -/
def Tx.unpackInputMsg (t : Tx) (sl : SizeLimits) (fwdPrices : MsgPrices) : Option (Except String Tx) := do
  let s := Slice.ofCell t.inMsg
  if !s.haveBits 1 then none
  let (t, s) ← if !(s.readBits 1)[0]! then do
      let (info, s) ← Reader.intMsgInfo s
      -- `msg_balance_remaining.unpack(value)`, `t_Grams.as_integer(extra_flags)`: `block::tlb` amounts
      if !info.value.gramsCanonical || !info.extraFlagsCanonical then none
      let t := { t with inMsgInfo := info, bounceEnabled := info.bounce, msgExtra := info.value.extra }
      let t := if t.gv ≥ 12 then t
        else { t with msgBalanceRemaining := t.msgBalanceRemaining + info.extraFlags }
      let t := { t with msgBalanceRemaining := t.msgBalanceRemaining + info.value.grams, inFwdFee := 0 }
      let t := if info.createdLt ≥ t.startLt then { t with startLt := info.createdLt + 1, endLt := info.createdLt + 2 } else t
      pure (Except.ok t, s)
    else do
      let ((src, dest, _), s) ← Reader.extInMsgInfo s
      if t.gv ≥ 10 then
        -- disable_anycast: the destination is addr_std without anycast
        let ((pfx, _, _), rest) ← Account.Reader.addrStd (Slice.ofCell (Cell.mkOrdinary dest))
        if pfx.isSome || rest.bitsRemaining != 0 then none
      if t.inMsg.depth > sl.maxExtMsgDepth then none
      let (cells, bits, depth) := sliceStorage s
      let cells := cells - 1
      let bits := bits - s.bitsRemaining
      if bits > sl.maxMsgBits ∨ cells > sl.maxMsgCells then none
      if depth > 2 then none
      let fee := if t.account.isSpecial then 0 else fwdPrices.fwdFees cells bits
      if t.balance < fee then none
      let info : IntMsgInfo := { src, dest }
      pure (Except.ok { t with inMsgInfo := info, inMsgExtern := true, inFwdFee := fee, balance := t.balance - fee,
                               msgBalanceRemaining := 0, msgExtra := none }, s)
  match t with
  | .error e => return .error e
  | .ok t =>
  -- init:(Maybe (Either StateInit ^StateInit))
  let (state, s) ←
    if s.haveBits 2 && bitsToNat (s.readBits 2) == 2 then do
      let (c, s) ← Reader.stateInitCell (s.advanceBits 2)
      if !validStateInitWithLibs c then none
      pure (some c, s)
    else if s.haveBits 2 && bitsToNat (s.readBits 2) == 3 then do
      let s := s.advanceBits 2
      if !s.haveRefs 1 then none
      let c := s.cell.refs[s.refPos]!
      if !validStateInitWithLibs c then none
      pure (some c, { s with refPos := s.refPos + 1 })
    else do
      if !s.haveBits 1 then none
      pure (none, s.advanceBits 1)
  -- body:(Either X ^X)
  if !s.haveBits 1 then none
  let body ←
    if !(s.readBits 1)[0]! then some (s.advanceBits 1)
    else
      let s := s.advanceBits 1
      if s.bitsRemaining != 0 || s.refsRemaining != 1 then none
      let c := s.cell.refs[s.refPos]!
      if c.special then return .error "exotic message body"
      some (Slice.ofCell c)
  let t := { t with inMsgState := state, inMsgBody := body, totalFees := t.totalFees + t.inFwdFee }
  -- the blackhole address of the masterchain (parameter 5) burns the grams of the message
  if t.account.isMasterchain && (t.cfg.blackholeAddr == some t.account.addr) then
    return .ok { t with msgBalanceRemaining := 0 }
  return .ok t


/-! ## Compute phase (`Transaction::prepare_compute_phase`) -/

/-- `block::is_public_library`: a library marked public whose root has the key as hash. -/
def isPublicLibrary (key : BitString) (v : Slice) : Bool :=
  v.haveBits 1 && (v.readBits 1)[0]! && v.haveRefs 1 && bytesToBits (v.cell.refs[v.refPos]!).hashBytes == key

/-- `Transaction::check_state_limits` for the new code, data and library: `some true` within the
limits, `some false` for limits exceeded (`errorcode_limits_exceeded`: too many cells, a Merkle depth
above 2, too many public libraries in the masterchain), `none` for another error. -/
def Tx.checkStateLimits (t : Tx) (sl : SizeLimits) (maxPublicLibraries : Nat) : Option Bool := do
  let same (a b : Option Cell) : Bool :=
    match a, b with
    | some x, some y => x.hashBytes == y.hashBytes
    | none, none => true
    | _, _ => false
  if same t.account.code t.newCode && same t.account.data t.newData && same t.account.library t.newLibrary then
    return true
  let roots := [t.newCode, t.newData, t.newLibrary].filterMap id
  let m := collectCells roots
  if roots.any (fun r => ((m.get? r.hashBytes).map (·.merkleDepth)).getD 0 > 2) then return false
  let (cells, _) := cellsAndBits m
  let maxCells := if t.account.isMasterchain && t.gv ≥ 12 then sl.maxMcAccStateCells else sl.maxAccStateCells
  if cells > maxCells then return false
  if t.account.isMasterchain && !same t.account.library t.newLibrary then
    let entries ← dictEntries t.newLibrary 256
    let count := (entries.filter fun (k, v) => isPublicLibrary k v).size
    if count > maxPublicLibraries then return false
  return true

/-- The balance as a VM tuple (`CurrencyCollection::as_vm_tuple`): `[grams, extra]`. -/
def balanceTuple (grams : Nat) (extra : Option Cell) : Value :=
  .tuple #[.int (.num (Int.ofNat grams)), match extra with | some c => .cell c | none => .null]

/-- `Config::get_unpacked_config_tuple(now)`: the storage prices valid at `now`, parameters 19, 20,
21, 24, 25, 43 as slices (null if absent). -/
def Config.unpackedTuple (cfg : Config) (now : Nat) : Value :=
  let param (n : Nat) : Value := match cfg.param n with | some c => .slice (Slice.ofCell c) | none => .null
  let prices : Value :=
    match cfg.param 18 with
    | none => .null
    | some c =>
        match dictEntries (some c) 32 with
        | none => .null
        | some es =>
            -- `check_for_each` stops at the first price not yet valid
            let valid := es.toList.takeWhile (fun (k, _) => bitsToNat k ≤ now)
            match valid.getLast? with
            | some (_, v) => .slice v
            | none => .null
  .tuple #[prices, param 19, param 20, param 21, param 24, param 25, param 43]

/-- `Transaction::prepare_in_msg_params_tuple` (version 11). -/
def Tx.inMsgParams (t : Tx) : Value :=
  let info := t.inMsgInfo
  let b (x : Bool) : Value := .int (.num (if x then -1 else 0))
  let n (x : Nat) : Value := .int (.num (Int.ofNat x))
  -- no message (tick-tock): zeros, `addr_none`, nulls
  if t.kind != .ord then
    .tuple #[n 0, n 0, .slice (Slice.ofCell (Cell.mkOrdinary #[false, false])), n 0, n 0, n 0, n 0, n 0, .null, .null]
  else
  .tuple #[b info.bounce, b info.bounced, .slice (Slice.ofCell (Cell.mkOrdinary info.src)), n info.fwdFee,
           n info.createdLt, n info.createdAt, n info.value.grams, n t.msgBalanceRemaining,
           match t.msgExtra with | some c => .cell c | none => .null,
           match t.inMsgState with | some c => .cell c | none => .null]

/-- `Transaction::prepare_rand_seed`: SHA-256 of the block seed and the address (before version 8:
the 32 bits of `addr_rewrite` and the first 224 bits of the address). -/
def Tx.randSeed (t : Tx) (blockSeed : BitString) : Nat :=
  let tail := if t.gv ≥ 8 then t.account.addr else t.account.addrRewrite ++ t.account.addr.extract 0 224
  bytesToNatBE (sha256Digest (bitStringToBytesBE (blockSeed ++ tail)))

/-- `Transaction::prepare_vm_c7`: `SmartContractInfo` and the fields added by later versions. -/
def Tx.c7 (t : Tx) (blockSeed : BitString) : Value :=
  let n (x : Nat) : Value := .int (.num (Int.ofNat x))
  let base : Array Value :=
    #[n 0x076ef1ea, n 0, n 0, n t.now, n t.account.blockLt, n t.startLt, n (t.randSeed blockSeed),
      balanceTuple t.balance t.balanceExtra, .slice (Slice.ofCell t.myAddr), .cell t.cfg.root]
  let v4 : Array Value :=
    if t.gv ≥ 4 then
      #[match t.newCode with | some c => .cell c | none => .null, balanceTuple t.msgBalanceRemaining t.msgExtra,
        n ((t.storagePhase.map (·.feesCollected)).getD 0), .null]
    else #[]
  let v6 : Array Value :=
    if t.gv ≥ 6 then
      #[t.cfg.unpackedTuple t.now, n t.duePayment,
        match t.computePhase.precompiledGasUsage with | some g => n g | none => .null]
    else #[]
  let v11 : Array Value := if t.gv ≥ 11 then #[t.inMsgParams] else #[]
  .tuple (base ++ v4 ++ v6 ++ v11)

/-- `Transaction::unpack_msg_state`: the code, data, library, tick-tock and fixed prefix length of
the message's `StateInit` (`lib_only`: only its library). `false` where C++ fails. -/
def Tx.unpackMsgState (t : Tx) (sl : SizeLimits) (libOnly : Bool) : Tx × Bool :=
  match t.inMsgState.bind (Reader.runExact Account.Reader.stateInit) with
  | none => (t, false)
  | some si =>
      if libOnly then ({ t with inMsgLibrary := si.library }, true)
      else
        let fpl := si.fixedPrefixLength.getD 0
        let (tick, tock) := match si.special with | some tt => tt | none => (t.newTick, t.newTock)
        let t := { t with newFixedPrefixLength := fpl, newTick := tick, newTock := tock }
        if t.gv ≥ 15 && t.accStatus == .uninit && si.library.isSome then (t, false)
        else
          let t' := { t with newCode := si.code, newData := si.data, newLibrary := si.library }
          let sl := if t.accStatus == .uninit && t.account.isMasterchain then { sl with maxAccPublicLibraries := 0 } else sl
          match t'.checkStateLimits sl sl.maxAccPublicLibraries with
          | some true => (t', true)
          | _ => (t, false)

/-- `Transaction::check_in_msg_state_hash`: the hash of the message's `StateInit` is the address
(below the fixed prefix). -/
def Tx.checkInMsgStateHash (t : Tx) : Option Tx := do
  let st ← t.inMsgState
  let h := bytesToBits st.hashBytes
  let d := t.newFixedPrefixLength
  if h.extract d 256 != t.account.addr.extract d 256 then none
  -- disable_anycast (version 10): my_addr = my_addr_exact; before, an address with the anycast prefix
  if t.gv ≥ 10 then return { t with myAddr := t.myAddrExact }
  if d = 0 then return { t with myAddr := t.myAddrExact }
  return { t with myAddr := Account.mkAddr t.account.workchain (some (t.account.addr.extract 0 d))
                              (h.extract 0 d ++ t.account.addr.extract d 256) }

/-- `VmState::convert_code_cell`: from version 9 the code cell is loaded as a slice with the VM's
libraries and without gas (a library cell becomes the root of its library); where that fails (a
missing library, another exotic cell) the code is a cell with one reference to the code cell. Before
version 9 an ordinary cell is read as it is (`NoVmOrd`) and an exotic one gets the reference too: the
VM's implicit JMPREF then loads it, with gas. The cell whose slice the VM runs. -/
def convertCodeCell (code : Cell) (gv : Nat) (libs : Array Cell) : Cell :=
  let wrapped := Cell.mkOrdinary #[] #[code]
  if gv ≥ 9 then
    match (libraryResolveLoads libs gv code).2 with
    | .ok c => c
    | .error _ => wrapped
  else if code.special then wrapped
  else code

/-- The VM of the compute phase: `vm::VmState(code, global_version, stack, gas, flags = 1, data, ...)`
(`computePhaseInit` of the converted code, the stack of `computePhaseStack` for a message) with the
libraries of `compute_vm_libraries`, `max_data_depth`, c7 and, if the configuration sets it,
`max_transaction_library_loads` as `max_library_loads` (transaction.cpp:1995-2002). -/
def Tx.runVm (t : Tx) (code : Cell) (gasLimit gasMax gasCredit : Nat) (blockSeed : BitString)
    (sl : SizeLimits) : VmState × Int :=
  -- `prepare_vm_stack`: tick-tock gets the balance, the address, whether it is tock and -2
  let stack : Stack :=
    if t.kind != .ord then
      #[.int (.num (Int.ofNat t.balance)), .int (.num (Int.ofNat (bitsToNat t.account.addr))),
        .int (.num (if t.kind == .tock then -1 else 0)), .int (.num (-2))]
    else
      computePhaseStack (Int.ofNat t.balance) (Int.ofNat t.msgBalanceRemaining) t.inMsg t.inMsgBody t.inMsgExtern
  -- `compute_vm_libraries`: the message's and the account's libraries before version 15, then the
  -- emulator's
  let libs : Array Cell :=
    (if t.gv < 15 then #[t.inMsgLibrary, t.newLibrary].filterMap id else #[]) ++ t.globalLibs.toArray
  let st0 := computePhaseInit (convertCodeCell code t.gv libs) (t.newData.getD Cell.empty) stack #[t.c7 blockSeed]
    (Int.ofNat gasLimit) (Int.ofNat gasMax) (Int.ofNat gasCredit) t.gv
  let st : VmState :=
    { st0 with libraries := libs, maxDataDepth := sl.maxVmDataDepth, maxLibraryLoads := sl.maxTransactionLibraryLoads }
  let fuel := (st.gas.stepBound) + 16
  match VmState.run fuel st with
  | .halt ec stF => (stF, ec)
  | .continue stF => (stF, Excno.fatal.toInt)


/-- The end of the compute phase once the VM ran: an accepted message pays for its gas (a special
account pays nothing). -/
def Tx.payGas (t : Tx) (gas : GasPrices) (cp : ComputePhase) : Except String (Tx × ComputePhase) := do
  if !cp.accepted then return (t, cp)
  if t.account.isSpecial then return (t, { cp with gasFees := 0 })
  let fees := gas.gasPriceOf cp.gasUsed
  if fees > t.balance then throw "gas fees above balance"
  return ({ t with totalFees := t.totalFees + fees, balance := t.balance - fees }, { cp with gasFees := fees })

/-- `Transaction::prepare_compute_phase` (no precompiled contract has an implementation: a
precompiled code runs the VM with the gas limits of the configuration, its gas usage reported).
`Except.error` for a path not modelled, `.ok none` where C++ fails (a precompiled contract out of gas). -/
def Tx.computePhaseRun (t : Tx) (gas : GasPrices) (sl : SizeLimits) (blockSeed : BitString) :
    Except String (Option Tx) := do
  -- `original_balance`: from version 9 the balance less the message's value, before it the account's
  -- balance less the fees so far (invalid below zero)
  let t ← if t.gv ≥ 9 then
      match extraSub t.balanceExtra t.msgExtra with
      | .ok (some e) => pure { t with originalBalance := t.balance - t.msgBalanceRemaining, originalExtra := e }
      | _ => throw "original balance"
    else pure { t with originalBalance := t.originalBalance - t.totalFees,
                       originalInvalid := t.originalBalance < t.totalFees }
  let skip (t : Tx) (reason : Nat) : Except String (Option Tx) :=
    .ok (some { t with computePhase := { t.computePhase with skipReason := reason } })
  if t.balance = 0 then return ← skip t 3
  -- `compute_gas_limits`
  let gasMax := if t.account.isSpecial then gas.specialGasLimit else t.gasBoughtFor gas t.balance
  -- tick-tock may use all the gas the balance buys
  let gasLimit := if t.kind != .ord || (t.account.isSpecial && t.gv ≥ 5) then gasMax
    else Nat.min (t.gasBoughtFor gas t.msgBalanceRemaining) gasMax
  let gasCredit := if t.inMsgExtern then Nat.min gas.gasCredit gasMax else 0
  let t := { t with computePhase := { gasMax, gasLimit, gasCredit } }
  if gasLimit = 0 ∧ gasCredit = 0 then return ← skip t 3
  let stateHashOk : Bool :=
    match t.inMsgState with
    | some c => t.accStatus == .uninit || (!t.wasFrozen && t.accStatus == .frozen && t.account.stateHash == bytesToBits c.hashBytes)
    | none => false
  let mut t := t
  if stateHashOk then
    if t.accStatus == .uninit then
      if (dictGet (t.cfg.suspendedAddresses t.now) (natToBits ((t.account.workchain % (2 ^ 32 : Int)).toNat) 32 ++ t.account.addr)).isSome then
        return ← skip t 4
    t := { t with useMsgState := true }
    let (t', ok) := t.unpackMsgState sl false
    t := t'
    if !ok then return ← skip t 2
    if (t.gv < 16 || t.accStatus != .frozen) then
      -- `check_addr_rewrite_length`
      let okLen := if t.account.addrRewriteLengthSet then t.newFixedPrefixLength == t.account.addrRewriteLength
        else t.newFixedPrefixLength ≤ 30
      if !okLen then return ← skip t 2
    if t.accStatus == .uninit then
      match t.checkInMsgStateHash with
      | none => return ← skip t 2
      | some t' => t := t'
    if t.gv ≥ 10 && t.accStatus == .uninit && t.newFixedPrefixLength > sl.maxAccFixedPrefixLength then
      return ← skip t 2
  else if t.accStatus != .active then
    return ← skip t (if t.inMsgState.isSome then 2 else 1)
  else if t.inMsgState.isSome then
    if t.gv ≥ 8 && t.inMsgExtern && some t.account.addr != t.inMsgState.map (bytesToBits ·.hashBytes) then
      return ← skip t 2
    t := (t.unpackMsgState sl true).1
  if t.gv < 8 && t.inMsgExtern && t.inMsgState.isSome && some t.account.addr != t.inMsgState.map (bytesToBits ·.hashBytes) then
    return ← skip t 2
  if t.gv ≥ 10 then
    t := { t with myAddr := t.myAddrExact }
  let some code := t.newCode
    | -- no code (an active account or a `StateInit` without it): `VmState::run` returns `fatal` at
      -- once (vm.cpp:513-516, `cp.exit_code = ~vm.run()`): no step, no gas, nothing committed; the
      -- exit argument is the top of the initial stack (`in_msg_extern`, or -2 for tick-tock)
      let accepted := t.computePhase.gasCredit == 0
      let cp0 := { t.computePhase with exitCode := ~~~ Excno.fatal.toInt, vmSteps := 0, gasUsed := 0, accepted,
                                       success := false, exitArg := if t.kind != .ord then -2 else if t.inMsgExtern then -1 else 0 }
      let t0 := if accepted && t.useMsgState then { t with wasActivated := true, accStatus := .active } else t
      let (t1, cp1) ← t0.payGas gas cp0
      return some { t1 with computePhase := cp1 }
  let precompiled : Option Nat :=
    if t.kind != .ord then none else
    (dictGet t.cfg.precompiledList (bytesToBits code.hashBytes)).bind fun v =>
      match (do if (← Reader.uint 8) != 0xb0 then Reader.fail
                Reader.uint 64 : Reader Nat) v with
      | some (g, _) => some g
      | none => none
  let (gl, gm, gc) := (t.computePhase.gasLimit, t.computePhase.gasMax, t.computePhase.gasCredit)
  let (gl, gm, gc) ← match precompiled with
    | none => pure (gl, gm, gc)
    | some usage =>
        if usage > gl then return ← skip { t with computePhase := { t.computePhase with precompiledGasUsage := some usage } } 3
        let limit := if t.account.isSpecial then gas.specialGasLimit else gas.gasLimit
        pure (limit, limit, if gc ≠ 0 then limit else 0)
  t := { t with computePhase := { t.computePhase with precompiledGasUsage := precompiled } }
  let (stF, ec) := t.runVm code gl gm gc blockSeed sl
  -- the exit code, the committed c4 and c5 and the gas used (`ComputeOutcome.ofHalt`)
  let out := ComputeOutcome.ofHalt ec stF (t.newData.getD Cell.empty)
  let exitCode := out.exitCode
  let gasUsed := out.gasUsed.toNat
  let accepted := stF.gas.gasCredit == 0
  let success := accepted && stF.cstate.committed
  let cp := t.computePhase
  let mut cp := { cp with exitCode, outOfGas := exitCode == ~~~ Excno.outOfGas.toInt, vmSteps := stF.steps, gasUsed,
                          accepted, success }
  if accepted && t.useMsgState then
    t := { t with wasActivated := true, accStatus := .active }
  if let some usage := precompiled then
    -- "Precompiled smc got out_of_gas in TVM": prepare_compute_phase fails
    if cp.outOfGas then return none
    cp := { cp with gasUsed := usage, vmSteps := 0 }
  if success then
    cp := { cp with newData := some out.c4, actions := some out.c5 }
  if !success then
    match stF.stack.back? with
    | some (.int (.num v)) => if -2 ^ 31 ≤ v ∧ v < 2 ^ 31 then cp := { cp with exitArg := v }
    | _ => pure ()
  let (t', cp') ← t.payGas gas cp
  t := t'
  cp := cp'
  -- C++ never sets `msg_state_used` and `account_activated` of the compute phase (both stay false)
  return some { t with computePhase := cp }


/-! ## The new state (`Transaction::compute_state`) and the transaction (`serialize`, `commit`) -/

def W.status (w : W) (s : AccStatus) : W :=
  w.uint (match s with | .nonexist | .deleted => 3 | .uninit => 0 | .frozen => 1 | .active => 2) 2

/-- `store_UInt7` (`VarUInteger 7`). -/
def W.uint7 (w : W) (v : Nat) : W := w.varUInt v 7

/-- The storage statistics and the dict hash of the new account with the storage `storage`
(`Transaction::compute_state`, transaction.cpp:3630-3710): recomputed when the references of the storage
change, else updated by the bits of its root; from version 10 without the extra currencies
(`storage_without_extra_currencies` replaces the dictionary of the balance, its first reference, by
`hme_empty`: the same bits). `none` where the update of the bits (`new_storage_used.bits -= old;
new_storage_used.bits += new`, 3704-3705, 64-bit) wraps around below zero: at least 2^64 - 1023,
which `store_UInt7` refuses (3714-3715). -/
def Tx.storageStat (t : Tx) (sl : SizeLimits) (storage : Cell) : Option (StorageUsed × Option BitString) :=
  let withoutExtra (rs : Array Cell) (extra : Bool) : Array Cell :=
    if t.gv ≥ 10 && extra then rs.extract 1 rs.size else rs
  let oldRefs : Option (Array Cell) := t.account.storage.map fun s =>
    withoutExtra (s.cell.refs.extract s.refPos s.cell.refs.size) t.account.balance.extra.isSome
  let newRefs := withoutExtra storage.refs t.balanceExtra.isSome
  let oldBits : Nat := (t.account.storage.map (·.bitsRemaining)).getD 0
  let refsChanged : Bool :=
    match oldRefs with
    | none => true
    | some rs => rs.size != newRefs.size || (rs.zip newRefs).any fun (a, b) => a.hashBytes != b.hashBytes
  let storeDictHash := t.gv ≥ 11 && !t.account.isMasterchain
  if refsChanged || (storeDictHash && t.account.storageDictHash.isNone && t.account.storageUsed.cells > 25) then
    let m := collectCells newRefs.toList
    let (c, b) := cellsAndBits m
    let used : StorageUsed := { cells := c + 1, bits := b + storage.bits.size }
    let dh := if storeDictHash && used.cells ≥ sl.accStateCellsForStorageDict then storageDictHash m else none
    some (used, dh)
  else if t.account.storageUsed.bits + storage.bits.size < oldBits then none
  else
    some ({ t.account.storageUsed with bits := t.account.storageUsed.bits + storage.bits.size - oldBits },
      if storeDictHash then t.account.storageDictHash else none)

/-- `Transaction::compute_state` (transaction.cpp:3552-3735): the new `Account` cell, or `none` where C++
returns `false` (a store of a `FAIL_UNLESS` that does not fit; `serialize` fails and so does the
emulator, transaction-emulator.cpp:70-73): the balance and the due payment are `Grams` (below 2^120),
the storage statistics `VarUInteger 7` (below 2^48). The other stores cannot fail: `store_long_bool`
keeps the low bits of a value (the logical time, the fixed prefix length, the last paid time), and the
account has at most 1023 bits (an `addr_std` address with an anycast prefix of 30 bits and every other
field at its largest; an anycast account in workchain 127 has a longer `addr_var` address, which fails
`accountAddrValid`) and 4 references; the balance of an account written as `account_none` is zero. -/
def Tx.computeState (t : Tx) (sl : SizeLimits) : Option (Tx × Cell) := do
  let zero := t.balance = 0 && t.balanceExtra.isNone
  let t := if t.accStatus == .uninit && !t.wasActivated && zero then { t with accStatus := .nonexist, wasCreated := false } else t
  let t := if t.accStatus == .deleted && !zero then { t with accStatus := .uninit } else t
  if t.accStatus == .nonexist || t.accStatus == .deleted then return (t, (W.bool {} false).cell)
  -- `balance.store(cb)` (3572-3573): the grams are `Grams`
  if t.balance ≥ 2 ^ 120 then none
  let disableAnycast := t.gv ≥ 10
  let ticktock := (if t.newTick then 2 else 0) + (if t.newTock then 1 else 0)
  let fpl := if disableAnycast then t.newFixedPrefixLength else t.account.addrRewriteLength
  let stateInitBits (w : W) : W :=
    let w := if fpl ≠ 0 then w.uint (fpl + 32) 6 else w.uint 0 1
    let w := if ticktock ≠ 0 then w.uint (ticktock ||| 4) 3 else w.uint 0 1
    ((w.maybeRef t.newCode).maybeRef t.newData).maybeRef t.newLibrary
  let w : W := ((({} : W).uint t.endLt 64).currencies { grams := t.balance, extra := t.balanceExtra })
  let (t, w) :=
    if t.accStatus == .uninit then (t, w.uint 0 2)
    else if t.accStatus == .frozen then
      let frozenHash := if t.wasFrozen then bytesToBits (stateInitBits {}).cell.hashBytes else t.frozenHash
      let t := { t with frozenHash, newCode := none, newData := none, newLibrary := none }
      if frozenHash == t.account.addrOrig then
        ({ t with accStatus := if t.gv ≥ 13 then .uninit else t.accStatus }, w.uint 0 2)
      else (t, (w.uint 1 2).bitStr frozenHash)
    else
      -- active: account_active$1 and the StateInit
      let w := if fpl ≠ 0 then w.uint (fpl + 96) 7 else w.uint 2 2
      let w := if ticktock ≠ 0 then w.uint (ticktock ||| 4) 3 else w.uint 0 1
      (t, ((w.maybeRef t.newCode).maybeRef t.newData).maybeRef t.newLibrary)
  let storage := w.cell
  let (used, dictHash) ← t.storageStat sl storage
  -- `store_UInt7` (3714-3715): the storage statistics are `VarUInteger 7`
  if used.cells ≥ 2 ^ 48 || used.bits ≥ 2 ^ 48 then none
  -- `t_Grams.store_integer_ref(cb, due_payment)` (3720)
  if t.duePayment ≥ 2 ^ 120 then none
  let addr := if disableAnycast then t.myAddr else t.account.myAddr
  let w : W := ({} : W).bool true |>.slice (Slice.ofCell addr)
  let w := (w.uint7 used.cells).uint7 used.bits
  let w := match dictHash with
    | some h => (w.uint 1 3).bitStr h
    | none => w.uint 0 3
  let w := w.uint t.lastPaid 32
  let w := if t.duePayment ≠ 0 then (w.bool true).grams t.duePayment else w.bool false
  return (t, (w.slice (Slice.ofCell storage)).cell)

/-- `serialize_compute_phase`. -/
def W.computePhase (w : W) (cp : ComputePhase) : W :=
  match cp.skipReason with
  | 1 => w.uint 0 3
  | 2 => w.uint 1 3
  | 3 => w.uint 2 3
  | 4 => w.uint 0b0110 4
  | _ =>
      let w2 : W := ((({} : W).uint7 cp.gasUsed).uint7 cp.gasLimit)
      let w2 := if cp.gasCredit ≠ 0 then (w2.bool true).varUInt cp.gasCredit 3 else w2.bool false
      let w2 := (w2.int 0 8).int cp.exitCode 32
      let w2 := if cp.exitArg ≠ 0 then (w2.bool true).int cp.exitArg 32 else w2.bool false
      let w2 := ((w2.uint cp.vmSteps 32).uint 0 256).uint 0 256
      ((((w.bool true).bool cp.success).bool cp.msgStateUsed).bool cp.accountActivated |>.grams cp.gasFees).ref w2.cell

/-- `store_Maybe_Grams_nz`. -/
def W.maybeGramsNz (w : W) (v : Nat) : W := if v ≠ 0 then (w.bool true).grams v else w.bool false

/-- `serialize_action_phase`. -/
def W.actionPhase (w : W) (ap : ActionPhase) : W :=
  let w := ((w.bool ap.success).bool ap.valid).bool ap.noFunds
  let w := w.uint ap.accStatusChange ((ap.accStatusChange >>> 1) + 1)
  let w := (w.maybeGramsNz ap.totalFwdFees).maybeGramsNz ap.totalActionFees
  let w := w.int ap.resultCode 32
  let w := if ap.resultArg ≠ 0 then (w.bool true).int ap.resultArg 32 else w.bool false
  let w := (((w.uint ap.totActions 16).uint ap.specActions 16).uint ap.skippedActions 16).uint ap.msgsCreated 16
  ((w.bitStr ap.actionListHash).uint7 ap.totMsgCells).uint7 ap.totMsgBits

/-- `Transaction::serialize` of an ordinary transaction, after `compute_state`. -/
def Tx.serialize (t : Tx) (newState : Cell) : Option Cell := do
  -- out_msgs:(HashmapE 15 ^(Message Any))
  let outDict ← t.outMsgs.size.fold (init := some (none : Option Cell)) fun i _ acc => do
    let root ← acc
    match dictSetRefWithCells root (natToBits i 15) t.outMsgs[i]! .add with
    | .ok (r, _, _, _) => some r
    | .error _ => none
  if t.outMsgs.size ≥ 2 ^ 15 then none
  let msgs : W := ({} : W).maybeRef (if t.kind == .ord then some t.inMsg else none) |>.maybeRef outDict
  let update : W := ((({} : W).uint 0x72 8).bitStr (bytesToBits t.account.totalState.hashBytes)).bitStr
    (bytesToBits newState.hashBytes)
  let cp := t.computePhase
  let act := cp.success
  let actOk := act && (t.actionPhase.map (·.success)).getD false
  let sp ← t.storagePhase
  let storage (d : W) : W :=
    let d := (d.grams sp.feesCollected).maybeGramsNz sp.feesDue
    if sp.deleted || sp.frozen then d.uint (if sp.deleted then 3 else 2) 2 else d.uint 0 1
  -- trans_ord$0000 credit_first storage_ph:(Maybe ...) credit_ph:(Maybe ...), or
  -- trans_tick_tock$001 is_tock storage_ph:TrStoragePhase
  let d : W :=
    if t.kind != .ord then storage (({} : W).uint (if t.kind == .tick then 2 else 3) 4)
    else
      let d := storage (((({} : W).uint 0 4).bool (!t.bounceEnabled)).bool true)
      match t.creditPhase with
      | some credit => ((d.bool true).maybeGramsNz 0).currencies credit
      | none => d.bool false
  let d := d.computePhase cp
  let d ← if act then do
      let ap ← t.actionPhase
      pure ((d.bool true).ref (W.actionPhase {} ap).cell)
    else pure (d.bool false)
  let d := d.bool (!actOk)
  -- bounce:(Maybe TrBouncePhase), not in tick-tock
  let d := if t.kind != .ord then d else match t.bouncePhase with
    | none => d.bool false
    | some bp =>
        let d := d.bool true
        if bp.ok then (((d.bool true).uint7 bp.msgCells).uint7 bp.msgBits).grams bp.fwdFeesCollected |>.grams bp.fwdFees
        else ((d.uint 1 2).uint7 bp.msgCells).uint7 bp.msgBits |>.grams bp.fwdFees
  let d := d.bool t.wasDeleted
  let w : W := (((({} : W).uint 7 4).bitStr t.account.addr).uint t.startLt 64)
  let w := (w.bitStr t.account.lastTransHash).uint t.account.lastTransLt 64
  let w := (w.uint t.now 32).uint t.outMsgs.size 15
  let w := (w.status t.account.status).status t.accStatus
  let w := ((w.ref msgs.cell).currencies { grams := t.totalFees }).ref update.cell
  return (w.ref d.cell).cell


end TvmLean.Tx

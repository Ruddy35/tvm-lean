import TvmLean.Transaction.Run

/-!
# Action and bounce phases

C++ `Transaction::prepare_action_phase`, `try_action_send_msg`, `try_action_reserve_currency`,
`try_action_set_code`, `try_action_change_library`, `check_replace_src_addr`,
`check_rewrite_dest_addr` and `prepare_bounce_phase` (`crypto/block/transaction.cpp`). Extra
currencies follow `extra_currency_v2` (version 10): before it they move with the grams (mode 128 sends
all of them, mode 64 those of the inbound message, a reserve takes them); from it only what an
outbound message names is sent, without zero amounts, and a reserve of extra currencies is invalid.
-/

namespace TvmLean.Tx

/-! ## Validation of TL-B values (`validate_ref`, `validate_csr`) -/

/-- A malformed dictionary of extra currencies: C++ throws, the path is not modelled. -/
def liftDict (x : DictM α) : Except String α :=
  match x with
  | .ok a => .ok a
  | .error _ => .error "malformed extra currencies"


/-- `HashmapE 32 (VarUInteger 32)` (`ExtraCurrencyCollection`). -/
def validExtraCurrencies (root : Option Cell) : Bool :=
  match dictEntries root 32 with
  | none => false
  | some es => es.all fun (_, v) =>
      match (Reader.varUInt 32) v with
      | some (_, r) => r.bitsRemaining == 0 && r.refsRemaining == 0
      | none => false

/-- `MsgAddress`: `MsgAddressExt` or `MsgAddressInt`. -/
def Reader.msgAddress : Reader BitString := do
  let s ← Reader.peek
  if s.haveBits 1 && (s.readBits 1)[0]! then Reader.msgAddressInt else Reader.msgAddressExt

/-- `CommonMsgInfoRelaxed` of an outbound message, validated. -/
inductive RelaxedInfo where
  | int (ihrDisabled bounce bounced : Bool) (src dest : BitString) (value : Currencies) (extraFlags fwdFee : Nat)
      (extraFlagsCanonical fwdFeeCanonical : Bool)
  | ext (src dest : BitString)

def Reader.relaxedInfo : Reader RelaxedInfo := do
  if !(← Reader.bool) then
    let ihr ← Reader.bool
    let bounce ← Reader.bool
    let bounced ← Reader.bool
    let src ← Reader.msgAddress
    let dest ← Reader.msgAddressInt
    let value ← Reader.currencies
    if !validExtraCurrencies value.extra then Reader.fail
    let (extraFlags, extraFlagsCanonical) ← Reader.gramsC
    let (fwdFee, fwdFeeCanonical) ← Reader.gramsC
    let _ ← Reader.uint 64
    let _ ← Reader.uint 32
    return .int ihr bounce bounced src dest value extraFlags fwdFee extraFlagsCanonical fwdFeeCanonical
  else
    if !(← Reader.bool) then Reader.fail
    let src ← Reader.msgAddress
    let dest ← Reader.msgAddressExt
    let _ ← Reader.uint 64
    let _ ← Reader.uint 32
    return .ext src dest

/-- An outbound message as proposed: its header, the `init` field and the `body` field as the
slices they occupy (`MessageRelaxed Any`, `type_unpack_cell`: the whole cell). -/
structure RelaxedMsg where
  info : RelaxedInfo
  /-- `init:(Maybe (Either StateInit ^StateInit))` -/
  init : Slice
  /-- `body:(Either X ^X)` -/
  body : Slice
  /-- no `StateInit`, or one whose library is a dictionary of `SimpleLib`
  (`block::tlb::validate_message_relaxed_libs`, block-parse.cpp:2476-2490) -/
  initLibsValid : Bool

/-- A slice of `s` from its position to that of `t` (the part `t` was read from). -/
def _root_.TvmLean.Slice.upTo (s t : Slice) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (s.cell.bits.extract s.bitPos t.bitPos) (s.cell.refs.extract s.refPos t.refPos))

/-- `MessageRelaxed Any`, validated as the generated TL-B code does (`StateInit` with
`library:(Maybe ^Cell)`); whether the library is a valid dictionary is recorded, not required. The
`^StateInit` and the body's `^X` are read by `validate_ref`, which refuses an exotic cell
(`TLB::validate_ref_internal`, tlblib.cpp:139-147; a `^Cell` field of the `StateInit` takes any). -/
def parseRelaxedMsg (c : Cell) : Option RelaxedMsg := do
  if c.special then none
  let s := Slice.ofCell c
  let (info, s1) ← Reader.relaxedInfo s
  -- init
  let (s2, initLibsValid) ←
    if !s1.haveBits 1 then none
    else if !(s1.readBits 1)[0]! then some (s1.advanceBits 1, true)
    else if !s1.haveBits 2 then none
    else if !(s1.readBits 2)[1]! then
      let (si, r) ← Reader.stateInitCell (s1.advanceBits 2)
      some (r, validStateInitWithLibs si)
    else
      let r := s1.advanceBits 2
      if !r.haveRefs 1 then none
      let si := r.cell.refs[r.refPos]!
      if si.special || (Reader.runExact Account.Reader.stateInit si).isNone then none
      some ({ r with refPos := r.refPos + 1 }, validStateInitWithLibs si)
  -- body: left (the rest) or right (one reference, nothing else)
  if !s2.haveBits 1 then none
  if (s2.readBits 1)[0]! then
    if s2.bitsRemaining != 1 || s2.refsRemaining != 1 || s2.cell.refs[s2.refPos]!.special then none
  return { info, init := s1.upTo s2, body := s2, initLibsValid }

/-- `OutAction` of an `OutListNode` (`prev:^Cell action:OutAction`), validated as
`t_OutListNode.validate_ref`. -/
inductive OutAction where
  | sendMsg (mode : Nat) (msg : Cell)
  | setCode (code : Cell)
  | reserve (mode : Nat) (value : Currencies)
  | changeLibrary (mode : Nat) (libRef : Sum BitString Cell)

def parseOutAction (node : Cell) : Option OutAction := do
  if node.special then none
  let s := Slice.ofCell node
  if !s.haveRefs 1 then none
  let s := { s with refPos := 1 }
  let (tag, s) ← Reader.uint 32 s
  let end? (r : Slice) : Bool := r.bitsRemaining == 0 && r.refsRemaining == 0
  if tag == 0x0ec3c86d then
    let ((mode, msg), r) ← (do return (← Reader.uint 8, ← Reader.ref)) s
    if !end? r then none
    let _ ← parseRelaxedMsg msg
    return .sendMsg mode msg
  else if tag == 0xad4de08e then
    let (code, r) ← Reader.ref s
    if !end? r then none
    return .setCode code
  else if tag == 0x36e6b809 then
    let ((mode, value), r) ← (do return (← Reader.uint 8, ← Reader.currencies)) s
    if !end? r || !validExtraCurrencies value.extra then none
    return .reserve mode value
  else if tag == 0x26fa1dd4 then
    let ((mode, lib), r) ← (do
      let mode ← Reader.uint 7
      -- libref_hash$0 lib_hash:bits256 | libref_ref$1 library:^Cell
      if ← Reader.bool then return (mode, Sum.inr (← Reader.ref))
      else return (mode, Sum.inl (← Reader.bits 256))) s
    if !end? r then none
    return .changeLibrary mode lib
  else none

/-! ## Workchains (parameter 12) -/

structure WorkchainInfo where
  acceptMsgs : Bool
  minAddrLen : Nat
  maxAddrLen : Nat
  addrLenStep : Nat

/-- `WorkchainInfo::unpack` of `workchain#a6` / `workchain_v2#a7` (the fields the destination checks
use). -/
def Config.workchain (cfg : Config) (wc : Int) : Option WorkchainInfo := do
  let v ← dictGet cfg.workchains (natToBits ((wc % (2 ^ 32 : Int)).toNat) 32)
  let (info, _) ← (do
      let tag ← Reader.uint 8
      if tag != 0xa6 && tag != 0xa7 then Reader.fail
      let _ ← Reader.bits (32 + 8 + 8 + 8)
      let basic ← Reader.bool
      let _ ← Reader.bool
      let accept ← Reader.bool
      let _ ← Reader.bits (13 + 256 + 256 + 32)
      if basic then return ({ acceptMsgs := accept, minAddrLen := 256, maxAddrLen := 256, addrLenStep := 256 } : WorkchainInfo)
      else
        if (← Reader.uint 4) != 0 then Reader.fail
        let mn ← Reader.uint 12
        let mx ← Reader.uint 12
        let st ← Reader.uint 12
        return { acceptMsgs := accept, minAddrLen := mn, maxAddrLen := mx, addrLenStep := st }) v
  return info

def WorkchainInfo.validAddrLen (w : WorkchainInfo) (len : Nat) : Bool :=
  len ≥ w.minAddrLen && len ≤ w.maxAddrLen &&
    (len == w.minAddrLen || len == w.maxAddrLen || (w.addrLenStep > 0 && (len - w.minAddrLen) % w.addrLenStep == 0))

/-- `Transaction::check_rewrite_dest_addr`: `none` for an invalid destination, else the address
(rewritten for an anycast with another prefix, `addr_var` of 256 bits repacked as `addr_std`) and
whether it is in the masterchain. -/
def Tx.checkRewriteDestAddr (t : Tx) (dest : BitString) (allowAnycast : Bool) : Option (BitString × Bool) := do
  if !dest[0]! then return (dest, false)
  let ((tag, anycast, wc, len, addr), r) ← (do
      let tag ← Reader.uint 2
      let anycast ← Reader.maybe (do
        let d ← Reader.uint 5
        return (d, ← Reader.bits d))
      if tag == 2 then return (tag, anycast, ← Reader.int 8, 256, ← Reader.bits 256)
      else if tag == 3 then
        let len ← Reader.uint 9
        let wc ← Reader.int 32
        return (tag, anycast, wc, len, ← Reader.bits len)
      else Reader.fail) (Slice.ofCell (Cell.mkOrdinary dest))
  if r.bitsRemaining != 0 then none
  let mut repack := tag == 3 && len == 256 && -128 ≤ wc && wc < 128
  if wc != -1 then
    let w ← t.cfg.workchain wc
    if !w.acceptMsgs || !w.validAddrLen len then none
  else if len != 256 then none
  let mut anycast := anycast
  match anycast with
  | some (d, pfx) =>
      if !allowAnycast then none
      if d = 0 ∨ d > 30 then none
      let mine := t.account.addr.extract 0 d
      if pfx != mine then
        anycast := some (d, mine)
        repack := true
  | none => pure ()
  let mc := wc == -1
  if !repack then return (dest, mc)
  let anyBits : BitString := match anycast with
    | some (d, p) => #[true] ++ natToBits d 5 ++ p
    | none => #[false]
  if len == 256 && -128 ≤ wc && wc < 128 then
    return (#[true, false] ++ anyBits ++ (({} : W).int wc 8).bits ++ addr, mc)
  else
    return (#[true, true] ++ anyBits ++ natToBits len 9 ++ (({} : W).int wc 32).bits ++ addr, mc)

/-- `Transaction::check_replace_src_addr`: `addr_none` becomes the account's address; otherwise it
must be `addr_std` equal to it. -/
def Tx.checkReplaceSrcAddr (t : Tx) (src : BitString) : Option BitString :=
  if src.size == 2 && bitsToNat src == 0 then some t.myAddr.bits
  else if src.size < 2 || bitsToNat (src.extract 0 2) != 2 then none
  else if src == t.myAddr.bits || src == t.myAddrExact.bits then some src
  else none


/-! ## The actions -/

/-- `ERRCODE_FAIL_ACTION_PHASE`: the action phase (and the transaction) fails. -/
def errFailActionPhase : Int := -666

/-- `try_action_set_code`. -/
def Tx.actionSetCode (_t : Tx) (ap : ActionPhase) (code : Cell) : Int × ActionPhase :=
  (0, { ap with newCode := some code, specActions := ap.specActions + 1 })

/-- `try_action_change_library`. -/
def Tx.actionChangeLibrary (t : Tx) (ap : ActionPhase) (sl : SizeLimits) (mode0 : Nat) (libRef : Sum BitString Cell) :
    Int × Tx × ActionPhase := Id.run do
  let mut mode := mode0
  let mut ap := ap
  if mode &&& 16 != 0 then
    if t.gv < 4 then return (-1, t, ap)
    ap := { ap with needBounceOnFail := true }
    mode := mode - (mode &&& 16)
  if mode > 2 then return (-1, t, ap)
  if t.gv ≥ 15 then
    if mode == 1 || !t.account.isSpecial then return (46, t, ap)
  let (hash, lib0) := match libRef with
    | .inr c => (bytesToBits c.hashBytes, some c)
    | .inl h => (h, none)
  if mode == 0 then
    match dictDeleteWithCells t.newLibrary hash with
    | .error _ => return (42, t, ap)
    | .ok (_, root, _) => return (0, { t with newLibrary := root }, { ap with specActions := ap.specActions + 1 })
  let mut lib := lib0
  match dictLookup t.newLibrary hash with
  | .error _ => return (42, t, ap)
  | .ok none => pure ()
  | .ok (some v) =>
      if v.haveBits 1 && v.haveRefs 1 then
        let isPublic := (v.readBits 1)[0]!
        let r := v.cell.refs[v.refPos]!
        if bytesToBits r.hashBytes == hash then
          lib := some r
          if isPublic == (mode >>> 1 == 1) then
            return (0, t, { ap with specActions := ap.specActions + 1 })
      else return (42, t, ap)
  let some libCell := lib | return (41, t, ap)
  let (cells, _, depth) := sliceStorage (Slice.ofCell (Cell.mkOrdinary #[] #[libCell]))
  if cells - 1 > sl.maxLibraryCells || depth > 2 then return (43, t, ap)
  let val : Builder := { bits := #[mode >>> 1 == 1], refs := #[libCell] }
  match dictSetBuilderWithCells t.newLibrary hash val .set with
  | .error _ => return (42, t, ap)
  | .ok (root, _, _, _) => return (0, { t with newLibrary := root }, { ap with specActions := ap.specActions + 1 })

/-- `try_action_reserve_currency`. -/
def Tx.actionReserve (t : Tx) (ap : ActionPhase) (mode0 : Nat) (value : Currencies) : Except String (Int × ActionPhase) := do
  let mut mode := mode0
  let mut ap := ap
  if mode &&& 16 != 0 && t.gv ≥ 4 then
    mode := mode - (mode &&& 16)
    ap := { ap with needBounceOnFail := true }
  if mode >>> 4 != 0 then return (-1, ap)
  -- `reserve.validate_unpack`: `block::tlb` amounts (the generated code of the action list is laxer)
  if !value.valid then return (-1, ap)
  if t.gv ≥ 10 && value.extra.isSome then return (-1, ap)
  let mut reserve : Int := value.grams
  let mut resExtra := value.extra
  if mode &&& 4 != 0 then
    if t.gv ≥ 10 then
      reserve := if mode &&& 8 != 0 then Int.ofNat t.originalBalance - reserve else reserve + t.originalBalance
    else
      -- `original_balance - reserve` or `reserve + original_balance` as `CurrencyCollection`s
      if t.originalInvalid then return (-1, ap)
      if mode &&& 8 != 0 then
        reserve := Int.ofNat t.originalBalance - reserve
        if reserve < 0 then return (-1, ap)
        let some e ← liftDict (extraSub t.originalExtra resExtra) | return (-1, ap)
        resExtra := e
      else
        reserve := reserve + t.originalBalance
        let some e ← liftDict (extraAdd resExtra t.originalExtra) | return (-1, ap)
        resExtra := e
  else if mode &&& 8 != 0 then return (-1, ap)
  if reserve < 0 then return (-1, ap)
  let mut r := reserve.toNat
  if mode &&& 2 != 0 then
    r := Nat.min r ap.remainingBalance
    -- `clamp` (reserve_extra_enabled, version 9)
    if t.gv ≥ 9 then
      let some e ← liftDict (extraClamp resExtra ap.remainingExtra) | return (-1, ap)
      resExtra := e
  if r > ap.remainingBalance then return (37, ap)
  let some newExtra ← liftDict (extraSub ap.remainingExtra resExtra) | return (38, ap)
  let mut newc := ap.remainingBalance - r
  let mut newExtra := newExtra
  if mode &&& 1 != 0 then
    let x := newc
    newc := r
    r := x
    if t.gv < 10 then
      let e := newExtra
      newExtra := resExtra
      resExtra := e
  let some reserved ← liftDict (extraAdd ap.reservedExtra resExtra) | return (errFailActionPhase, ap)
  return (0, { ap with remainingBalance := newc, remainingExtra := newExtra, reservedBalance := ap.reservedBalance + r,
                       reservedExtra := reserved, specActions := ap.specActions + 1 })

/-- The distinct cells and bits referenced by `slices` (their roots not counted) and the largest
Merkle depth, counted at most up to `maxCells` cells (`CellStorageStat` with `limit_cells`: the
count stops past the limit). -/
def refsStorage (slices : List Slice) (maxCells : Nat) : Nat × Nat × Nat :=
  let refs := slices.flatMap fun s => (s.cell.refs.extract s.refPos s.cell.refs.size).toList
  let m := collectCells refs
  let (c, b) := cellsAndBits m
  let depth := refs.foldl (fun d r => Nat.max d (((m.get? r.hashBytes).map (·.merkleDepth)).getD 0)) 0
  (if c > maxCells then maxCells + 1 else c, b, depth)

/-- `try_action_send_msg` (`redoing`: 1 moves the `StateInit` into a reference, 2 also the body).
Returns the code: 0, -1 (invalid), -2 (to redo), `errFailActionPhase` or a result code. -/
def Tx.actionSendMsg (t : Tx) (ap : ActionPhase) (sl : SizeLimits) (mode0 : Nat) (msgCell : Cell) (redoing0 : Nat) :
    Except String (Int × Tx × ActionPhase) := do
  let mut mode := mode0
  let mut ap := ap
  let mut redoing := redoing0
  if mode &&& 16 != 0 && t.gv ≥ 4 then
    mode := mode - (mode &&& 16)
    ap := { ap with needBounceOnFail := true }
  let skipInvalid := mode &&& 2 != 0
  let skip (ap : ActionPhase) (code : Int) : Int × Tx × ActionPhase :=
    if skipInvalid then (0, t, if t.gv ≥ 8 then { ap with skippedActions := ap.skippedActions + 1 } else ap)
    else (code, t, ap)
  if mode &&& 0x1c != 0 || mode &&& 0xc0 == 0xc0 then
    return if t.gv ≥ 13 then skip ap (-1) else (-1, t, ap)
  let some msg := parseRelaxedMsg msgCell | return (-1, t, ap)
  -- `validate_message_relaxed_libs` (transaction.cpp:2704-2707): the action list passed validation
  -- with any library cell in the `StateInit`; here it must be a dictionary of `SimpleLib`
  if !msg.initLibsValid then return if t.gv ≥ 13 then skip ap (-1) else (-1, t, ap)
  -- `redoing`: the StateInit into a reference (if it is inline with its references), then the body
  let mut init := msg.init
  let mut body := msg.body
  if redoing ≥ 1 then
    if init.refsRemaining ≥ 2 then
      let inner := init.advanceBits 2
      init := Slice.ofCell (Cell.mkOrdinary #[true, true] #[inner.toCellRemaining])
    else redoing := 2
  if redoing ≥ 2 && (body.bitsRemaining + body.refsRemaining > 1) && !(body.readBits 1)[0]! then
    body := Slice.ofCell (Cell.mkOrdinary #[true] #[(body.advanceBits 1).toCellRemaining])
  let (ext, ihrDisabled0, bounce, src0, dest0, value, extraFlags, fwdFee0, efOk, ffOk) :=
    match msg.info with
    | .int ihr b _ src dest v ef ff efOk ffOk => (false, ihr, b, src, dest, v, ef, ff, efOk, ffOk)
    | .ext src dest => (true, true, false, src, dest, ({ grams := 0 } : Currencies), 0, 0, true, true)
  if ext && mode >>> 2 != 0 then return (-1, t, ap)
  -- `t_CurrencyCollection.validate_csr(info.value)`: `block::tlb` amounts, positive extra currencies
  if !ext && !value.valid then return (-1, t, ap)
  let mut fwdFee : Nat := 0
  let mut ihrFee : Nat := 0
  let mut ihrDisabled := ihrDisabled0
  if !ext then
    if t.gv < 8 then
      -- `t_Grams.as_integer` of `block::tlb` (transaction.cpp:2769-2773): a forwarding or IHR fee
      -- with a leading zero byte is no amount, the action is invalid
      if !ffOk || !efOk then return (-1, t, ap)
      fwdFee := fwdFee0
      ihrFee := if t.gv ≥ 12 then 0 else extraFlags
    if t.gv ≥ 11 then ihrDisabled := true
    -- `extra_flags` (2778-2783): a leading zero byte makes it null, as bits outside 0 and 1 do
    if t.gv ≥ 12 && (!efOk || extraFlags &&& 3 != extraFlags) then
      return skip ap 45
  let some src := t.checkReplaceSrcAddr src0
    | return if t.gv ≥ 13 then skip ap 35 else (35, t, ap)
  let some (dest, toMc) := t.checkRewriteDestAddr dest0 (t.gv < 10)
    | return skip ap 36
  -- the extra currencies before version 10 count in the size of the message
  let valueRoot : List Slice :=
    match value.extra with
    | some d => if !ext && t.gv < 10 then [Slice.ofCell (Cell.mkOrdinary #[] #[d])] else []
    | none => []
  -- extra_currency_v2: zero amounts removed, at most `max_msg_extra_currencies`
  let mut value := value
  if !ext && t.gv ≥ 10 then
    match ← liftDict (extraRemoveZero value.extra sl.maxMsgExtraCurrencies) with
    | none => return skip ap 44
    | some e => value := { value with extra := e }
  let some prices := t.cfg.msgPrices (toMc || t.account.isMasterchain) | throw "msg prices"
  -- the fine for the cells of a message that fails (version 4)
  let mut maxCells := sl.maxMsgCells
  let mut finePerCell := 0
  if t.gv ≥ 4 && !t.account.isSpecial then
    finePerCell := (prices.cellPrice >>> 16) / 4
    let mut funds : Int := ap.remainingBalance
    if !ext && mode &&& 0x80 == 0 && mode &&& 1 == 0 then
      let mut newFunds : Int := value.grams
      if mode &&& 0x40 != 0 then
        newFunds := newFunds + t.msgBalanceRemaining - t.computePhase.gasFees - ap.actionFine
        if newFunds < 0 then return skip ap 37
      funds := min funds newFunds
    if funds < maxCells * finePerCell then
      maxCells := (funds / finePerCell).toNat
  let (cells, bits, depth) := refsStorage ([init, body] ++ valueRoot) maxCells
  let fine := if t.gv ≥ 4 && !t.account.isSpecial then finePerCell * Nat.min maxCells cells else 0
  let collectFine (ap : ActionPhase) : ActionPhase :=
    let f := Nat.min fine ap.remainingBalance
    { ap with actionFine := ap.actionFine + f, remainingBalance := ap.remainingBalance - f }
  if cells > maxCells && maxCells < sl.maxMsgCells then return skip (collectFine ap) 40
  if bits > sl.maxMsgBits || cells > maxCells then return skip (collectFine ap) 40
  if depth > 2 then return skip (collectFine ap) 40
  -- `compute_fwd_ihr_fees` (transaction.cpp:2469-2476): `td::uint64`s, the IHR fee the low 64 bits of
  -- `fwd * ihr_factor >> 16`
  let fwdC := if t.account.isSpecial then 0 else prices.fwdFees cells bits
  let ihrC := if t.account.isSpecial || ihrDisabled then 0
    else prices.fwdFees cells bits * prices.ihrPriceFactor / 0x10000 % 2 ^ 64
  -- a fee of the message is raised to the computed one if it is below 2^63 and below the computed one
  -- taken as `long long` (2911-2916): a computed fee of 2^63 or more is never charged
  if fwdFee < 2 ^ 63 && (fwdFee : Int) < int64OfUInt64 fwdC then fwdFee := fwdC
  if ihrC ≠ 0 && ihrFee < 2 ^ 63 && (ihrFee : Int) < int64OfUInt64 ihrC then ihrFee := ihrC
  let lt := ap.endLt
  let mut t := t
  let mut feesCollected := 0
  let mut feesTotal := 0
  let newMsg : Cell ← if !ext then do
      if ihrDisabled then ihrFee := 0
      let mut req : Int := value.grams
      let mut reqExtra := value.extra
      if mode &&& 0x80 != 0 then
        req := ap.remainingBalance
        if t.gv < 10 then reqExtra := ap.remainingExtra
        mode := mode - (mode &&& 1)
      else if mode &&& 0x40 != 0 then
        -- no inbound message (tick-tock): before version 10 `req += msg_balance_remaining` invalidates
        -- the value, which then fails (transaction.cpp:2953-2965); from version 10 (2951), and with
        -- mode 1 (2974), C++ dereferences the null grams and aborts
        if !t.msgBalanceValid then
          if t.gv ≥ 10 || mode &&& 1 != 0 then throw "mode 64 without an inbound message: C++ aborts"
          return skip (collectFine ap) 37
        req := req + t.msgBalanceRemaining
        -- before version 10 `req += msg_balance_remaining` adds the extra currencies too (an invalid sum
        -- fails below like a negative one)
        let mut reqValid := true
        if t.gv < 10 then
          match ← liftDict (extraAdd reqExtra t.msgExtra) with
          | some e => reqExtra := e
          | none => reqValid := false
        if mode &&& 1 == 0 then
          req := req - ap.actionFine - t.computePhase.gasFees
          if req < 0 || !reqValid then return skip (collectFine ap) 37
        else if !reqValid then throw "invalid message value"
      let mut brutto := req
      let total := fwdFee + ihrFee
      if mode &&& 1 != 0 then brutto := brutto + total
      else if req < total then return skip (collectFine ap) 37
      else req := req - total
      if ap.remainingBalance < brutto then return skip (collectFine ap) 37
      if t.gv ≥ 10 && !(← liftDict (extraWithin reqExtra sl.maxMsgExtraCurrencies)) then return skip ap 44
      let some newExtra ← liftDict (extraSub ap.remainingExtra reqExtra) | return skip (collectFine ap) 38
      let fwdMine := fwdFee * prices.firstFrac / 0x10000
      let fwdRemain := fwdFee - fwdMine
      let w : W := (((({} : W).bool false).bool ihrDisabled).bool bounce).bool false
      let w := ((w.bitStr src).bitStr dest).currencies { grams := req.toNat, extra := reqExtra }
      let w := (w.grams (if t.gv ≥ 12 then extraFlags else ihrFee)).grams fwdRemain
      let w := (w.uint lt 64).uint t.now 32
      -- `FAIL_UNLESS_ERRCODE(tlb::csr_pack(msg.info, info), ERRCODE_FAIL_ACTION_PHASE)`
      -- (transaction.cpp:3026): a header that alone does not fit a cell fails the action phase
      if w.bits.size > 1023 then return (errFailActionPhase, t, ap)
      let w := (w.slice init).slice body
      if w.bits.size > 1023 || w.refs.size > 4 then
        return if redoing == 2 then skip (collectFine ap) 39 else (-2, t, ap)
      let newBits := w.bits.size
      if t.gv ≥ 15 then
        if ap.totMsgBits + bits + newBits > sl.maxTotalMsgBits || ap.totMsgCells + cells + 1 > sl.maxTotalMsgCells then
          return skip (collectFine ap) 47
      if mode &&& 0xc0 != 0 then
        t := { t with msgBalanceRemaining := 0, msgExtra := if t.gv ≥ 10 then t.msgExtra else none, msgBalanceValid := true }
      ap := { ap with remainingBalance := ap.remainingBalance - brutto.toNat, remainingExtra := newExtra,
                      totMsgBits := ap.totMsgBits + bits + newBits }
      feesTotal := fwdFee + ihrFee
      feesCollected := fwdMine
      pure w.cell
    else do
      if ap.remainingBalance < fwdFee then return skip (collectFine ap) 37
      let w : W := (((({} : W).uint 3 2).bitStr src).bitStr dest).uint lt 64 |>.uint t.now 32
      let w := (w.slice init).slice body
      if w.bits.size > 1023 || w.refs.size > 4 then
        return if redoing == 2 then skip (collectFine ap) 39 else (-2, t, ap)
      let newBits := w.bits.size
      if t.gv ≥ 15 then
        if ap.totMsgBits + bits + newBits > sl.maxTotalMsgBits || ap.totMsgCells + cells + 1 > sl.maxTotalMsgCells then
          return skip (collectFine ap) 47
      ap := { ap with remainingBalance := ap.remainingBalance - fwdFee, totMsgBits := ap.totMsgBits + bits + newBits }
      feesTotal := fwdFee
      feesCollected := fwdFee
      pure w.cell
  ap := { ap with msgsCreated := ap.msgsCreated + 1, endLt := ap.endLt + 1, outMsgs := ap.outMsgs.push newMsg,
                  totalActionFees := ap.totalActionFees + feesCollected, totalFwdFees := ap.totalFwdFees + feesTotal,
                  totMsgCells := ap.totMsgCells + cells + 1 }
  if mode &&& 0xa0 == 0xa0 then
    -- before version 10 the extra currencies must be gone too
    let v1 := t.gv < 10
    if ap.remainingBalance != 0 || (v1 && ap.remainingExtra.isSome) then return (errFailActionPhase, t, ap)
    ap := { ap with accDeleteReq := ap.reservedBalance == 0 && (!v1 || ap.reservedExtra.isNone) }
  if t.gv ≥ 15 then ap := { ap with failActionFine := ap.failActionFine + fine }
  return (0, t, ap)


/-! ## The action phase -/

/-- `Transaction::prepare_action_phase`. `Except.error` for a path not modelled; `.ok none` where it
returns false (the transaction fails). -/
def Tx.actionPhaseRun (t : Tx) (sl : SizeLimits) : Except String (Option Tx) := do
  let some list0 := t.computePhase.actions | return none
  let mut ap : ActionPhase :=
    { actionListHash := bytesToBits list0.hashBytes, remainingBalance := t.balance, remainingExtra := t.balanceExtra,
      endLt := t.endLt }
  let (msgBalanceBefore, msgExtraBefore, msgValidBefore) := (t.msgBalanceRemaining, t.msgExtra, t.msgBalanceValid)
  let (oldCode, oldData, oldLibrary) := (t.newCode, t.newData, t.newLibrary)
  -- the list, from the last action
  let mut nodes : Array Cell := #[]
  let mut list := list0
  let mut n : Nat := 0
  let mut done := false
  for _ in [0:257] do
    if !done then
      nodes := nodes.push list
      if list.special then
        return some { t with actionPhase := some { ap with resultCode := 32, resultArg := Int.ofNat n, actionListInvalid := true } }
      if list.bits.size == 0 && list.refs.size == 0 then done := true
      else if list.refs.size == 0 then
        return some { t with actionPhase := some { ap with resultCode := 32, resultArg := Int.ofNat n, actionListInvalid := true } }
      else
        list := list.refs[0]!
        n := n + 1
        if n > 255 then
          return some { t with actionPhase := some { ap with resultCode := 33, resultArg := Int.ofNat n, actionListInvalid := true } }
  ap := { ap with totActions := n }
  -- validation of every action (from the first)
  let mut actions : Array (Option OutAction) := Array.replicate n none
  for k in [0:n] do
    let i := n - 1 - k
    ap := { ap with resultArg := Int.ofNat k }
    match parseOutAction nodes[i]! with
    | some a => actions := actions.set! i (some a)
    | none =>
        let node := nodes[i]!
        let mut skipped := false
        if t.gv ≥ 8 && !node.special then
          let s := Slice.ofCell node
          if s.bitsRemaining ≥ 40 && bitsToNat (s.readBits 32) == 0x0ec3c86d then
            let mode := bitsToNat ((s.advanceBits 32).readBits 8)
            if mode &&& 2 != 0 then
              ap := { ap with skippedActions := ap.skippedActions + 1 }
              skipped := true
            else if mode &&& 16 != 0 && t.gv ≥ 4 then
              ap := { ap with bounce := true }
        if !skipped then
          return some { t with actionPhase := some { ap with resultCode := 34, actionListInvalid := true } }
  ap := { ap with valid := true }
  let mut t := t
  -- `enforce_state_limits`: some true within the limits, some false exceeded, none on another error
  let enforce (t : Tx) : Option Bool :=
    if t.account.isSpecial then some true else t.checkStateLimits sl sl.maxAccPublicLibraries
  for k in [0:n] do
    let i := n - 1 - k
    match actions[i]! with
    | none => pure ()
    | some a =>
        ap := { ap with resultArg := Int.ofNat k, needBounceOnFail := false }
        let (code, t', ap') ←
          match a with
          | .setCode c => let (r, ap') := t.actionSetCode ap c; pure (r, t, ap')
          | .changeLibrary mode lib => pure (t.actionChangeLibrary ap sl mode lib)
          | .reserve mode value => do let (r, ap') ← t.actionReserve ap mode value; pure (r, t, ap')
          | .sendMsg mode msg => do
              let (r, t', ap') ← t.actionSendMsg ap sl mode msg 0
              if r != -2 then pure (r, t', ap') else
              let (r, t', ap') ← t.actionSendMsg ap sl mode msg 1
              if r != -2 then pure (r, t', ap') else t.actionSendMsg ap sl mode msg 2
        t := t'
        ap := ap'
        if code == errFailActionPhase then return none
        if code != 0 then
          ap := { ap with resultCode := if code == -1 then 34 else code, endLt := t.endLt,
                          actionListInvalid := ap.actionListInvalid || code == -1 || code == 34,
                          noFunds := ap.noFunds || code == 37 || code == 38 }
          -- library changes stay even if the phase fails
          match enforce t with
          | none => return none
          | some false =>
              t := { t with newCode := oldCode, newData := oldData, newLibrary := oldLibrary }
              ap := { ap with resultCode := 50, stateExceedsLimits := true }
          | some true => pure ()
          if t.gv ≥ 14 then
            t := { t with msgBalanceRemaining := msgBalanceBefore, msgExtra := msgExtraBefore, msgBalanceValid := msgValidBefore }
          if t.gv ≥ 4 then
            let fine := Nat.min (ap.actionFine + ap.failActionFine) t.balance
            ap := { ap with actionFine := fine, totalActionFees := fine }
            t := { t with balance := t.balance - fine, totalFees := t.totalFees + fine }
          if ap.needBounceOnFail then ap := { ap with bounce := true }
          return some { t with actionPhase := some ap }
  if t.gv ≥ 4 then ap := { ap with totalActionFees := ap.totalActionFees + ap.actionFine }
  t := { t with endLt := ap.endLt }
  if let some c := ap.newCode then t := { t with newCode := some c }
  t := { t with newData := t.computePhase.newData }
  match enforce t with
  | none => return none
  | some false =>
      t := { t with newCode := oldCode, newData := oldData, newLibrary := oldLibrary }
      ap := { ap with resultCode := 50, stateExceedsLimits := true }
      if t.gv ≥ 14 then
        t := { t with msgBalanceRemaining := msgBalanceBefore, msgExtra := msgExtraBefore, msgBalanceValid := msgValidBefore }
      if t.gv ≥ 10 then
        t := { t with endLt := t.startLt + 1 }
        ap := { ap with endLt := t.startLt + 1 }
        if t.gv ≥ 4 then
          let fine := Nat.min (ap.actionFine + ap.failActionFine) t.balance
          ap := { ap with actionFine := fine, totalActionFees := fine }
          t := { t with balance := t.balance - fine, totalFees := t.totalFees + fine }
      return some { t with actionPhase := some ap }
  | some true => pure ()
  let some remainingExtra ← liftDict (extraAdd ap.remainingExtra ap.reservedExtra) | return none
  ap := { ap with resultArg := 0, resultCode := 0, remainingBalance := ap.remainingBalance + ap.reservedBalance,
                  remainingExtra }
  if ap.accDeleteReq then
    if ap.remainingBalance != 0 || (t.gv < 10 && ap.remainingExtra.isSome) then return none
    ap := { ap with accStatusChange := 3 }
    t := { t with accStatus := if ap.remainingExtra.isNone then .deleted else .uninit, wasDeleted := true }
  return some { t with actionPhase := some { ap with success := true }, outMsgs := ap.outMsgs,
                       totalFees := t.totalFees + ap.totalActionFees, balance := ap.remainingBalance,
                       balanceExtra := ap.remainingExtra }


/-! ## The bounce phase -/

/-- `Transaction::prepare_bounce_phase`: the body of the bounced message in the new format (from
version 12, `extra_flags` bit 0: the original body, with its references if bit 1, the original value
and times, the phase and exit code, gas and steps) or the old one (the first `bounce_msg_body` bits
of the body under `capBounceMsgBody`). `none` where it returns false (an
invalid destination: the transaction fails). -/
def Tx.bouncePhaseRun (t : Tx) : Except String (Option Tx) := do
  let info := t.inMsgInfo
  -- the original body (in a reference or inline)
  let bodyBits : BitString := t.inMsgBody.readBits t.inMsgBody.bitsRemaining
  let bounceBody := if t.cfg.hasCapability 4 then 256 else 0
  let newFormat := t.gv ≥ 12 && info.extraFlags &&& 1 != 0
  let body : W :=
    if newFormat then
      -- new_bounce_body#fffffffe original_body:^Cell original_info:^NewBounceOriginalInfo
      -- bounced_by_phase:uint8 exit_code:int32 compute_phase:(Maybe NewBounceComputePhaseInfo)
      let orig : Cell := if info.extraFlags &&& 2 != 0 then t.inMsgBody.toCellRemaining else Cell.mkOrdinary bodyBits
      let origInfo : Cell := ((({} : W).currencies info.value).uint info.createdLt 64).uint info.createdAt 32 |>.cell
      let w : W := ((({} : W).uint 0xfffffffe 32).ref orig).ref origInfo
      let cp := t.computePhase
      let (phase, code) : Nat × Int :=
        if cp.skipReason != 0 then (0, -(Int.ofNat cp.skipReason))
        else if !cp.success then (1, cp.exitCode)
        else (2, (t.actionPhase.map (·.resultCode)).getD 0)
      let w := (w.uint phase 8).int code 32
      if cp.skipReason != 0 then w.bool false else ((w.bool true).uint cp.gasUsed 32).uint cp.vmSteps 32
    else if bounceBody > 0 then (({} : W).int (-1) 32).bitStr (bodyBits.extract 0 (Nat.min bodyBits.size bounceBody))
    else {}
  let some (dest, toMc) := t.checkRewriteDestAddr info.src true | return none
  let some prices := t.cfg.msgPrices (toMc || t.account.isMasterchain) | throw "msg prices"
  -- before version 13 the extra currencies of the inbound message count in the size
  let valueRoot : List Slice :=
    match info.value.extra with
    | some d => if t.gv < 13 then [Slice.ofCell (Cell.mkOrdinary #[] #[d])] else []
    | none => []
  let (cells, bits, _) := refsStorage (valueRoot ++ [Slice.ofCell body.cell]) 1000000000
  let fwd := prices.fwdFees cells bits
  let fine := (t.actionPhase.map (·.actionFine)).getD 0
  let msgBalance : Int := Int.ofNat t.msgBalanceRemaining - t.computePhase.gasFees - fine
  -- no funds (3459-3460): a balance below zero, or one of 64 signed bits below the fee as `long long`
  if msgBalance < 0 || (msgBalance < 2 ^ 63 && msgBalance < int64OfUInt64 fwd) then
    return some { t with bouncePhase := some { ok := false, msgCells := cells, msgBits := bits, fwdFees := fwd } }
  -- the message's value `msg_balance - fwd_fees` and its `fwd_fee` (the fee less the part collected,
  -- `t_Grams.store_long` of a `long long`) must store (3478-3484, `FAIL_UNLESS`): else the bounce
  -- phase fails, and so does the transaction
  if msgBalance < fwd || fwd - fwd * prices.firstFrac / 0x10000 ≥ 2 ^ 63 then return none
  let some balanceExtra ← liftDict (extraSub t.balanceExtra t.msgExtra) | return none
  let t : Tx := { t with balance := t.balance - msgBalance.toNat, balanceExtra }
  let value := msgBalance.toNat - fwd
  let collected := fwd * prices.firstFrac / 0x10000
  let fwdRemain := fwd - collected
  let t : Tx := { t with totalFees := t.totalFees + collected }
  let lt := t.startLt + 1 + t.outMsgs.size
  let t : Tx := { t with endLt := t.endLt + 1 }
  let w : W := (({} : W).uint 5 4).bitStr info.dest |>.bitStr dest
  -- `in_msg_extra_flags` is read from version 12 (before, the field was the IHR fee)
  let w := (w.currencies { grams := value, extra := t.msgExtra }).grams (if t.gv ≥ 12 then t.inMsgInfo.extraFlags &&& 3 else 0) |>.grams fwdRemain
  let w := ((w.uint lt 64).uint t.now 32).bool false
  let w := if w.bits.size + 1 + body.bits.size ≤ 1023 && w.refs.size + body.refs.size ≤ 4 then
      -- `append_builder`: the bits and the references of the body
      { (w.bool false).bitStr body.bits with refs := w.refs ++ body.refs }
    else (w.bool true).ref body.cell
  let msg := w.cell
  return some { t with outMsgs := t.outMsgs.push msg,
                       bouncePhase := some { ok := true, msgCells := cells, msgBits := bits, fwdFees := fwdRemain,
                                             fwdFeesCollected := collected } }

end TvmLean.Tx

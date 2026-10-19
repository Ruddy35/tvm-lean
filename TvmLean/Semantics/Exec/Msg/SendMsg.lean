import TvmLean.Semantics.Exec.Common

namespace TvmLean

/-- C++ `VmStorageStat::add_storage` (boc.cpp) on the cells of `todo` (a stack: the last one is
visited first): depth-first, references in order, each distinct cell (by hash) loaded and counted
once, stopping at the first new cell beyond `maxCells`. Terminates by the lexicographic measure
`(maxCells - cells, todo.size)`: a newly seen cell increases `cells`, a seen one shrinks `todo`. -/
def VM.countMsgCells (maxCells : Nat) (todo : Array Cell) (seen : Array (Array UInt8))
    (cells bits : Nat) : VM (Array (Array UInt8) × Nat × Nat) := do
  if h : todo.size > 0 ∧ cells < maxCells then
    let c := todo[todo.size - 1]!
    let todo' := todo.pop
    let hsh := Cell.hashBytes c
    if !(seen.any (fun x => x == hsh)) then
      VM.registerCellLoad c
      VM.countMsgCells maxCells (todo' ++ c.refs.reverse) (seen.push hsh) (cells + 1) (bits + c.bits.size)
    else
      VM.countMsgCells maxCells todo' seen cells bits
  else
    return (seen, cells, bits)
termination_by (maxCells - cells, todo.size)
decreasing_by
  all_goals
    obtain ⟨h1, h2⟩ := h
    first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; simp [Array.size_pop]; omega)
      | (simp_wf; apply Prod.Lex.left; omega)
      | (simp_wf; apply Prod.Lex.right; simp [Array.size_pop]; omega)

/-- `max_msg_cells` of C++ `Config::do_get_size_limits_config` (mc-config.cpp) on a slice: a
`size_limits_config` v1, v2 or v3 record that fills the slice exactly (`tlb::csr_unpack`), else
`none` (the configuration is invalid). -/
def sizeLimitsMaxMsgCells? (cs : Slice) : Option Nat :=
  let b := cs.readBits cs.bitsRemaining
  -- v1 fields after the tag: 160 bits; v2 adds 200 bits and `max_transaction_library_loads:(Maybe
  -- uint32)`; v3 adds 64 bits after that
  let v2Len : Nat := if b.size > 368 && b[368]! then 401 else 369
  let len? : Option Nat :=
    match bitsToNat (b.extract 0 8) with
    | 1 => some 168
    | 2 => some v2Len
    | 3 => some (v2Len + 64)
    | _ => none
  match len? with
  | some len =>
      if b.size == len && cs.refsRemaining == 0 then some (bitsToNat (b.extract 40 72)) else none
  | none => none

set_option maxHeartbeats 1000000 in
def execInstrMsgSendMsg (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .sendMsg =>
      -- Matches C++ `exec_send_message` (tonops.cpp) for modern TVM (global_version >= 12).
      -- Stack: ... msg_cell mode -- ... total_fees
      --
      -- Notes:
      -- - We parse MessageRelaxed enough to compute forwarding fees and to detect when init/body must be treated
      --   as references to satisfy root-cell limits (1023 bits / 4 refs).
      -- - We do not attempt to validate all TL-B invariants beyond what is needed here.
      VM.checkUnderflow 2
      let modeNat ← VM.popNatUpTo 2047
      let send : Bool := (modeNat &&& 1024) = 0
      let mode : Nat := modeNat &&& 0x3ff -- clear the "no-send" flag (bit 10)
      if mode ≥ 256 then
        throw .rangeChk
      let msgCell ← VM.popCell
      -- Mirrors the TL-B unpack attempt which loads the root cell once (even if the message is invalid).
      VM.registerCellLoad msgCell

      let getParam (idx : Nat) : VM Value := do
        let st ← get
        if 0 < st.regs.c7.size then
          match st.regs.c7[0]! with
          | .tuple params =>
              if idx < params.size then
                return params[idx]!
              else
                throw .rangeChk
          | _ => throw .typeChk
        else
          throw .rangeChk

      let parseAddrWorkchain (cs0 : Slice) : VM Int := do
        -- C++ `parse_addr_workchain` (tonops.cpp) reads without validating: a field cut short
        -- is not consumed (`fetch_ulong` / `fetch_long` return their eof values, `skip_first`
        -- fails); only a first bit other than 1 is an error (range_chk).
        let b : BitString := cs0.readBits cs0.bitsRemaining
        let fetch (pos n : Nat) : Option Nat × Nat :=
          if pos + n ≤ b.size then (some (bitsToNat (b.extract pos (pos + n))), pos + n) else (none, pos)
        let (b0, p1) := fetch 0 1
        if b0 != some 1 then
          throw .rangeChk
        -- `fetch_ulong(1)` at the end is eof (not 0): addr_var
        let (isVarBit, p2) := fetch p1 1
        let isVar : Bool := isVarBit != some 0
        let (anycastBit, p3) := fetch p2 1
        -- anycast: `fetch_uint_leq(30, depth)` consumes the 5 bits even if depth > 30, and the
        -- prefix is skipped only when it is there
        let p4 : Nat :=
          if anycastBit == some 1 then
            match fetch p3 5 with
            | (some depth, p) => if depth ≤ 30 ∧ p + depth ≤ b.size then p + depth else p
            | (none, p) => p
          else
            p3
        -- `(int)fetch_long(n)`: the eof value (-2^63) truncates to 0
        if isVar then
          let p5 : Nat := if p4 + 9 ≤ b.size then p4 + 9 else p4
          match (fetch p5 32).1 with
          | some w => pure (natToIntSignedTwos w 32)
          | none => pure 0
        else
          match (fetch p4 8).1 with
          | some w => pure (natToIntSignedTwos w 8)
          | none => pure 0

      let parsedMsg : SendMsgParsed ←
        match (show Except Excno SendMsgParsed from do
          let s0 : Slice := Slice.ofCell msgCell
          let (b0, s1) ← s0.takeBitsAsNatCellUnd 1
          if b0 = 0 then
            -- Internal message (CommonMsgInfoRelaxed.int_msg_info).
            let (_, s2) ← s1.takeBitsAsNatCellUnd 1 -- ihr_disabled (ignored for gv>=11)
            let (_, s3) ← s2.takeBitsAsNatCellUnd 1 -- bounce
            let (_, s4) ← s3.takeBitsAsNatCellUnd 1 -- bounced
            -- src:MsgAddress dest:MsgAddressInt, as the generated block.tlb unpacker
            -- (t_MessageRelaxed_Any) validates them: anycasts and addr_var are valid
            let afterSrc ← s4.skipMsgAddressTlb
            let destStart := afterSrc
            let destStop ← destStart.skipMsgAddressIntTlb
            let destCell := Slice.prefixCell destStart destStop
            let dest := Slice.ofCell destCell

            -- value:CurrencyCollection = grams:Grams other:ExtraCurrencyCollection(HashmapE)
            let (grams, afterGrams) ← destStop.takeGramsCellUnd
            let (hmTag, afterHmTag) ← afterGrams.takeBitsAsNatCellUnd 1
            let haveExtraCurrencies : Bool := hmTag = 1
            let afterExtra ←
              if hmTag = 0 then
                pure afterHmTag
              else if afterHmTag.haveRefs 1 then
                pure { afterHmTag with refPos := afterHmTag.refPos + 1 }
              else
                throw .cellUnd

            -- extra_flags:(VarUInteger 16) (gv>=12)
            let flagsStart := afterExtra
            let (flagsLenBytes, flags1) ← flagsStart.takeBitsAsNatCellUnd 4
            let flagsBits : Nat := flagsLenBytes * 8
            if !flags1.haveBits flagsBits then
              throw .cellUnd
            let afterFlags := flags1.advanceBits flagsBits
            let extraFlagsLen : Nat := 4 + flagsBits

            -- fwd_fee:Grams
            let (userFwdFee, afterFee) ← afterFlags.takeGramsCellUnd
            let (_, afterLt) ← afterFee.takeBitsAsNatCellUnd 64 -- created_lt
            let (_, afterAt) ← afterLt.takeBitsAsNatCellUnd 32 -- created_at

            -- init:(Maybe (Either StateInit ^StateInit))
            let initStart := afterAt
            let (hasInitNat, afterHasInit) ← initStart.takeBitsAsNatCellUnd 1
            let haveInit : Bool := hasInitNat = 1
            let (initRef, initStop) ←
              if hasInitNat = 0 then
                pure (false, afterHasInit)
              else
                let (isRefNat, afterEither) ← afterHasInit.takeBitsAsNatCellUnd 1
                if isRefNat = 1 then
                  if afterEither.haveRefs 1 then
                    pure (true, { afterEither with refPos := afterEither.refPos + 1 })
                  else
                    throw .cellUnd
                else
                  let stStop ← afterEither.skipStateInitCellUnd
                  pure (false, stStop)
            let initCell := Slice.prefixCell initStart initStop
            let initBits := initCell.bits.size
            let initInlineBits : Nat := if haveInit && !initRef then initBits - 2 else 0
            let initRefs := initCell.refs.size

            -- body:(Either X ^X)
            let bodyStart := initStop
            let (bodyRefNat, afterBodyTag) ← bodyStart.takeBitsAsNatCellUnd 1
            let (bodyRef, bodyStop) ←
              if bodyRefNat = 1 then
                -- `Either X ^X` in a reference ends the message: `type_unpack_cell` requires the
                -- slice to be empty after it (`empty_ext`)
                if afterBodyTag.haveRefs 1 && afterBodyTag.bitsRemaining == 0 &&
                    afterBodyTag.refsRemaining == 1 then
                  pure (true, { afterBodyTag with refPos := afterBodyTag.refPos + 1 })
                else
                  throw .cellUnd
              else
                pure (false, { afterBodyTag with bitPos := afterBodyTag.cell.bits.size, refPos := afterBodyTag.cell.refs.size })
            let bodyCell := Slice.prefixCell bodyStart bodyStop
            let bodyBits := bodyCell.bits.size
            let bodyInlineBits : Nat := if !bodyRef then bodyBits - 1 else 0
            let bodyRefs := bodyCell.refs.size

            return {
              extMsg := false
              dest
              value := grams
              userFwdFee
              extraFlagsLen
              haveExtraCurrencies
              haveInit
              initRef
              initInlineBits
              initRefs
              bodyRef
              bodyInlineBits
              bodyRefs
            }
          else
            -- External message: only ext_out_msg_info$11 is accepted by SENDMSG.
            let (b1, s2) ← s1.takeBitsAsNatCellUnd 1
            if b1 != 1 then
              throw .unknown
            -- src:MsgAddress dest:MsgAddressExt
            let afterSrc ← s2.skipMsgAddressTlb
            let destStart := afterSrc
            let destStop ← destStart.skipMsgAddressExtTlb
            let destCell := Slice.prefixCell destStart destStop
            let dest := Slice.ofCell destCell
            let (_, afterLt) ← destStop.takeBitsAsNatCellUnd 64 -- created_lt
            let (_, afterAt) ← afterLt.takeBitsAsNatCellUnd 32 -- created_at

            -- init/body
            let initStart := afterAt
            let (hasInitNat, afterHasInit) ← initStart.takeBitsAsNatCellUnd 1
            let haveInit : Bool := hasInitNat = 1
            let (initRef, initStop) ←
              if hasInitNat = 0 then
                pure (false, afterHasInit)
              else
                let (isRefNat, afterEither) ← afterHasInit.takeBitsAsNatCellUnd 1
                if isRefNat = 1 then
                  if afterEither.haveRefs 1 then
                    pure (true, { afterEither with refPos := afterEither.refPos + 1 })
                  else
                    throw .cellUnd
                else
                  let stStop ← afterEither.skipStateInitCellUnd
                  pure (false, stStop)
            let initCell := Slice.prefixCell initStart initStop
            let initBits := initCell.bits.size
            let initInlineBits : Nat := if haveInit && !initRef then initBits - 2 else 0
            let initRefs := initCell.refs.size

            let bodyStart := initStop
            let (bodyRefNat, afterBodyTag) ← bodyStart.takeBitsAsNatCellUnd 1
            let (bodyRef, bodyStop) ←
              if bodyRefNat = 1 then
                -- `Either X ^X` in a reference ends the message: `type_unpack_cell` requires the
                -- slice to be empty after it (`empty_ext`)
                if afterBodyTag.haveRefs 1 && afterBodyTag.bitsRemaining == 0 &&
                    afterBodyTag.refsRemaining == 1 then
                  pure (true, { afterBodyTag with refPos := afterBodyTag.refPos + 1 })
                else
                  throw .cellUnd
              else
                pure (false, { afterBodyTag with bitPos := afterBodyTag.cell.bits.size, refPos := afterBodyTag.cell.refs.size })
            let bodyCell := Slice.prefixCell bodyStart bodyStop
            let bodyBits := bodyCell.bits.size
            let bodyInlineBits : Nat := if !bodyRef then bodyBits - 1 else 0
            let bodyRefs := bodyCell.refs.size

            return {
              extMsg := true
              dest
              value := 0
              userFwdFee := 0
              extraFlagsLen := 0
              haveExtraCurrencies := false
              haveInit
              initRef
              initInlineBits
              initRefs
              bodyRef
              bodyInlineBits
              bodyRefs
            }
          ) with
        | .ok v => pure v
        | .error _ => throw .unknown

      let myAddr : Slice ←
        match (← getParam 8) with
        | .slice s => pure s
        | _ => throw .typeChk

      let myWc ← parseAddrWorkchain myAddr
      let destWc ←
        if parsedMsg.extMsg then
          pure (0 : Int)
        else
          parseAddrWorkchain parsedMsg.dest
      let isMasterchain : Bool := (myWc == -1) || (!parsedMsg.extMsg && destWc == -1)

      -- C++ order: the prices (unpacked config 4 or 5: tuple_index, not a slice -> unknown, not
      -- parsed -> cell_und), the size limits (6: not a slice -> defaults, not parsed -> cell_und),
      -- then the root cell is loaded again and the cells below it counted (VmStorageStat).
      let unpacked ← VM.getUnpackedConfigTuple
      let pricesIdx : Nat := if isMasterchain then 4 else 5
      let (lumpPrice, bitPrice, cellPrice, _ihrFactor, firstFrac) ←
        match unpacked[pricesIdx]? with
        | none => throw .rangeChk
        | some (Value.slice cs) =>
            match parseMsgPrices cs with
            | .ok p => pure p
            | .error e => throw e
        | some _ => throw .unknown
      let maxCells : Nat ←
        match unpacked[6]? with
        | none => throw .rangeChk
        | some (Value.slice cs) =>
            match sizeLimitsMaxMsgCells? cs with
            | some n => pure n
            | none => throw .cellUnd
        | some _ => pure (1 <<< 13)

      VM.registerCellLoad msgCell

      -- storage stat: the cells below the root (not its bits), without the extra-currency
      -- dictionary (global version >= 10), depth-first from the first reference
      let refStart : Nat := if parsedMsg.haveExtraCurrencies then 1 else 0
      let todo0 : Array Cell := (msgCell.refs.extract refStart msgCell.refs.size).reverse
      let (_seen, cells, bits) ← VM.countMsgCells maxCells todo0 #[] 0 0

      let valueAdjusted : Int ←
        if parsedMsg.extMsg then
          pure (0 : Int)
        else if (mode &&& 128) = 128 then
          match (← getParam 7) with
          | .tuple bal =>
              if 0 < bal.size then
                match bal[0]! with
                | .int (.num n) => pure n
                | .int .nan => throw .rangeChk
                | _ => throw .typeChk
              else
                throw .typeChk
          | _ => throw .typeChk
        else if (mode &&& 64) = 64 then
          match (← getParam 11) with
          | .tuple inc =>
              if 0 < inc.size then
                match inc[0]! with
                | .int (.num n) => pure (parsedMsg.value + n)
                | .int .nan => throw .rangeChk
                | _ => throw .typeChk
              else
                throw .typeChk
          | _ => throw .typeChk
        else
          pure parsedMsg.value

      let storedGramsLenBits (x : Int) : VM Nat := do
        if x < 0 then
          throw .rangeChk
        let u : Nat := x.toNat
        let bl : Nat := natLenBits u
        let bytes : Nat := (bl + 7) / 8
        return 4 + bytes * 8

      let mut cellsI : Nat := cells
      let mut bitsI : Nat := bits
      let feeX0 : Int := bitPrice * Int.ofNat bitsI + cellPrice * Int.ofNat cellsI
      let fwdFeeShort0 : Int := lumpPrice + ceilDivPow2 feeX0 16
      -- TVM 14: the user-provided fwd_fee is ignored (as in the action phase).
      let mut fwdFee : Int := (if (← get).globalVersion ≥ 14 then fwdFeeShort0 else max fwdFeeShort0 parsedMsg.userFwdFee)
      let mut ihrFee : Int := 0 -- global_version >= 11 disables IHR

      let msgRootBits (initRef : Bool) (bodyRef : Bool) : VM Nat := do
        if parsedMsg.extMsg then
          let mySz : Nat := myAddr.bitsRemaining
          let destSz : Nat := parsedMsg.dest.bitsRemaining
          let mut total : Nat := 2 + mySz + destSz + 32 + 64
          total := total + 1 -- init: Maybe ...
          if parsedMsg.haveInit then
            total := total + 1 + (if initRef then 0 else parsedMsg.initInlineBits)
          total := total + 1 -- body: Either ...
          total := total + (if bodyRef then 0 else parsedMsg.bodyInlineBits)
          return total
        else
          let mySz : Nat := myAddr.bitsRemaining
          let destSz : Nat := parsedMsg.dest.bitsRemaining
          let mut total : Nat := 4 + mySz + destSz
          total := total + (← storedGramsLenBits valueAdjusted)
          total := total + 1 + 32 + 64
          let fwdFeeFirst : Int := (fwdFee * Int.ofNat firstFrac) / intPow2 16
          total := total + (← storedGramsLenBits (fwdFee - fwdFeeFirst))
          total := total + parsedMsg.extraFlagsLen
          total := total + 1
          if parsedMsg.haveInit then
            total := total + 1 + (if initRef then 0 else parsedMsg.initInlineBits)
          total := total + 1
          total := total + (if bodyRef then 0 else parsedMsg.bodyInlineBits)
          return total

      let msgRootRefs (initRef : Bool) (bodyRef : Bool) : Nat :=
        (if parsedMsg.extMsg then 0 else (if parsedMsg.haveExtraCurrencies then 1 else 0)) +
          (if parsedMsg.haveInit then (if initRef then 1 else parsedMsg.initRefs) else 0) +
            (if bodyRef then 1 else parsedMsg.bodyRefs)

      let mut initRef := parsedMsg.initRef
      let mut bodyRef := parsedMsg.bodyRef

      if parsedMsg.haveInit && !initRef then
        let rb ← msgRootBits initRef bodyRef
        let rr := msgRootRefs initRef bodyRef
        if rb > 1023 || rr > 4 then
          initRef := true
          cellsI := cellsI + 1
          bitsI := bitsI + parsedMsg.initInlineBits
          let feeX1 : Int := bitPrice * Int.ofNat bitsI + cellPrice * Int.ofNat cellsI
          let fwdFeeShort1 : Int := lumpPrice + ceilDivPow2 feeX1 16
          fwdFee := (if (← get).globalVersion ≥ 14 then fwdFeeShort1 else max fwdFeeShort1 parsedMsg.userFwdFee)
          ihrFee := 0

      if !bodyRef then
        let rb ← msgRootBits initRef bodyRef
        let rr := msgRootRefs initRef bodyRef
        if rb > 1023 || rr > 4 then
          bodyRef := true
          cellsI := cellsI + 1
          bitsI := bitsI + parsedMsg.bodyInlineBits
          let feeX2 : Int := bitPrice * Int.ofNat bitsI + cellPrice * Int.ofNat cellsI
          let fwdFeeShort2 : Int := lumpPrice + ceilDivPow2 feeX2 16
          fwdFee := (if (← get).globalVersion ≥ 14 then fwdFeeShort2 else max fwdFeeShort2 parsedMsg.userFwdFee)
          ihrFee := 0

      VM.pushIntQuiet (.num (fwdFee + ihrFee)) false

      if send then
        modify fun st => st.consumeGas cellCreateGasPrice
        let st ← get
        let prev := st.regs.c5
        let actionBits := natToBits 0x0ec3c86d 32 ++ natToBits mode 8
        let newHead : Cell := Cell.mkOrdinary actionBits #[prev, msgCell]
        set { st with regs := { st.regs with c5 := newHead } }
      else
        pure ()
  | _ => next

end TvmLean

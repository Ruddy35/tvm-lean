import TvmLean.Proofs.WF.JoinPoints

/-!
# The Msg family keeps states well-formed

`execInstrMsg_WF`: every handler of `execInstrMsg` (`TvmLean/Semantics/Exec/Msg/`) keeps
`VmState.WF`, so the family does. Each handler installs an output action (C++
`install_output_action`): a new cell in `c5` whose references are the previous `c5` and, for
`SENDRAWMSG`, `SENDMSG`, `SETCODE` and `SETLIBCODE`, the cell taken from the stack, and whose bits
are a tag, a mode and the fields of the action. It is well-formed by `Cell.mkOrdinary_WF`: at most
two references, and bits within the 1023 a cell holds (the model checks the length of the
`RAWRESERVE` and `RAWRESERVEX` actions, `bits.size > 1023` is cell_ov; the others have at most
296 bits).

* The six handlers other than `SENDMSG`: `mvcgen` and `wf_cont`.
* `SENDMSG` (`execInstrMsgSendMsg_WF`): only gas, counters and the stack change before the action,
  but the handler has ten join points in a row and local functions; it is proved a join point at a
  time (`JoinPoints.lean`), by hand where `mvcgen` builds an ill-typed proof (its address parser,
  the matches with a catch-all pattern). `VM.countMsgCells_keeps` (the storage stat of the message,
  by functional induction; its hashes are never computed) and `VM.loadCellSlice_keepsWF` (a load of
  any cell keeps the state well-formed) are its steps.

`natToBits` and `Cell.mkOrdinary` are irreducible here: otherwise the unifier evaluates the bits of
the actions (`natToBits 0x36e6b809 32`, ...) when `mvcgen` compares states, a minute per handler.
-/

open Std.Do

set_option mvcgen.warning false

-- the matches of `SENDMSG` need more than the default
set_option maxHeartbeats 4000000

namespace TvmLean

attribute [local irreducible] natToBits Cell.mkOrdinary

/-! ## The handlers other than `SENDMSG` -/

theorem execInstrMsgSendRawMsg_WF : FamilyWF execInstrMsgSendRawMsg := by
  intro i next hi hnext
  mvcgen [execInstrMsgSendRawMsg, hnext]
  all_goals wf_cont [Cell.mkOrdinary_WF, natToBits_size]

theorem execInstrMsgRawReserve_WF : FamilyWF execInstrMsgRawReserve := by
  intro i next hi hnext
  mvcgen [execInstrMsgRawReserve, hnext]
  all_goals wf_cont [Cell.mkOrdinary_WF, natToBits_size]

theorem execInstrMsgRawReserveX_WF : FamilyWF execInstrMsgRawReserveX := by
  intro i next hi hnext
  mvcgen [execInstrMsgRawReserveX, hnext]
  all_goals wf_cont [Cell.mkOrdinary_WF, natToBits_size]

theorem execInstrMsgSetCode_WF : FamilyWF execInstrMsgSetCode := by
  intro i next hi hnext
  mvcgen [execInstrMsgSetCode, hnext]
  all_goals wf_cont [Cell.mkOrdinary_WF, natToBits_size]

theorem execInstrMsgSetLibCode_WF : FamilyWF execInstrMsgSetLibCode := by
  intro i next hi hnext
  mvcgen [execInstrMsgSetLibCode, hnext]
  all_goals wf_cont [Cell.mkOrdinary_WF, natToBits_size]

theorem execInstrMsgChangeLib_WF : FamilyWF execInstrMsgChangeLib := by
  intro i next hi hnext
  mvcgen [execInstrMsgChangeLib, hnext]
  all_goals wf_cont [Cell.mkOrdinary_WF, natToBits_size]

/-! ## `SENDMSG` -/

/-- C++ `VmStorageStat::add_storage` on the cells of a message: only gas and counters change. -/
theorem VM.countMsgCells_keeps (maxCells : Nat) (todo : Array Cell) (seen : Array (Array UInt8))
    (cells bits : Nat) : (VM.countMsgCells maxCells todo seen cells bits).Keeps fun _ => True := by
  induction todo, seen, cells, bits using VM.countMsgCells.induct maxCells with
  | case1 todo seen cells bits h c todo' hsh hnew ih =>
    rw [VM.countMsgCells, dif_pos h]
    dsimp only at hnew ih ⊢
    rw [if_pos hnew]
    exact VM.Keeps.bind (VM.Keeps.ofWF (VM.registerCellLoadSpecial_spec _)) fun _ _ => ih
  | case2 todo seen cells bits h c todo' hsh hnew ih =>
    rw [VM.countMsgCells, dif_pos h]
    dsimp only at hnew ih ⊢
    rw [if_neg hnew]
    exact ih
  | case3 todo seen cells bits h =>
    rw [VM.countMsgCells, dif_neg h]
    exact VM.Keeps.pure' trivial

/-- `VM.loadCellSlice_spec` as a step. -/
theorem VM.loadCellSlice_keeps {c : Cell} (h : c.WF) : (VM.loadCellSlice c).Keeps Slice.WF :=
  VM.spec_mono (VM.loadCellSlice_spec c) (fun _ hs => ⟨hs, h⟩) (fun _ _ h => h) (fun _ _ h => h)

/-- `VM.loadCellSlice` of any cell keeps states well-formed (the slice is not claimed
well-formed). -/
theorem VM.loadCellSlice_keepsWF (c : Cell) : (VM.loadCellSlice c).Keeps fun _ => True := by
  unfold VM.loadCellSlice
  mvcgen
  all_goals wf_vc

/-- C++ `exec_send_message`: the message is parsed, its fees computed from the prices, the size
limits and the cells below its root, the fees pushed and the action installed, a join point at a
time (`JoinPoints.lean`). -/
theorem execInstrMsgSendMsg_WF : FamilyWF execInstrMsgSendMsg := by
  intro i next hi hnext
  unfold execInstrMsgSendMsg
  split
  · refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec 2)) fun _ _ => ?_
    refine VM.Keeps.bind (VM.popNatUpTo_spec 2047) fun modeNat _ => ?_
    extract_lets -underBinder +onlyGivenNames send mode jpA
    have hjpA : ∀ y, VM.KeepsWFIf True (jpA y) := ?jpA
    · clear_value jpA
      split <;> keeps_leaf hjpA
    clear hnext
    -- the message and its parse
    intro y
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpA
    refine VM.Keeps.bind VM.popCell_spec fun msgCell hmsg => ?_
    refine VM.Keeps.bind (VM.loadCellSlice_keeps hmsg) fun _ _ => ?_
    extract_lets -underBinder +onlyGivenNames msgRoot getParam parseAddrWorkchain jpB
    have hgp : ∀ idx, (getParam idx).Keeps Value.WF := by
      intro idx
      unfold getParam
      mvcgen
      all_goals wf_cont
    -- by hand: `mvcgen` builds an ill-typed proof on its matches of pairs (Lean 4.24)
    have hpaw : ∀ cs, (parseAddrWorkchain cs).Keeps fun _ => True := by
      intro cs
      unfold parseAddrWorkchain
      extract_lets -underBinder +onlyGivenNames b fetch
      split
      extract_lets -underBinder +onlyGivenNames jp
      split
      · exact VM.Keeps.bind (Q := fun _ => False) (VM.Keeps.throw' _) fun _ h => h.elim
      · refine VM.Keeps.bind (Q := fun _ => True) (VM.Keeps.pure' trivial) fun _ _ => ?_
        unfold jp
        split
        extract_lets -underBinder +onlyGivenNames isVar
        split
        extract_lets -underBinder +onlyGivenNames p4
        split
        · extract_lets -underBinder +onlyGivenNames p5
          split <;> exact VM.Keeps.pure' trivial
        · split <;> exact VM.Keeps.pure' trivial
    have hjpB : ∀ p, VM.KeepsWFIf True (jpB p) := ?jpB
    · clear_value jpB
      split <;> keeps_leaf hjpB
    -- its addresses
    intro parsedMsg
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpB
    refine VM.Keeps.bind (hgp 8) fun _ _ => ?_
    extract_lets -underBinder +onlyGivenNames jpC
    have hjpC : ∀ myAddr, VM.KeepsWFIf True (jpC myAddr) := ?jpC
    · clear_value jpC
      split <;> keeps_leaf hjpC
    intro myAddr
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpC
    refine VM.Keeps.bind (hpaw myAddr) fun myWc _ => ?_
    extract_lets -underBinder +onlyGivenNames jpD
    have hjpD : ∀ destWc, VM.KeepsWFIf True (jpD destWc) := ?jpD
    · clear_value jpD
      split
      · keeps_leaf hjpD
      · exact VM.Keeps.bind (hpaw _) fun _ _ => (hjpD _).keeps trivial
    -- the prices
    intro destWc
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpD
    extract_lets -underBinder +onlyGivenNames isMasterchain
    refine VM.Keeps.bind VM.Keeps.get' fun _ hs => ?_
    clear hs
    extract_lets -underBinder +onlyGivenNames gv jpE
    have hjpE : ∀ pricesCs, VM.KeepsWFIf True (jpE pricesCs) := ?jpE
    · clear_value jpE
      split
      · -- from version 6, in the unpacked configuration
        refine VM.Keeps.bind VM.getUnpackedConfigTuple_spec fun _ _ => ?_
        extract_lets -underBinder +onlyGivenNames pricesIdx
        split <;> keeps_leaf hjpE
      · -- before, in the configuration dictionary
        refine VM.Keeps.bind (hgp 9) fun _ _ => ?_
        extract_lets -underBinder +onlyGivenNames configRoot keyBits
        refine VM.Keeps.bind VM.cellResolver_spec fun _ _ => ?_
        extract_lets -underBinder +onlyGivenNames jpE'
        have hjpE' : ∀ p, VM.KeepsWFIf True (jpE' p) := ?jpE'
        · clear_value jpE'
          have hloads : ∀ cells : Array Cell, (forIn cells PUnit.unit fun c _ => do
              VM.registerCellLoad c
              pure (ForInStep.yield PUnit.unit)).Keeps fun _ => True := by
            intro cells
            refine VM.Keeps.forIn_array (fun _ => True) cells trivial fun c _ _ => ?_
            mvcgen
            all_goals wf_cont
          split
          · refine VM.Keeps.bind VM.cellResolver_spec fun _ _ => ?_
            refine VM.Keeps.bind (hloads _) fun _ _ => ?_
            keeps_leaf hjpE'
          · refine VM.Keeps.bind (hloads _) fun _ _ => ?_
            keeps_leaf hjpE'
          · refine VM.Keeps.bind (hloads _) fun _ _ => ?_
            split <;> keeps_leaf hjpE'
        intro p
        apply VM.KeepsWFIf.of_keeps
        intro _
        unfold jpE'
        split
        · exact VM.Keeps.bind (VM.loadCellSlice_keepsWF _) fun _ _ => (hjpE _).keeps trivial
        · keeps_leaf hjpE
    intro pricesCs
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpE
    extract_lets -underBinder +onlyGivenNames jpF
    have hjpF : ∀ p, VM.KeepsWFIf True (jpF p) := ?jpF
    · clear_value jpF
      split <;> keeps_leaf hjpF
    -- the size limits and the cells of the message
    intro p
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpF
    split
    extract_lets -underBinder +onlyGivenNames jpG
    have hjpG : ∀ maxCells, VM.KeepsWFIf True (jpG maxCells) := ?jpG
    · clear_value jpG
      split
      · refine VM.Keeps.bind VM.getUnpackedConfigTuple_spec fun _ _ => ?_
        split
        · keeps_leaf hjpG
        · split <;> keeps_leaf hjpG
        · keeps_leaf hjpG
      · keeps_leaf hjpG
    intro maxCells
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpG
    refine VM.Keeps.bind (VM.loadCellSlice_keeps hmsg) fun _ _ => ?_
    extract_lets -underBinder +onlyGivenNames msgRoot' refStart todo0
    refine VM.Keeps.bind (VM.countMsgCells_keeps _ _ _ _ _) fun _ _ => ?_
    split
    extract_lets -underBinder +onlyGivenNames extraOf jpH
    have hextraOf : ∀ t, (extraOf t).Keeps fun _ => True := by
      intro t
      unfold extraOf
      extract_lets -underBinder +onlyGivenNames jp
      split
      · exact VM.Keeps.pure' trivial
      · refine VM.Keeps.bind (Q := fun _ => True) (VM.Keeps.pure' trivial) fun _ _ => ?_
        unfold jp
        split <;> first | exact VM.Keeps.throw' _ | exact VM.Keeps.pure' trivial
    have hjpH : ∀ ve, VM.KeepsWFIf True (jpH ve) := ?jpH
    · clear_value jpH
      split
      · keeps_leaf hjpH
      · split
        · refine VM.Keeps.bind (hgp 7) fun _ _ => ?_
          split
          · split
            · split
              · exact VM.Keeps.bind (hextraOf _) fun _ _ =>
                  VM.Keeps.bind (Q := fun _ => True) (VM.Keeps.pure' trivial) fun _ _ =>
                    (hjpH _).keeps trivial
              · keeps_leaf hjpH
              · keeps_leaf hjpH
            · keeps_leaf hjpH
          · keeps_leaf hjpH
        · split
          · refine VM.Keeps.bind (hgp 11) fun _ _ => ?_
            split
            · split
              · split
                · exact VM.Keeps.bind (hextraOf _) fun _ _ =>
                    VM.Keeps.bind (Q := fun _ => True) (VM.Keeps.pure' trivial) fun _ _ =>
                      (hjpH _).keeps trivial
                · keeps_leaf hjpH
                · keeps_leaf hjpH
              · keeps_leaf hjpH
            · keeps_leaf hjpH
          · keeps_leaf hjpH
    -- the fees and the root of the message
    intro ve
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpH
    split
    extract_lets -underBinder +onlyGivenNames storedGramsLenBits ihrDisabled computeFees cellsI
      bitsI
    have hsgl : ∀ x, (storedGramsLenBits x).Keeps fun _ => True := by
      intro x
      unfold storedGramsLenBits
      extract_lets -underBinder +onlyGivenNames jp
      split
      · exact VM.Keeps.bind (Q := fun _ => False) (VM.Keeps.throw' _) fun _ h => h.elim
      · refine VM.Keeps.bind (Q := fun _ => True) (VM.Keeps.pure' trivial) fun _ _ => ?_
        unfold jp
        exact VM.Keeps.pure' trivial
    split
    extract_lets -underBinder +onlyGivenNames fwdFee ihrFee msgRootBits msgRootRefs initRef bodyRef
      jpI
    have hmrb : ∀ a b c d, (msgRootBits a b c d).Keeps fun _ => True := by
      intro a b c d
      unfold msgRootBits
      split
      · extract_lets -underBinder +onlyGivenNames mySz destSz total total' jp
        split
        · extract_lets -underBinder +onlyGivenNames total''
          refine VM.Keeps.bind (Q := fun _ => True) (VM.Keeps.pure' trivial) fun _ _ => ?_
          unfold jp
          exact VM.Keeps.pure' trivial
        · refine VM.Keeps.bind (Q := fun _ => True) (VM.Keeps.pure' trivial) fun _ _ => ?_
          unfold jp
          exact VM.Keeps.pure' trivial
      · extract_lets -underBinder +onlyGivenNames mySz destSz total
        refine VM.Keeps.bind (hsgl _) fun _ _ => ?_
        extract_lets -underBinder +onlyGivenNames total' total'' fwdFeeFirst
        refine VM.Keeps.bind (hsgl _) fun _ _ => ?_
        extract_lets -underBinder +onlyGivenNames total3
        refine VM.Keeps.bind (Q := fun _ => True) ?_ fun _ _ => ?_
        · split
          · exact VM.Keeps.pure' trivial
          · exact hsgl _
        extract_lets -underBinder +onlyGivenNames total4 total5 jp
        split
        · extract_lets -underBinder +onlyGivenNames total6
          refine VM.Keeps.bind (Q := fun _ => True) (VM.Keeps.pure' trivial) fun _ _ => ?_
          unfold jp
          exact VM.Keeps.pure' trivial
        · refine VM.Keeps.bind (Q := fun _ => True) (VM.Keeps.pure' trivial) fun _ _ => ?_
          unfold jp
          exact VM.Keeps.pure' trivial
    have hjpI : ∀ a b c d e f y, VM.KeepsWFIf True (jpI a b c d e f y) := ?jpI
    · clear_value jpI
      split
      · refine VM.Keeps.bind (hmrb _ _ _ _) fun _ _ => ?_
        extract_lets -underBinder +onlyGivenNames rr
        split
        · extract_lets -underBinder +onlyGivenNames initRef' cellsI' bitsI'
          split
          extract_lets -underBinder +onlyGivenNames fwdFee' ihrFee'
          keeps_leaf (hjpI _ _ _ _ _ _)
        · keeps_leaf (hjpI _ _ _ _ _ _)
      · keeps_leaf (hjpI _ _ _ _ _ _)
    intro a b c d e f y
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpI
    extract_lets -underBinder +onlyGivenNames jpJ
    have hjpJ : ∀ a b c d e y, VM.KeepsWFIf True (jpJ a b c d e y) := ?jpJ
    · clear_value jpJ
      split
      · refine VM.Keeps.bind (hmrb _ _ _ _) fun _ _ => ?_
        extract_lets -underBinder +onlyGivenNames rr
        split
        · extract_lets -underBinder +onlyGivenNames bodyRef' cellsI' bitsI'
          split
          extract_lets -underBinder +onlyGivenNames fwdFee' ihrFee'
          keeps_leaf (hjpJ _ _ _ _ _)
        · keeps_leaf (hjpJ _ _ _ _ _)
      · keeps_leaf (hjpJ _ _ _ _ _)
    -- the fees pushed and the action installed
    intro a b c d e y
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jpJ
    mvcgen
    all_goals wf_cont [Cell.mkOrdinary_WF, natToBits_size]
  · exact hnext

/-- The Msg family keeps states well-formed. -/
theorem execInstrMsg_WF : FamilyWF execInstrMsg := by
  intro i next hi hnext
  unfold execInstrMsg
  exact execInstrMsgSendMsg_WF i _ hi <|
    execInstrMsgSendRawMsg_WF i _ hi <|
    execInstrMsgRawReserve_WF i _ hi <|
    execInstrMsgRawReserveX_WF i _ hi <|
    execInstrMsgSetCode_WF i _ hi <|
    execInstrMsgSetLibCode_WF i _ hi <|
    execInstrMsgChangeLib_WF i _ hi <|
    hnext

end TvmLean

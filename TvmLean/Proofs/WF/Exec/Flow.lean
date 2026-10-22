import TvmLean.Proofs.WF.JoinPoints
import TvmLean.Proofs.WF.Exec.Stack
import TvmLean.Proofs.WF.Exec.Arith
import TvmLean.Proofs.WF.Exec.Cell
import TvmLean.Proofs.WF.Exec.CellOp
import TvmLean.Proofs.WF.Exec.Cont
import TvmLean.Proofs.WF.Exec.Msg

/-!
# The Flow family keeps states well-formed

`execInstrFlow_WF`: every handler of `execInstrFlow` (`TvmLean/Semantics/Exec/Flow/`) keeps
`VmState.WF`, so the family does, given the obligations of the families a `RUNVM` child runs that
this module does not import (Tuple, TonEnv, Crypto, Misc, Debug, Exception, Dict; discharged in
`TvmLean/Proofs/WF/All.lean`); the Stack, Cont, Cell, Arith, CellOp and Msg families are used
through their theorems.

* The 46 handlers other than `RUNVM` (`execInstrFlowChildNoRunvm_WF`, the Flow family of a child
  VM): `mvcgen` and `wf_cont` (`Calls.lean`), with the specifications of `VM.call`, `VM.jump`,
  `VM.extractCc`, the private argument readers of `CALLCCVARARGS`, `CALLXVARARGS` and `IFBITJMP`,
  the cells the `...REF` instructions carry (`Instr.WF`), and `VmState.c1Envelope` and
  `VmState.c1SaveSet` unfolded for the loops of `LoopExt`.
* `RUNVM` and `RUNVMX` (`execInstrFlowRunvmWith_WF`): the child state (its stack, the registers
  `c3`, `c4`, `c7` it gets, its code) is well-formed, so is the state it ends in
  (`VmState.WF.runWith`, `childRun_WF`), and the parent takes back the child's libraries, values
  and committed `c4`, `c5`. `runChildVm` has 19 join points in a row, too many for `mvcgen`
  (`JoinPoints.lean`): `runChildVm_keeps` proves it a join point at a time.
* The child runs the instructions of `execInstrNested`, a `RUNVM` at each depth down to a VM
  without one (`execInstrChildNoRunvm`): `execInstrNested_WF` by induction on the depth.
-/

open Std.Do

set_option mvcgen.warning false

-- the matches of the loops of `LoopExt` need more than the default
set_option maxHeartbeats 4000000

namespace TvmLean

/-! ## Helpers -/

/-- The argument reader of `CALLCCVARARGS` (private). -/
@[spec] theorem popCallccVarArgBounded_spec :
    ⦃fun st => ⌜st.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Flow.Callcc TvmLean.popCallccVarArgBounded)
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Flow.Callcc TvmLean.popCallccVarArgBounded
  mvcgen
  all_goals wf_vc

/-- The argument reader of `CALLXVARARGS` (private). -/
@[spec] theorem popCallxVarArgBounded_spec :
    ⦃fun st => ⌜st.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Flow.CallxVarArgs TvmLean.popCallxVarArgBounded)
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Flow.CallxVarArgs TvmLean.popCallxVarArgBounded
  mvcgen
  all_goals wf_vc

/-- The bit test of `IFBITJMP` and its variants (private). -/
@[spec] theorem popIntFiniteKeepAndBit_spec (idx : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.popIntFiniteKeepAndBit) idx
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.popIntFiniteKeepAndBit
  mvcgen
  all_goals wf_vc

/-- The count of `REPEAT` and `REPEATEND`. -/
@[spec] theorem popSmallintRepeatCount_spec :
    ⦃fun st => ⌜st.WF⌝⦄ popSmallintRepeatCount
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [popSmallintRepeatCount]
  all_goals wf_vc

/-! The cells the `...REF` instructions carry (`Instr.WF`). -/

@[simp] theorem Instr.wf_ifref (s : Slice) : (Instr.ifref s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_ifnotref (s : Slice) : (Instr.ifnotref s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_ifjmpref (s : Slice) : (Instr.ifjmpref s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_ifnotjmpref (s : Slice) : (Instr.ifnotjmpref s).WF ↔ s.WF := Iff.rfl
/-! The cells the `...REF` instructions carry (`Instr.WF`). -/

@[simp] theorem Instr.wf_ifrefElse (s : Slice) : (Instr.ifrefElse s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_ifelseRef (s : Slice) : (Instr.ifelseRef s).WF ↔ s.WF := Iff.rfl
/-! The cells the `...REF` instructions carry (`Instr.WF`). -/

@[simp] theorem Instr.wf_ifrefElseRef (s t : Slice) :
    (Instr.ifrefElseRef s t).WF ↔ s.WF ∧ t.WF := Iff.rfl
@[simp] theorem Instr.wf_callRef (s : Slice) : (Instr.callRef s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_jmpRef (s : Slice) : (Instr.jmpRef s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_jmpRefData (s : Slice) : (Instr.jmpRefData s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_contExt_ifbitjmpref (n : Nat) (s : Slice) :
    (Instr.contExt (.ifbitjmpref n s)).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_contExt_ifnbitjmpref (n : Nat) (s : Slice) :
    (Instr.contExt (.ifnbitjmpref n s)).WF ↔ s.WF := Iff.rfl

theorem VmState.callTo_WF {st : VmState} {k : Continuation} (h : st.WF) (hk : k.WF) :
    (st.callTo k).WF := h.callTo hk

/-- `wf_cont` with the lemmas of the Flow family: the saved registers set, the calls of
`IFELSE`, the jumps of `IFNOTJMP` and the cells and slices the instructions carry. -/
macro "wf_flow" : tactic => `(tactic|
  wf_cont [Continuation.WF.defineC0, Continuation.WF.defineC1, VmState.callTo_WF, VmState.wf_iff,
    Regs.wf_iff, VmState.jumpTo, Instr.wf_ifref, Instr.wf_ifnotref, Instr.wf_ifjmpref,
    Instr.wf_ifnotjmpref, Instr.wf_ifrefElse, Instr.wf_ifelseRef, Instr.wf_ifrefElseRef,
    Instr.wf_callRef, Instr.wf_jmpRef, Instr.wf_jmpRefData, Instr.wf_contExt_ifbitjmpref,
    Instr.wf_contExt_ifnbitjmpref, Instr.wf_pushSliceConst, Instr.wf_pushCont, Instr.wf_pushRef,
    Instr.wf_pushRefSlice, Instr.wf_pushRefCont, → Slice.WF.cell_wf])

/-! ## The handlers other than `RUNVM` -/

theorem execInstrFlowSetcp_WF : FamilyWF execInstrFlowSetcp := by
  intro i next hi hnext
  mvcgen [execInstrFlowSetcp, hnext]
  all_goals wf_flow

theorem execInstrFlowIfret_WF : FamilyWF execInstrFlowIfret := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfret, hnext]
  all_goals wf_flow

theorem execInstrFlowIfnotret_WF : FamilyWF execInstrFlowIfnotret := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfnotret, hnext]
  all_goals wf_flow

theorem execInstrFlowIfretAlt_WF : FamilyWF execInstrFlowIfretAlt := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfretAlt, hnext]
  all_goals wf_flow

theorem execInstrFlowIf_WF : FamilyWF execInstrFlowIf := by
  intro i next hi hnext
  mvcgen [execInstrFlowIf, hnext]
  all_goals wf_flow

theorem execInstrFlowIfnot_WF : FamilyWF execInstrFlowIfnot := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfnot, hnext]
  all_goals wf_flow

theorem execInstrFlowPushSliceConst_WF : FamilyWF execInstrFlowPushSliceConst := by
  intro i next hi hnext
  mvcgen [execInstrFlowPushSliceConst, hnext]
  all_goals wf_flow

theorem execInstrFlowPushCont_WF : FamilyWF execInstrFlowPushCont := by
  intro i next hi hnext
  mvcgen [execInstrFlowPushCont, hnext]
  all_goals wf_flow

theorem execInstrFlowPushRef_WF : FamilyWF execInstrFlowPushRef := by
  intro i next hi hnext
  mvcgen [execInstrFlowPushRef, hnext]
  all_goals wf_flow

theorem execInstrFlowPushRefSlice_WF : FamilyWF execInstrFlowPushRefSlice := by
  intro i next hi hnext
  mvcgen [execInstrFlowPushRefSlice, hnext]
  all_goals wf_flow

theorem execInstrFlowPushRefCont_WF : FamilyWF execInstrFlowPushRefCont := by
  intro i next hi hnext
  mvcgen [execInstrFlowPushRefCont, hnext]
  all_goals wf_flow

theorem execInstrFlowExecute_WF : FamilyWF execInstrFlowExecute := by
  intro i next hi hnext
  mvcgen [execInstrFlowExecute, hnext]
  all_goals wf_flow

theorem execInstrFlowJmpx_WF : FamilyWF execInstrFlowJmpx := by
  intro i next hi hnext
  mvcgen [execInstrFlowJmpx, hnext]
  all_goals wf_flow

theorem execInstrFlowCallxArgs_WF : FamilyWF execInstrFlowCallxArgs := by
  intro i next hi hnext
  mvcgen [execInstrFlowCallxArgs, hnext]
  all_goals wf_flow

theorem execInstrFlowJmpxArgs_WF : FamilyWF execInstrFlowJmpxArgs := by
  intro i next hi hnext
  mvcgen [execInstrFlowJmpxArgs, hnext]
  all_goals wf_flow

theorem execInstrFlowCallcc_WF : FamilyWF execInstrFlowCallcc := by
  intro i next hi hnext
  mvcgen [execInstrFlowCallcc, hnext]
  all_goals wf_flow

theorem execInstrFlowCallxVarArgs_WF : FamilyWF execInstrFlowCallxVarArgs := by
  intro i next hi hnext
  mvcgen [execInstrFlowCallxVarArgs, hnext]
  all_goals wf_flow

theorem execInstrFlowRet_WF : FamilyWF execInstrFlowRet := by
  intro i next hi hnext
  mvcgen [execInstrFlowRet, hnext]
  all_goals wf_flow

theorem execInstrFlowRetAlt_WF : FamilyWF execInstrFlowRetAlt := by
  intro i next hi hnext
  mvcgen [execInstrFlowRetAlt, hnext]
  all_goals wf_flow

theorem execInstrFlowRetBool_WF : FamilyWF execInstrFlowRetBool := by
  intro i next hi hnext
  mvcgen [execInstrFlowRetBool, hnext]
  all_goals wf_flow

theorem execInstrFlowRetArgs_WF : FamilyWF execInstrFlowRetArgs := by
  intro i next hi hnext
  mvcgen [execInstrFlowRetArgs, hnext]
  all_goals wf_flow

theorem execInstrFlowRetVarArgs_WF : FamilyWF execInstrFlowRetVarArgs := by
  intro i next hi hnext
  mvcgen [execInstrFlowRetVarArgs, hnext]
  all_goals wf_flow

theorem execInstrFlowRetData_WF : FamilyWF execInstrFlowRetData := by
  intro i next hi hnext
  mvcgen [execInstrFlowRetData, hnext]
  all_goals wf_flow

theorem execInstrFlowJmpxVarArgs_WF : FamilyWF execInstrFlowJmpxVarArgs := by
  intro i next hi hnext
  mvcgen [execInstrFlowJmpxVarArgs, hnext]
  all_goals wf_flow

theorem execInstrFlowJmpxData_WF : FamilyWF execInstrFlowJmpxData := by
  intro i next hi hnext
  mvcgen [execInstrFlowJmpxData, hnext]
  all_goals wf_flow

theorem execInstrFlowIfjmp_WF : FamilyWF execInstrFlowIfjmp := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfjmp, hnext]
  all_goals wf_flow

theorem execInstrFlowIfnotjmp_WF : FamilyWF execInstrFlowIfnotjmp := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfnotjmp, hnext]
  all_goals wf_flow

theorem execInstrFlowIfelse_WF : FamilyWF execInstrFlowIfelse := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfelse, hnext]
  all_goals wf_flow

theorem execInstrFlowIfref_WF : FamilyWF execInstrFlowIfref := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfref, hnext]
  all_goals wf_flow

theorem execInstrFlowIfnotref_WF : FamilyWF execInstrFlowIfnotref := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfnotref, hnext]
  all_goals wf_flow

theorem execInstrFlowIfjmpref_WF : FamilyWF execInstrFlowIfjmpref := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfjmpref, hnext]
  all_goals wf_flow

theorem execInstrFlowIfnotjmpref_WF : FamilyWF execInstrFlowIfnotjmpref := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfnotjmpref, hnext]
  all_goals wf_flow

theorem execInstrFlowIfrefElse_WF : FamilyWF execInstrFlowIfrefElse := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfrefElse, hnext]
  all_goals wf_flow

theorem execInstrFlowIfelseRef_WF : FamilyWF execInstrFlowIfelseRef := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfelseRef, hnext]
  all_goals wf_flow

theorem execInstrFlowIfrefElseRef_WF : FamilyWF execInstrFlowIfrefElseRef := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfrefElseRef, hnext]
  all_goals wf_flow

theorem execInstrFlowIfBitJmp_WF : FamilyWF execInstrFlowIfBitJmp := by
  intro i next hi hnext
  mvcgen [execInstrFlowIfBitJmp, hnext]
  all_goals wf_flow

theorem execInstrFlowCallRef_WF : FamilyWF execInstrFlowCallRef := by
  intro i next hi hnext
  mvcgen [execInstrFlowCallRef, hnext]
  all_goals wf_flow

theorem execInstrFlowJmpRef_WF : FamilyWF execInstrFlowJmpRef := by
  intro i next hi hnext
  mvcgen [execInstrFlowJmpRef, hnext]
  all_goals wf_flow

theorem execInstrFlowCallDict_WF : FamilyWF execInstrFlowCallDict := by
  intro i next hi hnext
  mvcgen [execInstrFlowCallDict, hnext]
  all_goals wf_flow

theorem execInstrFlowPrepareDict_WF : FamilyWF execInstrFlowPrepareDict := by
  intro i next hi hnext
  mvcgen [execInstrFlowPrepareDict, hnext]
  all_goals wf_flow

theorem execInstrFlowUntil_WF : FamilyWF execInstrFlowUntil := by
  intro i next hi hnext
  mvcgen [execInstrFlowUntil, hnext]
  all_goals wf_flow

theorem execInstrFlowWhile_WF : FamilyWF execInstrFlowWhile := by
  intro i next hi hnext
  mvcgen [execInstrFlowWhile, hnext]
  all_goals wf_flow

theorem execInstrFlowLoopExt_WF : FamilyWF execInstrFlowLoopExt := by
  intro i next hi hnext
  mvcgen [execInstrFlowLoopExt, hnext]
  all_goals (try simp (config := { zetaDelta := true }) only [VmState.c1Envelope,
    VmState.c1SaveSet] at *)
  all_goals wf_flow

theorem execInstrFlowBlkdrop2_WF : FamilyWF execInstrFlowBlkdrop2 := by
  intro i next hi hnext
  mvcgen [execInstrFlowBlkdrop2, hnext]
  all_goals wf_flow

theorem execInstrFlowBlkdrop_WF : FamilyWF execInstrFlowBlkdrop := by
  intro i next hi hnext
  mvcgen [execInstrFlowBlkdrop, hnext]
  all_goals wf_flow

theorem execInstrFlowDrop2_WF : FamilyWF execInstrFlowDrop2 := by
  intro i next hi hnext
  mvcgen [execInstrFlowDrop2, hnext]
  all_goals wf_flow

/-! ## `RUNVM` -/

/-- The gas limits `RUNVM` takes. -/
@[spec] theorem popGasRange_spec :
    ⦃fun st => ⌜st.WF⌝⦄ popGasRange ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [popGasRange]
  all_goals wf_vc

/-- The mode `RUNVMX` takes. -/
@[spec] theorem popNatUpToSigned_spec (max : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄ popNatUpToSigned max
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [popNatUpToSigned]
  all_goals wf_vc

/-- The `c7` `RUNVM` takes for the child. -/
@[spec] theorem VM.popTuple_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popTuple
      ⦃post⟨fun t st => ⌜st.WF ∧ ∀ v ∈ t, v.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popTuple]
  all_goals wf_vc

/-- The child run of `RUNVM` ends in a well-formed state. -/
theorem childRun_WF {exec : Instr → VM Unit} (hexec : ExecWF exec) {st : VmState} (h : st.WF) :
    (childRun exec st).2.WF := by
  have := VmState.WF.runWith hexec st.gas.stepBound h
  unfold childRun
  split <;> rename_i heq <;> rw [heq] at this <;> exact this

/-- The child run of `RUNVM` keeps states well-formed (a definition, so that the closing tactics
leave it alone). -/
def ChildRunWF (exec : Instr → VM Unit) : Prop :=
  ∀ st c st', childRun exec st = (c, st') → st.WF → st'.WF

/-- C++ `exec_runvm_common` and `run_child_vm`, `restore_parent_vm`: the child state is
well-formed (the values passed, the code, `c3`, `c4`, `c7`), so is the state the child ends in, and
the parent state returned (with the child's libraries, values, and committed `c4` and `c5`). A join
point at a time (`JoinPoints.lean`), each with the facts it needs. -/
theorem runChildVm_keeps {childExec : Instr → VM Unit}
    (hrun : ChildRunWF childExec) {parent : VmState}
    (hp : parent.WF) (mode : Nat) :
    (runChildVm childExec parent mode).Keeps VmState.WF := by
  unfold runChildVm
  -- after the mode check
  extract_lets -underBinder +onlyGivenNames jp1
  have hjp1 : ∀ y, VM.KeepsIf True (jp1 y) VmState.WF := ?jp1
  · clear_value jp1
    mvcgen
    all_goals (try jp_close (hjp1 _))
    all_goals first | trivial | wf_cont
  intro y
  apply VM.KeepsIf.of_keeps
  intro _
  unfold jp1
  refine VM.Keeps.bind (VM.Keeps.set' ((VmState.consumeGas_WF _ _).mpr hp)) fun _ _ => ?_
  clear hp
  refine VM.Keeps.bind VM.Keeps.get' fun _ hs => ?_
  clear hs
  -- after the gas check
  extract_lets -underBinder +onlyGivenNames jp2
  have hjp2 : ∀ y, VM.KeepsIf True (jp2 y) VmState.WF := ?jp2
  · clear_value jp2
    mvcgen
    all_goals (try jp_close (hjp2 _))
    all_goals first | trivial | wf_cont
  intro y
  apply VM.KeepsIf.of_keeps
  intro _
  unfold jp2
  extract_lets -underBinder +onlyGivenNames sameC3 push0 withData returnGas loadC7
    returnActions hasHardMax isolateGas hasRetVals jp3
  -- the gas limits, c7, the data and the number of values returned
  have hjp3 : ∀ gasMax0, VM.KeepsIf True (jp3 gasMax0) VmState.WF := ?jp3
  · clear_value jp3
    mvcgen
    all_goals (try jp_close (hjp3 _))
    all_goals first | trivial | wf_cont
  intro gasMax0
  apply VM.KeepsIf.of_keeps
  intro _
  unfold jp3
  extract_lets -underBinder +onlyGivenNames jp4
  have hjp4 : ∀ gasLimit0, VM.KeepsIf True (jp4 gasLimit0) VmState.WF := ?jp4
  · clear_value jp4
    mvcgen
    all_goals (try jp_close (hjp4 _))
    all_goals first | trivial | wf_cont
  intro gasLimit0
  apply VM.KeepsIf.of_keeps
  intro _
  unfold jp4
  extract_lets -underBinder +onlyGivenNames gasMax1 jp5
  have hjp5 : ∀ c7Opt, VM.KeepsIf (∀ t, c7Opt = some t → ∀ v ∈ t, v.WF) (jp5 c7Opt)
      VmState.WF := ?jp5
  · clear_value jp5
    mvcgen
    all_goals (try jp_close (hjp5 _))
    all_goals wf_cont
  intro c7Opt
  apply VM.KeepsIf.of_keeps
  intro hc7
  unfold jp5
  extract_lets -underBinder +onlyGivenNames jp6
  have hjp6 : ∀ dataOpt, VM.KeepsIf (∀ c, dataOpt = some c → c.WF) (jp6 dataOpt)
      VmState.WF := ?jp6
  · clear_value jp6
    mvcgen
    all_goals (try jp_close (hjp6 _))
    all_goals wf_cont
  intro dataOpt
  apply VM.KeepsIf.of_keeps
  intro hdata
  unfold jp6
  extract_lets -underBinder +onlyGivenNames jp7
  have hjp7 : ∀ retValsOpt, VM.KeepsIf True (jp7 retValsOpt) VmState.WF := ?jp7
  · clear_value jp7
    mvcgen
    all_goals (try jp_close (hjp7 _))
    all_goals first | trivial | wf_cont
  -- the code and the stack of the child
  intro retValsOpt
  apply VM.KeepsIf.of_keeps
  intro _
  unfold jp7
  refine VM.Keeps.bind VM.popSlice_spec fun codeSlice hcode => ?_
  refine VM.Keeps.bind VM.Keeps.get' fun _ hs => ?_
  clear hs
  extract_lets -underBinder +onlyGivenNames jp8
  have hjp8 : ∀ y, VM.KeepsIf True (jp8 y) VmState.WF := ?jp8
  · clear_value jp8
    mvcgen
    all_goals (try jp_close (hjp8 _))
    all_goals first | trivial | wf_cont
  intro y
  apply VM.KeepsIf.of_keeps
  intro _
  unfold jp8
  refine VM.Keeps.bind (VM.Keeps.ofWF VM.popInt_spec) fun lift _ => ?_
  extract_lets -underBinder +onlyGivenNames jp9
  have hjp9 : ∀ stackSize, VM.KeepsIf True (jp9 stackSize) VmState.WF := ?jp9
  · clear_value jp9
    mvcgen
    all_goals (try jp_close (hjp9 _))
    all_goals first | trivial | wf_cont
  intro stackSize
  apply VM.KeepsIf.of_keeps
  intro _
  unfold jp9
  refine VM.Keeps.bind VM.Keeps.get' fun _ hs => ?_
  clear hs
  extract_lets -underBinder +onlyGivenNames jp10
  have hjp10 : ∀ y, VM.KeepsIf True (jp10 y) VmState.WF := ?jp10
  · clear_value jp10
    mvcgen
    all_goals (try jp_close (hjp10 _))
    all_goals first | trivial | wf_cont
  intro y
  apply VM.KeepsIf.of_keeps
  intro _
  unfold jp10
  extract_lets -underBinder +onlyGivenNames childStack0
  refine VM.Keeps.bind (VM.Keeps.forIn_range (fun cs => ∀ v ∈ cs, v.WF) _
    (by simp [childStack0]) fun i b hb => ?_) fun cs0 hcs0 => ?_
  · mvcgen
    all_goals wf_cont [ForInStep.value]
  extract_lets -underBinder +onlyGivenNames childStack1
  refine VM.Keeps.bind (Q := fun _ => True) ?_ fun _ _ => ?_
  · mvcgen
    all_goals wf_cont
  refine VM.Keeps.bind VM.Keeps.get' fun _ hs => ?_
  clear hs
  extract_lets -underBinder +onlyGivenNames jp11
  have hjp11 : ∀ cs y, VM.KeepsIf (∀ v ∈ cs, v.WF) (jp11 cs y) VmState.WF := ?jp11
  · clear_value jp11
    mvcgen
    all_goals (try jp_close (hjp11 _ _))
    all_goals wf_cont
  clear hcs0
  intro cs y
  apply VM.KeepsIf.of_keeps
  intro hcs
  unfold jp11
  extract_lets -underBinder +onlyGivenNames jp12
  have hjp12 : ∀ cs y, VM.KeepsIf (∀ v ∈ cs, v.WF) (jp12 cs y) VmState.WF := ?jp12
  · clear_value jp12
    mvcgen
    all_goals (try jp_close (hjp12 _ _))
    all_goals wf_cont
  clear hcs
  -- the registers and the state of the child
  intro cs y
  apply VM.KeepsIf.of_keeps
  intro hcs
  unfold jp12
  extract_lets -underBinder +onlyGivenNames childCc childRegs0 childRegs1 childRegs2 childRegs3
  have hcc : childCc.WF := by simp [childCc, hcode]
  have hr1 : childRegs1.WF := by
    simp only [childRegs1, childRegs0]
    split <;> simp [Regs.wf_iff, Regs.initial, hcc]
  have hr2 : childRegs2.WF := by
    simp only [childRegs2]
    split
    · exact hr1
    · rename_i t
      have ht := hc7 t rfl
      simp only [Regs.wf_iff] at hr1 ⊢
      exact ⟨hr1.1, hr1.2.1, hr1.2.2.1, hr1.2.2.2.1, hr1.2.2.2.2.1, hr1.2.2.2.2.2.1, ht⟩
  have hr3 : childRegs3.WF := by
    simp only [childRegs3]
    split
    · exact hr2
    · rename_i c
      have hc := hdata c rfl
      simp only [Regs.wf_iff] at hr2 ⊢
      exact ⟨hr2.1, hr2.2.1, hr2.2.2.1, hr2.2.2.2.1, hc, hr2.2.2.2.2.2.1, hr2.2.2.2.2.2.2⟩
  clear_value childRegs3 childRegs2 childRegs1 childRegs0 childCc
  clear hr1 hr2 hc7 hdata hcode
  refine VM.Keeps.bind VM.Keeps.get' fun _ hs => ?_
  clear hs
  extract_lets -underBinder +onlyGivenNames parentRem0 jp13
  have hjp13 : ∀ y, VM.KeepsIf True (jp13 y) VmState.WF := ?jp13
  · clear_value jp13
    mvcgen
    all_goals (try jp_close (hjp13 _))
    all_goals first | trivial | wf_cont
  -- the child run
  intro y
  apply VM.KeepsIf.of_keeps
  intro _
  unfold jp13
  refine VM.Keeps.bind VM.Keeps.get' fun pap hpap => ?_
  extract_lets -underBinder +onlyGivenNames parentRem gasMax gasLimit childGas src child
  have hchild : child.WF := by
    simp only [child, src]
    exact ⟨hcs, hr3, hcc, by simp [VmState.initial, CommittedState.empty],
      by simp [VmState.initial, CommittedState.empty], hpap.libraries⟩
  clear_value child
  split
  rename_i childExit childFinal hcr
  have hfin : childFinal.WF := hrun _ _ _ hcr hchild
  clear hchild hcr hcs hr3 hcc
  extract_lets -underBinder +onlyGivenNames resCode childConsumed pay parentAfter0 parentAfter1 jp14
  have hpa1 : parentAfter1.WF := by
    simp only [parentAfter1, parentAfter0, VmState.consumeGas]
    exact ⟨hpap.stack, hpap.regs, hpap.cc, hpap.committedC4, hpap.committedC5, hfin.libraries⟩
  clear_value parentAfter1 parentAfter0
  clear hpap
  -- the values returned
  have hjp14 : ∀ pa rc y, VM.KeepsIf pa.WF (jp14 pa rc y) VmState.WF := ?jp14
  · clear_value jp14
    mvcgen
    all_goals (try jp_close (hjp14 _ _ _))
    all_goals wf_cont
  clear hpa1
  intro pa rc y
  apply VM.KeepsIf.of_keeps
  intro hpa
  unfold jp14
  extract_lets -underBinder +onlyGivenNames depth retCnt0 jp15
  have hjp15 : ∀ pa rc rcnt y, VM.KeepsIf pa.WF (jp15 pa rc rcnt y) VmState.WF := ?jp15
  · clear_value jp15
    mvcgen
    all_goals (try jp_close (hjp15 _ _ _ _))
    all_goals wf_cont
  clear hpa
  intro pa rc rcnt y
  apply VM.KeepsIf.of_keeps
  intro hpa
  unfold jp15
  extract_lets -underBinder +onlyGivenNames pa1 jp16
  have hjp16 : ∀ pa y, VM.KeepsIf pa.WF (jp16 pa y) VmState.WF := ?jp16
  · clear_value jp16
    mvcgen
    all_goals (try jp_close (hjp16 _ _))
    all_goals wf_cont
  clear hpa
  intro pa y
  apply VM.KeepsIf.of_keeps
  intro hpa
  unfold jp16
  refine VM.Keeps.bind (VM.Keeps.forIn_list VmState.WF _ hpa fun i b hb => ?_) fun r hr => ?_
  · mvcgen
    all_goals (try simp only [ForInStep.value_yield] at *)
    all_goals wf_cont
  clear hpa
  extract_lets -underBinder +onlyGivenNames pa2 pa3 uncommitted jp17
  -- the committed c4 and c5 of the child and the gas it used
  have hjp17 : ∀ pa y, VM.KeepsIf pa.WF (jp17 pa y) VmState.WF := ?jp17
  · clear_value jp17
    mvcgen
    all_goals (try jp_close (hjp17 _ _))
    all_goals wf_cont
  clear hr
  intro pa y
  apply VM.KeepsIf.of_keeps
  intro hpa
  unfold jp17
  extract_lets -underBinder +onlyGivenNames jp18
  have hjp18 : ∀ pa y, VM.KeepsIf pa.WF (jp18 pa y) VmState.WF := ?jp18
  · clear_value jp18
    mvcgen
    all_goals (try jp_close (hjp18 _ _))
    all_goals wf_cont
  clear hpa
  intro pa y
  apply VM.KeepsIf.of_keeps
  intro hpa
  unfold jp18
  extract_lets -underBinder +onlyGivenNames jp19
  have hjp19 : ∀ pa y, VM.KeepsIf pa.WF (jp19 pa y) VmState.WF := ?jp19
  · clear_value jp19
    mvcgen
    all_goals (try jp_close (hjp19 _ _))
    all_goals wf_cont
  clear hpa
  intro pa y
  apply VM.KeepsIf.of_keeps
  intro hpa
  unfold jp19
  exact VM.Keeps.pure' hpa

/-- `RUNVM` and `RUNVMX` keep states well-formed when the instructions the child runs do. -/
theorem execInstrFlowRunvmWith_WF {childExec : Instr → VM Unit} (hexec : ExecWF childExec) :
    FamilyWF (execInstrFlowRunvmWith childExec) := by
  have hrun : ChildRunWF childExec := fun st c st' h hs => by
    have := childRun_WF hexec hs
    rw [h] at this
    exact this
  intro i next hi hnext
  unfold execInstrFlowRunvmWith
  split
  · extract_lets -underBinder +onlyGivenNames mode
    refine VM.Keeps.bind VM.Keeps.get' fun st hst => ?_
    refine VM.Keeps.bind (runChildVm_keeps hrun hst mode) fun st' hst' => ?_
    exact VM.Keeps.set' hst'
  · refine VM.Keeps.bind (VM.Keeps.ofWF (popNatUpToSigned_spec 4095)) fun mode _ => ?_
    refine VM.Keeps.bind VM.Keeps.get' fun st hst => ?_
    refine VM.Keeps.bind (runChildVm_keeps hrun hst mode) fun st' hst' => ?_
    exact VM.Keeps.set' hst'
  · exact hnext

/-! ## The family -/

/-- The Flow family of a child VM (`RUNVM` excluded) keeps states well-formed. -/
theorem execInstrFlowChildNoRunvm_WF : FamilyWF execInstrFlowChildNoRunvm := by
  intro i next hi hnext
  unfold execInstrFlowChildNoRunvm
  exact execInstrFlowSetcp_WF i _ hi <|
    execInstrFlowIfret_WF i _ hi <|
    execInstrFlowIfnotret_WF i _ hi <|
    execInstrFlowIfretAlt_WF i _ hi <|
    execInstrFlowIf_WF i _ hi <|
    execInstrFlowIfnot_WF i _ hi <|
    execInstrFlowPushSliceConst_WF i _ hi <|
    execInstrFlowPushCont_WF i _ hi <|
    execInstrFlowPushRef_WF i _ hi <|
    execInstrFlowPushRefSlice_WF i _ hi <|
    execInstrFlowPushRefCont_WF i _ hi <|
    execInstrFlowExecute_WF i _ hi <|
    execInstrFlowJmpx_WF i _ hi <|
    execInstrFlowCallxArgs_WF i _ hi <|
    execInstrFlowJmpxArgs_WF i _ hi <|
    execInstrFlowCallcc_WF i _ hi <|
    execInstrFlowCallxVarArgs_WF i _ hi <|
    execInstrFlowRet_WF i _ hi <|
    execInstrFlowRetAlt_WF i _ hi <|
    execInstrFlowRetBool_WF i _ hi <|
    execInstrFlowRetArgs_WF i _ hi <|
    execInstrFlowRetVarArgs_WF i _ hi <|
    execInstrFlowRetData_WF i _ hi <|
    execInstrFlowJmpxVarArgs_WF i _ hi <|
    execInstrFlowJmpxData_WF i _ hi <|
    execInstrFlowIfjmp_WF i _ hi <|
    execInstrFlowIfnotjmp_WF i _ hi <|
    execInstrFlowIfelse_WF i _ hi <|
    execInstrFlowIfref_WF i _ hi <|
    execInstrFlowIfnotref_WF i _ hi <|
    execInstrFlowIfjmpref_WF i _ hi <|
    execInstrFlowIfnotjmpref_WF i _ hi <|
    execInstrFlowIfrefElse_WF i _ hi <|
    execInstrFlowIfelseRef_WF i _ hi <|
    execInstrFlowIfrefElseRef_WF i _ hi <|
    execInstrFlowIfBitJmp_WF i _ hi <|
    execInstrFlowCallRef_WF i _ hi <|
    execInstrFlowJmpRef_WF i _ hi <|
    execInstrFlowCallDict_WF i _ hi <|
    execInstrFlowPrepareDict_WF i _ hi <|
    execInstrFlowUntil_WF i _ hi <|
    execInstrFlowWhile_WF i _ hi <|
    execInstrFlowLoopExt_WF i _ hi <|
    execInstrFlowBlkdrop2_WF i _ hi <|
    execInstrFlowBlkdrop_WF i _ hi <|
    execInstrFlowDrop2_WF i _ hi <|
    hnext

/-- The instructions of a VM without `RUNVM` keep states well-formed, given the families this
module does not import. -/
theorem execInstrChildNoRunvm_WF (hTuple : FamilyWF execInstrTuple)
    (hTonEnv : FamilyWF execInstrTonEnv) (hCrypto : FamilyWF execInstrCrypto)
    (hMisc : FamilyWF execInstrMisc) (hDebug : FamilyWF execInstrDebug)
    (hException : FamilyWF execInstrException) (hDict : FamilyWF execInstrDict) :
    ExecWF execInstrChildNoRunvm := by
  intro i hi
  unfold execInstrChildNoRunvm
  have hthrow : (throw .invOpcode : VM Unit).KeepsWF := by mvcgen
  exact execInstrStack_WF i _ hi <| execInstrCont_WF i _ hi <| execInstrCell_WF i _ hi <|
    execInstrFlowChildNoRunvm_WF i _ hi <| execInstrArith_WF i _ hi <| hTuple i _ hi <|
    execInstrCellOp_WF i _ hi <| hTonEnv i _ hi <| hCrypto i _ hi <| execInstrMsg_WF i _ hi <|
    hMisc i _ hi <| hDebug i _ hi <| hException i _ hi <| hDict i _ hi <| hthrow

/-- The instructions of a `RUNVM` child at any depth keep states well-formed. -/
theorem execInstrNested_WF (hTuple : FamilyWF execInstrTuple)
    (hTonEnv : FamilyWF execInstrTonEnv) (hCrypto : FamilyWF execInstrCrypto)
    (hMisc : FamilyWF execInstrMisc) (hDebug : FamilyWF execInstrDebug)
    (hException : FamilyWF execInstrException) (hDict : FamilyWF execInstrDict) :
    ∀ depth, ExecWF (execInstrNested depth)
  | 0 => by
    unfold execInstrNested
    exact execInstrChildNoRunvm_WF hTuple hTonEnv hCrypto hMisc hDebug hException hDict
  | depth + 1 => by
    intro i hi
    unfold execInstrNested
    exact execInstrFlowRunvmWith_WF
      (execInstrNested_WF hTuple hTonEnv hCrypto hMisc hDebug hException hDict depth) i _ hi
      (execInstrChildNoRunvm_WF hTuple hTonEnv hCrypto hMisc hDebug hException hDict i hi)

/-- `RUNVM` and `RUNVMX` of the VM, whose child runs `execInstrNested` at the depth its gas
allows. -/
theorem execInstrFlowRunvm_WF (hTuple : FamilyWF execInstrTuple)
    (hTonEnv : FamilyWF execInstrTonEnv) (hCrypto : FamilyWF execInstrCrypto)
    (hMisc : FamilyWF execInstrMisc) (hDebug : FamilyWF execInstrDebug)
    (hException : FamilyWF execInstrException) (hDict : FamilyWF execInstrDict) :
    FamilyWF execInstrFlowRunvm := by
  intro i next hi hnext
  unfold execInstrFlowRunvm
  refine VM.Keeps.bind VM.Keeps.get' fun st _ => ?_
  extract_lets -underBinder +onlyGivenNames depth
  exact execInstrFlowRunvmWith_WF
    (execInstrNested_WF hTuple hTonEnv hCrypto hMisc hDebug hException hDict depth) i next hi
    hnext

/-- The Flow family keeps states well-formed, given the families a `RUNVM` child runs that this
module does not import. -/
theorem execInstrFlow_WF (hTuple : FamilyWF execInstrTuple)
    (hTonEnv : FamilyWF execInstrTonEnv) (hCrypto : FamilyWF execInstrCrypto)
    (hMisc : FamilyWF execInstrMisc) (hDebug : FamilyWF execInstrDebug)
    (hException : FamilyWF execInstrException) (hDict : FamilyWF execInstrDict) :
    FamilyWF execInstrFlow := by
  intro i next hi hnext
  unfold execInstrFlow
  exact execInstrFlowSetcp_WF i _ hi <|
    execInstrFlowIfret_WF i _ hi <|
    execInstrFlowIfnotret_WF i _ hi <|
    execInstrFlowIfretAlt_WF i _ hi <|
    execInstrFlowIf_WF i _ hi <|
    execInstrFlowIfnot_WF i _ hi <|
    execInstrFlowPushSliceConst_WF i _ hi <|
    execInstrFlowPushCont_WF i _ hi <|
    execInstrFlowPushRef_WF i _ hi <|
    execInstrFlowPushRefSlice_WF i _ hi <|
    execInstrFlowPushRefCont_WF i _ hi <|
    execInstrFlowExecute_WF i _ hi <|
    execInstrFlowJmpx_WF i _ hi <|
    execInstrFlowCallxArgs_WF i _ hi <|
    execInstrFlowJmpxArgs_WF i _ hi <|
    execInstrFlowCallcc_WF i _ hi <|
    execInstrFlowCallxVarArgs_WF i _ hi <|
    execInstrFlowRet_WF i _ hi <|
    execInstrFlowRetAlt_WF i _ hi <|
    execInstrFlowRetBool_WF i _ hi <|
    execInstrFlowRetArgs_WF i _ hi <|
    execInstrFlowRetVarArgs_WF i _ hi <|
    execInstrFlowRetData_WF i _ hi <|
    execInstrFlowJmpxVarArgs_WF i _ hi <|
    execInstrFlowJmpxData_WF i _ hi <|
    execInstrFlowRunvm_WF hTuple hTonEnv hCrypto hMisc hDebug hException hDict i _ hi <|
    execInstrFlowIfjmp_WF i _ hi <|
    execInstrFlowIfnotjmp_WF i _ hi <|
    execInstrFlowIfelse_WF i _ hi <|
    execInstrFlowIfref_WF i _ hi <|
    execInstrFlowIfnotref_WF i _ hi <|
    execInstrFlowIfjmpref_WF i _ hi <|
    execInstrFlowIfnotjmpref_WF i _ hi <|
    execInstrFlowIfrefElse_WF i _ hi <|
    execInstrFlowIfelseRef_WF i _ hi <|
    execInstrFlowIfrefElseRef_WF i _ hi <|
    execInstrFlowIfBitJmp_WF i _ hi <|
    execInstrFlowCallRef_WF i _ hi <|
    execInstrFlowJmpRef_WF i _ hi <|
    execInstrFlowCallDict_WF i _ hi <|
    execInstrFlowPrepareDict_WF i _ hi <|
    execInstrFlowUntil_WF i _ hi <|
    execInstrFlowWhile_WF i _ hi <|
    execInstrFlowLoopExt_WF i _ hi <|
    execInstrFlowBlkdrop2_WF i _ hi <|
    execInstrFlowBlkdrop_WF i _ hi <|
    execInstrFlowDrop2_WF i _ hi <|
    hnext

end TvmLean

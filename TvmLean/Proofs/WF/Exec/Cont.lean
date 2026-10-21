import TvmLean.Proofs.WF.Calls

/-!
# The Cont family keeps states well-formed

`execInstrCont_WF`: every handler of `execInstrCont` (`TvmLean/Semantics/Exec/Cont/`) keeps
`VmState.WF`, so the family does. The handlers are `mvcgen` and `wf_cont` (`Calls.lean`), with:
* the specifications of the helpers they share: `VM.returnArgsCommon` (`RETURNARGS`),
  `VM.blessArgsCommon` (`BLESSARGS`), and the private argument readers of `BLESSVARARGS` and
  `SETCONTVARARGS`;
* the lemmas on registers led by the operation (`VmState.getCtr_WF`, `VmState.setCtr_WF`,
  `Continuation.defineCtr_WF`, as forward rules of `grind`) and `Continuation.WF.defineC0`,
  `defineC1`;
* the invariant of the loops of `SETCONTCTRMANY` and `SETCONTCTRMANYX` (the state and the
  continuation being defined are well-formed).
-/

open Std.Do

set_option mvcgen.warning false

-- the loops of `SETCONTCTRMANY(X)` and the matches of `POPSAVE` need more than the default
set_option maxHeartbeats 4000000

namespace TvmLean

theorem execInstrContPushCtr_WF : FamilyWF execInstrContPushCtr := by
  intro i next hi hnext
  mvcgen [execInstrContPushCtr, hnext]
  all_goals wf_cont [→ VmState.getCtr_WF, VmState.wf_iff, Regs.wf_iff]

theorem execInstrContPopCtr_WF : FamilyWF execInstrContPopCtr := by
  intro i next hi hnext
  mvcgen [execInstrContPopCtr, hnext]
  all_goals wf_cont [→ VmState.setCtr_WF, VmState.wf_iff, Regs.wf_iff]

theorem execInstrContSetContCtr_WF : FamilyWF execInstrContSetContCtr := by
  intro i next hi hnext
  mvcgen [execInstrContSetContCtr, hnext]
  all_goals wf_cont [→ Continuation.defineCtr_WF]

theorem execInstrContSetContArgs_WF : FamilyWF execInstrContSetContArgs := by
  intro i next hi hnext
  mvcgen [execInstrContSetContArgs, hnext]
  all_goals wf_cont

/-- The argument reader of `SETCONTVARARGS` (private). -/
@[spec] theorem popSetContVarArgBounded_spec (lo hi : Int) :
    ⦃fun st => ⌜st.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Cont.SetContVarArgs TvmLean.popSetContVarArgBounded) lo hi
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Cont.SetContVarArgs TvmLean.popSetContVarArgBounded
  mvcgen
  all_goals wf_vc

theorem execInstrContSetContVarArgs_WF : FamilyWF execInstrContSetContVarArgs := by
  intro i next hi hnext
  mvcgen [execInstrContSetContVarArgs, hnext]
  all_goals wf_cont

theorem execInstrContSetNumVarArgs_WF : FamilyWF execInstrContSetNumVarArgs := by
  intro i next hi hnext
  mvcgen [execInstrContSetNumVarArgs, hnext]
  all_goals wf_cont

/-- `RETURNARGS`, `RETURNVARARGS`: the bottom of the stack goes to the closure stack of `c0`. -/
@[spec] theorem VM.returnArgsCommon_spec (count : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.returnArgsCommon count
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.returnArgsCommon]
  all_goals wf_cont

theorem execInstrContReturnArgs_WF : FamilyWF execInstrContReturnArgs := by
  intro i next hi hnext
  mvcgen [execInstrContReturnArgs, hnext]
  all_goals wf_cont

/-- `BLESSARGS`, `BLESSVARARGS`: the top of the stack becomes the closure stack of the new
continuation. -/
@[spec] theorem VM.blessArgsCommon_spec (copy : Nat) (more : Int) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.blessArgsCommon copy more
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.blessArgsCommon]
  all_goals wf_cont

/-- The argument reader of `BLESSVARARGS` (private). -/
@[spec] theorem popBlessVarArgMore_spec :
    ⦃fun st => ⌜st.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Cont.Bless TvmLean.popBlessVarArgMore)
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Cont.Bless TvmLean.popBlessVarArgMore
  mvcgen
  all_goals wf_vc

theorem execInstrContBless_WF : FamilyWF execInstrContBless := by
  intro i next hi hnext
  mvcgen [execInstrContBless, hnext]
  all_goals wf_cont

theorem execInstrContSaveCtr_WF : FamilyWF execInstrContSaveCtr := by
  intro i next hi hnext
  mvcgen [execInstrContSaveCtr, hnext]
  all_goals wf_cont [→ Continuation.defineCtr_WF]

theorem execInstrContSameAlt_WF : FamilyWF execInstrContSameAlt := by
  intro i next hi hnext
  mvcgen [execInstrContSameAlt, hnext]
  all_goals wf_cont

theorem execInstrContSameAltSave_WF : FamilyWF execInstrContSameAltSave := by
  intro i next hi hnext
  mvcgen [execInstrContSameAltSave, hnext]
  all_goals wf_cont [Continuation.WF.defineC1]

theorem execInstrContBoolAnd_WF : FamilyWF execInstrContBoolAnd := by
  intro i next hi hnext
  mvcgen [execInstrContBoolAnd, hnext]
  all_goals wf_cont [Continuation.WF.defineC0]

theorem execInstrContBoolOr_WF : FamilyWF execInstrContBoolOr := by
  intro i next hi hnext
  mvcgen [execInstrContBoolOr, hnext]
  all_goals wf_cont [Continuation.WF.defineC1]

theorem execInstrContComposBoth_WF : FamilyWF execInstrContComposBoth := by
  intro i next hi hnext
  mvcgen [execInstrContComposBoth, hnext]
  all_goals wf_cont [Continuation.WF.defineC0, Continuation.WF.defineC1]

theorem execInstrContCondSel_WF : FamilyWF execInstrContCondSel := by
  intro i next hi hnext
  mvcgen [execInstrContCondSel, hnext]
  all_goals wf_cont

theorem execInstrContAtExit_WF : FamilyWF execInstrContAtExit := by
  intro i next hi hnext
  mvcgen [execInstrContAtExit, hnext]
  all_goals wf_cont [Continuation.WF.defineC0, Continuation.WF.defineC1]

theorem execInstrContChangeExt_WF : FamilyWF execInstrContChangeExt := by
  intro i next hi hnext
  mvcgen [execInstrContChangeExt, hnext] invariants
  · post⟨fun ⟨_, k⟩ st => ⌜st.WF ∧ k.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun ⟨_, k⟩ st => ⌜st.WF ∧ k.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_cont [→ VmState.getCtr_WF, → VmState.setCtr_WF, → Continuation.defineCtr_WF,
    VmState.wf_iff, Regs.wf_iff, Continuation.WF.defineC0, Continuation.WF.defineC1]


/-- The Cont family keeps states well-formed. -/
theorem execInstrCont_WF : FamilyWF execInstrCont := by
  intro i next hi hnext
  unfold execInstrCont
  exact execInstrContPushCtr_WF i _ hi <|
    execInstrContPopCtr_WF i _ hi <|
    execInstrContSetContCtr_WF i _ hi <|
    execInstrContSetContArgs_WF i _ hi <|
    execInstrContSetContVarArgs_WF i _ hi <|
    execInstrContSetNumVarArgs_WF i _ hi <|
    execInstrContReturnArgs_WF i _ hi <|
    execInstrContBless_WF i _ hi <|
    execInstrContSaveCtr_WF i _ hi <|
    execInstrContChangeExt_WF i _ hi <|
    execInstrContSameAlt_WF i _ hi <|
    execInstrContSameAltSave_WF i _ hi <|
    execInstrContBoolAnd_WF i _ hi <|
    execInstrContBoolOr_WF i _ hi <|
    execInstrContComposBoth_WF i _ hi <|
    execInstrContCondSel_WF i _ hi <|
    execInstrContAtExit_WF i _ hi <|
    hnext

end TvmLean

import TvmLean.Proofs.WF.Step

/-!
# The Stack family keeps states well-formed

`execInstrStack_WF : FamilyWF execInstrStack`, one theorem per handler of
`TvmLean/Semantics/Exec/Stack/` (the pattern of `Step.lean`): the stack operations only move values
of a well-formed stack. The loops of `BLKPUSH`, `ROLL` and `ROLLREV` (in the VM monad) take the
invariant `VmState.WF`; the stack `REVERSE` computes (a loop in `Id`) takes the invariant that its
values are well-formed (`WF.id_forIn_range`).
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

theorem execInstrStackNop_WF : FamilyWF execInstrStackNop := by
  intro i next hi hnext
  mvcgen [execInstrStackNop, hnext]
  all_goals wf_vc

theorem execInstrStackPushInt_WF : FamilyWF execInstrStackPushInt := by
  intro i next hi hnext
  mvcgen [execInstrStackPushInt, hnext]
  all_goals wf_vc

theorem execInstrStackPushPow2_WF : FamilyWF execInstrStackPushPow2 := by
  intro i next hi hnext
  mvcgen [execInstrStackPushPow2, hnext]
  all_goals wf_vc

theorem execInstrStackPushPow2Dec_WF : FamilyWF execInstrStackPushPow2Dec := by
  intro i next hi hnext
  mvcgen [execInstrStackPushPow2Dec, hnext]
  all_goals wf_vc

theorem execInstrStackPushNegPow2_WF : FamilyWF execInstrStackPushNegPow2 := by
  intro i next hi hnext
  mvcgen [execInstrStackPushNegPow2, hnext]
  all_goals wf_vc

theorem execInstrStackPush_WF : FamilyWF execInstrStackPush := by
  intro i next hi hnext
  mvcgen [execInstrStackPush, hnext]
  all_goals wf_vc

theorem execInstrStackPop_WF : FamilyWF execInstrStackPop := by
  intro i next hi hnext
  mvcgen [execInstrStackPop, hnext]
  all_goals wf_vc

theorem execInstrStackXchg0_WF : FamilyWF execInstrStackXchg0 := by
  intro i next hi hnext
  mvcgen [execInstrStackXchg0, hnext]
  all_goals wf_vc

theorem execInstrStackXchg1_WF : FamilyWF execInstrStackXchg1 := by
  intro i next hi hnext
  mvcgen [execInstrStackXchg1, hnext]
  all_goals wf_vc

theorem execInstrStackXchg_WF : FamilyWF execInstrStackXchg := by
  intro i next hi hnext
  mvcgen [execInstrStackXchg, hnext]
  all_goals wf_vc

theorem execInstrStackXchg2_WF : FamilyWF execInstrStackXchg2 := by
  intro i next hi hnext
  mvcgen [execInstrStackXchg2, hnext]
  all_goals wf_vc

theorem execInstrStackXchg3_WF : FamilyWF execInstrStackXchg3 := by
  intro i next hi hnext
  mvcgen [execInstrStackXchg3, hnext]
  all_goals wf_vc

theorem execInstrStackXcpu_WF : FamilyWF execInstrStackXcpu := by
  intro i next hi hnext
  mvcgen [execInstrStackXcpu, hnext]
  all_goals wf_vc

theorem execInstrStackXc2pu_WF : FamilyWF execInstrStackXc2pu := by
  intro i next hi hnext
  mvcgen [execInstrStackXc2pu, hnext]
  all_goals wf_vc

theorem execInstrStackXcpuxc_WF : FamilyWF execInstrStackXcpuxc := by
  intro i next hi hnext
  mvcgen [execInstrStackXcpuxc, hnext]
  all_goals wf_vc

theorem execInstrStackXcpu2_WF : FamilyWF execInstrStackXcpu2 := by
  intro i next hi hnext
  mvcgen [execInstrStackXcpu2, hnext]
  all_goals wf_vc

theorem execInstrStackPuxc2_WF : FamilyWF execInstrStackPuxc2 := by
  intro i next hi hnext
  mvcgen [execInstrStackPuxc2, hnext]
  all_goals wf_vc

theorem execInstrStackPuxc_WF : FamilyWF execInstrStackPuxc := by
  intro i next hi hnext
  mvcgen [execInstrStackPuxc, hnext]
  all_goals wf_vc

theorem execInstrStackPuxcpu_WF : FamilyWF execInstrStackPuxcpu := by
  intro i next hi hnext
  mvcgen [execInstrStackPuxcpu, hnext]
  all_goals wf_vc

theorem execInstrStackPu2xc_WF : FamilyWF execInstrStackPu2xc := by
  intro i next hi hnext
  mvcgen [execInstrStackPu2xc, hnext]
  all_goals wf_vc

theorem execInstrStackPush2_WF : FamilyWF execInstrStackPush2 := by
  intro i next hi hnext
  mvcgen [execInstrStackPush2, hnext]
  all_goals wf_vc

theorem execInstrStackPush3_WF : FamilyWF execInstrStackPush3 := by
  intro i next hi hnext
  mvcgen [execInstrStackPush3, hnext]
  all_goals wf_vc

theorem execInstrStackBlkSwap_WF : FamilyWF execInstrStackBlkSwap := by
  intro i next hi hnext
  mvcgen [execInstrStackBlkSwap, hnext]
  all_goals wf_vc

theorem execInstrStackBlkPush_WF : FamilyWF execInstrStackBlkPush := by
  intro i next hi hnext
  mvcgen [execInstrStackBlkPush, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

theorem execInstrStackRot_WF : FamilyWF execInstrStackRot := by
  intro i next hi hnext
  mvcgen [execInstrStackRot, hnext]
  all_goals wf_vc

theorem execInstrStackRotRev_WF : FamilyWF execInstrStackRotRev := by
  intro i next hi hnext
  mvcgen [execInstrStackRotRev, hnext]
  all_goals wf_vc

theorem execInstrStackTwoSwap_WF : FamilyWF execInstrStackTwoSwap := by
  intro i next hi hnext
  mvcgen [execInstrStackTwoSwap, hnext]
  all_goals wf_vc

theorem execInstrStackTwoDup_WF : FamilyWF execInstrStackTwoDup := by
  intro i next hi hnext
  mvcgen [execInstrStackTwoDup, hnext]
  all_goals wf_vc

theorem execInstrStackTwoOver_WF : FamilyWF execInstrStackTwoOver := by
  intro i next hi hnext
  mvcgen [execInstrStackTwoOver, hnext]
  all_goals wf_vc

theorem execInstrStackReverse_WF : FamilyWF execInstrStackReverse := by
  intro i next hi hnext
  mvcgen [execInstrStackReverse, hnext]
  all_goals try wf_vc
  -- the stack the loop computes: swaps of elements of the stack
  apply VmState.WF.withStack (by assumption)
  simp (config := { zetaDelta := true }) only [bind_pure]
  apply WF.id_forIn_range (fun a : Stack => ∀ v ∈ a, v.WF) (VmState.WF.stack (by assumption))
  intro _ b hb
  exact WF.forall_mem_set! (WF.forall_mem_set! hb (Value.getElem!_WF hb _) _)
    (Value.getElem!_WF hb _) _

theorem execInstrStackPick_WF : FamilyWF execInstrStackPick := by
  intro i next hi hnext
  mvcgen [execInstrStackPick, hnext]
  all_goals wf_vc

theorem execInstrStackRoll_WF : FamilyWF execInstrStackRoll := by
  intro i next hi hnext
  mvcgen [execInstrStackRoll, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

theorem execInstrStackRollRev_WF : FamilyWF execInstrStackRollRev := by
  intro i next hi hnext
  mvcgen [execInstrStackRollRev, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

theorem execInstrStackBlkSwapX_WF : FamilyWF execInstrStackBlkSwapX := by
  intro i next hi hnext
  mvcgen [execInstrStackBlkSwapX, hnext]
  all_goals wf_vc

theorem execInstrStackReverseX_WF : FamilyWF execInstrStackReverseX := by
  intro i next hi hnext
  mvcgen [execInstrStackReverseX, hnext]
  all_goals wf_vc

theorem execInstrStackDropX_WF : FamilyWF execInstrStackDropX := by
  intro i next hi hnext
  mvcgen [execInstrStackDropX, hnext]
  all_goals wf_vc

theorem execInstrStackTuck_WF : FamilyWF execInstrStackTuck := by
  intro i next hi hnext
  mvcgen [execInstrStackTuck, hnext]
  all_goals wf_vc

theorem execInstrStackXchgX_WF : FamilyWF execInstrStackXchgX := by
  intro i next hi hnext
  mvcgen [execInstrStackXchgX, hnext]
  all_goals wf_vc

theorem execInstrStackDepth_WF : FamilyWF execInstrStackDepth := by
  intro i next hi hnext
  mvcgen [execInstrStackDepth, hnext]
  all_goals wf_vc

theorem execInstrStackChkDepth_WF : FamilyWF execInstrStackChkDepth := by
  intro i next hi hnext
  mvcgen [execInstrStackChkDepth, hnext]
  all_goals wf_vc

theorem execInstrStackOnlyTopX_WF : FamilyWF execInstrStackOnlyTopX := by
  intro i next hi hnext
  mvcgen [execInstrStackOnlyTopX, hnext]
  all_goals wf_vc

theorem execInstrStackOnlyX_WF : FamilyWF execInstrStackOnlyX := by
  intro i next hi hnext
  mvcgen [execInstrStackOnlyX, hnext]
  all_goals wf_vc

theorem execInstrStack_WF : FamilyWF execInstrStack := by
  intro i next hi hnext
  unfold execInstrStack
  exact execInstrStackNop_WF i _ hi <|
    execInstrStackPushInt_WF i _ hi <|
    execInstrStackPushPow2_WF i _ hi <|
    execInstrStackPushPow2Dec_WF i _ hi <|
    execInstrStackPushNegPow2_WF i _ hi <|
    execInstrStackPush_WF i _ hi <|
    execInstrStackPop_WF i _ hi <|
    execInstrStackXchg0_WF i _ hi <|
    execInstrStackXchg1_WF i _ hi <|
    execInstrStackXchg_WF i _ hi <|
    execInstrStackXchg2_WF i _ hi <|
    execInstrStackXchg3_WF i _ hi <|
    execInstrStackXcpu_WF i _ hi <|
    execInstrStackXc2pu_WF i _ hi <|
    execInstrStackXcpuxc_WF i _ hi <|
    execInstrStackXcpu2_WF i _ hi <|
    execInstrStackPuxc2_WF i _ hi <|
    execInstrStackPuxc_WF i _ hi <|
    execInstrStackPuxcpu_WF i _ hi <|
    execInstrStackPu2xc_WF i _ hi <|
    execInstrStackPush2_WF i _ hi <|
    execInstrStackPush3_WF i _ hi <|
    execInstrStackBlkSwap_WF i _ hi <|
    execInstrStackBlkPush_WF i _ hi <|
    execInstrStackRot_WF i _ hi <|
    execInstrStackRotRev_WF i _ hi <|
    execInstrStackTwoSwap_WF i _ hi <|
    execInstrStackTwoDup_WF i _ hi <|
    execInstrStackTwoOver_WF i _ hi <|
    execInstrStackReverse_WF i _ hi <|
    execInstrStackPick_WF i _ hi <|
    execInstrStackRoll_WF i _ hi <|
    execInstrStackRollRev_WF i _ hi <|
    execInstrStackBlkSwapX_WF i _ hi <|
    execInstrStackReverseX_WF i _ hi <|
    execInstrStackDropX_WF i _ hi <|
    execInstrStackTuck_WF i _ hi <|
    execInstrStackXchgX_WF i _ hi <|
    execInstrStackDepth_WF i _ hi <|
    execInstrStackChkDepth_WF i _ hi <|
    execInstrStackOnlyTopX_WF i _ hi <|
    execInstrStackOnlyX_WF i _ hi <|
    hnext

end TvmLean

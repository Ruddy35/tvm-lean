import TvmLean.Proofs.WF.Step

/-!
# The Arith family keeps states well-formed

`execInstrArith_WF : FamilyWF execInstrArith`, one theorem per handler of
`TvmLean/Semantics/Exec/Arith/` (the pattern of `Step.lean`): the arithmetic instructions pop and
push integers. The helpers `popBitsTwos257` and the private `popLongLike` get specifications;
`LESSINT` unfolds its private core (`unfold_private`).
-/

open Std.Do

set_option mvcgen.warning false

-- the equations of the longest handlers (`execInstrArithExt`) are built with the options of the file
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace TvmLean

/-! ## Helpers of the family -/

set_option maxRecDepth 100000 in
@[spec] theorem popBitsTwos257_spec (n : Int) :
    ⦃fun st => ⌜st.WF⌝⦄ popBitsTwos257 n ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  apply VM.triple_of_run
  intro st hst
  unfold popBitsTwos257
  generalize intToBitsTwos n 257 = r
  cases r <;> exact hst

@[spec] theorem popLongLike_spec :
    ⦃fun st => ⌜st.WF⌝⦄ (private% TvmLean.Semantics.Exec.Arith.Ext TvmLean.popLongLike : VM Int)
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Arith.Ext TvmLean.popLongLike
  mvcgen
  all_goals wf_vc

/-! ## The handlers -/

theorem execInstrArithContExt_WF : FamilyWF execInstrArithContExt := by
  intro i next hi hnext
  mvcgen [execInstrArithContExt, hnext]
  all_goals wf_vc

theorem execInstrArithExt_WF : FamilyWF execInstrArithExt := by
  intro i next hi hnext
  unfold execInstrArithExt
  mvcgen [hnext]
  all_goals wf_vc

theorem execInstrArithInc_WF : FamilyWF execInstrArithInc := by
  intro i next hi hnext
  mvcgen [execInstrArithInc, hnext]
  all_goals wf_vc

theorem execInstrArithQinc_WF : FamilyWF execInstrArithQinc := by
  intro i next hi hnext
  mvcgen [execInstrArithQinc, hnext]
  all_goals wf_vc

theorem execInstrArithDec_WF : FamilyWF execInstrArithDec := by
  intro i next hi hnext
  mvcgen [execInstrArithDec, hnext]
  all_goals wf_vc

theorem execInstrArithQdec_WF : FamilyWF execInstrArithQdec := by
  intro i next hi hnext
  mvcgen [execInstrArithQdec, hnext]
  all_goals wf_vc

theorem execInstrArithNegate_WF : FamilyWF execInstrArithNegate := by
  intro i next hi hnext
  mvcgen [execInstrArithNegate, hnext]
  all_goals wf_vc

theorem execInstrArithQnegate_WF : FamilyWF execInstrArithQnegate := by
  intro i next hi hnext
  mvcgen [execInstrArithQnegate, hnext]
  all_goals wf_vc

theorem execInstrArithQpow2_WF : FamilyWF execInstrArithQpow2 := by
  intro i next hi hnext
  mvcgen [execInstrArithQpow2, hnext]
  all_goals wf_vc

theorem execInstrArithAdd_WF : FamilyWF execInstrArithAdd := by
  intro i next hi hnext
  mvcgen [execInstrArithAdd, hnext]
  all_goals wf_vc

theorem execInstrArithQadd_WF : FamilyWF execInstrArithQadd := by
  intro i next hi hnext
  mvcgen [execInstrArithQadd, hnext]
  all_goals wf_vc

theorem execInstrArithAddInt_WF : FamilyWF execInstrArithAddInt := by
  intro i next hi hnext
  mvcgen [execInstrArithAddInt, hnext]
  all_goals wf_vc

theorem execInstrArithSub_WF : FamilyWF execInstrArithSub := by
  intro i next hi hnext
  mvcgen [execInstrArithSub, hnext]
  all_goals wf_vc

theorem execInstrArithQsub_WF : FamilyWF execInstrArithQsub := by
  intro i next hi hnext
  mvcgen [execInstrArithQsub, hnext]
  all_goals wf_vc

theorem execInstrArithQsubr_WF : FamilyWF execInstrArithQsubr := by
  intro i next hi hnext
  mvcgen [execInstrArithQsubr, hnext]
  all_goals wf_vc

theorem execInstrArithSubr_WF : FamilyWF execInstrArithSubr := by
  intro i next hi hnext
  mvcgen [execInstrArithSubr, hnext]
  all_goals wf_vc

theorem execInstrArithMulInt_WF : FamilyWF execInstrArithMulInt := by
  intro i next hi hnext
  mvcgen [execInstrArithMulInt, hnext]
  all_goals wf_vc

theorem execInstrArithMul_WF : FamilyWF execInstrArithMul := by
  intro i next hi hnext
  mvcgen [execInstrArithMul, hnext]
  all_goals wf_vc

theorem execInstrArithQmul_WF : FamilyWF execInstrArithQmul := by
  intro i next hi hnext
  mvcgen [execInstrArithQmul, hnext]
  all_goals wf_vc

theorem execInstrArithMin_WF : FamilyWF execInstrArithMin := by
  intro i next hi hnext
  mvcgen [execInstrArithMin, hnext]
  all_goals wf_vc

theorem execInstrArithMax_WF : FamilyWF execInstrArithMax := by
  intro i next hi hnext
  mvcgen [execInstrArithMax, hnext]
  all_goals wf_vc

theorem execInstrArithQmax_WF : FamilyWF execInstrArithQmax := by
  intro i next hi hnext
  mvcgen [execInstrArithQmax, hnext]
  all_goals wf_vc

theorem execInstrArithMinmax_WF : FamilyWF execInstrArithMinmax := by
  intro i next hi hnext
  mvcgen [execInstrArithMinmax, hnext]
  all_goals wf_vc

theorem execInstrArithAbs_WF : FamilyWF execInstrArithAbs := by
  intro i next hi hnext
  mvcgen [execInstrArithAbs, hnext]
  all_goals wf_vc

theorem execInstrArithBitsize_WF : FamilyWF execInstrArithBitsize := by
  intro i next hi hnext
  mvcgen [execInstrArithBitsize, hnext]
  all_goals wf_vc

theorem execInstrArithUbitsize_WF : FamilyWF execInstrArithUbitsize := by
  intro i next hi hnext
  mvcgen [execInstrArithUbitsize, hnext]
  all_goals wf_vc

theorem execInstrArithMulShrModConst_WF : FamilyWF execInstrArithMulShrModConst := by
  intro i next hi hnext
  mvcgen [execInstrArithMulShrModConst, hnext]
  all_goals wf_vc

theorem execInstrArithDivMod_WF : FamilyWF execInstrArithDivMod := by
  intro i next hi hnext
  mvcgen [execInstrArithDivMod, hnext]
  all_goals wf_vc

theorem execInstrArithMulDivMod_WF : FamilyWF execInstrArithMulDivMod := by
  intro i next hi hnext
  mvcgen [execInstrArithMulDivMod, hnext]
  all_goals wf_vc

theorem execInstrArithLshiftConst_WF : FamilyWF execInstrArithLshiftConst := by
  intro i next hi hnext
  mvcgen [execInstrArithLshiftConst, hnext]
  all_goals wf_vc

theorem execInstrArithRshiftConst_WF : FamilyWF execInstrArithRshiftConst := by
  intro i next hi hnext
  mvcgen [execInstrArithRshiftConst, hnext]
  all_goals wf_vc

theorem execInstrArithLshift_WF : FamilyWF execInstrArithLshift := by
  intro i next hi hnext
  mvcgen [execInstrArithLshift, hnext]
  all_goals wf_vc

theorem execInstrArithRshift_WF : FamilyWF execInstrArithRshift := by
  intro i next hi hnext
  mvcgen [execInstrArithRshift, hnext]
  all_goals wf_vc

theorem execInstrArithEqual_WF : FamilyWF execInstrArithEqual := by
  intro i next hi hnext
  mvcgen [execInstrArithEqual, hnext]
  all_goals wf_vc

theorem execInstrArithNeq_WF : FamilyWF execInstrArithNeq := by
  intro i next hi hnext
  mvcgen [execInstrArithNeq, hnext]
  all_goals wf_vc

theorem execInstrArithAnd_WF : FamilyWF execInstrArithAnd := by
  intro i next hi hnext
  mvcgen [execInstrArithAnd, hnext]
  all_goals wf_vc

theorem execInstrArithOr_WF : FamilyWF execInstrArithOr := by
  intro i next hi hnext
  mvcgen [execInstrArithOr, hnext]
  all_goals wf_vc

theorem execInstrArithXor_WF : FamilyWF execInstrArithXor := by
  intro i next hi hnext
  mvcgen [execInstrArithXor, hnext]
  all_goals wf_vc

theorem execInstrArithNot_WF : FamilyWF execInstrArithNot := by
  intro i next hi hnext
  mvcgen [execInstrArithNot, hnext]
  all_goals wf_vc

theorem execInstrArithSgn_WF : FamilyWF execInstrArithSgn := by
  intro i next hi hnext
  mvcgen [execInstrArithSgn, hnext]
  all_goals wf_vc

theorem execInstrArithLess_WF : FamilyWF execInstrArithLess := by
  intro i next hi hnext
  mvcgen [execInstrArithLess, hnext]
  all_goals wf_vc

theorem execInstrArithLeq_WF : FamilyWF execInstrArithLeq := by
  intro i next hi hnext
  mvcgen [execInstrArithLeq, hnext]
  all_goals wf_vc

theorem execInstrArithGreater_WF : FamilyWF execInstrArithGreater := by
  intro i next hi hnext
  mvcgen [execInstrArithGreater, hnext]
  all_goals wf_vc

theorem execInstrArithGeq_WF : FamilyWF execInstrArithGeq := by
  intro i next hi hnext
  mvcgen [execInstrArithGeq, hnext]
  all_goals wf_vc

theorem execInstrArithCmp_WF : FamilyWF execInstrArithCmp := by
  intro i next hi hnext
  mvcgen [execInstrArithCmp, hnext]
  all_goals wf_vc

theorem execInstrArithLessInt_WF : FamilyWF execInstrArithLessInt := by
  intro i next hi hnext
  unfold execInstrArithLessInt
  unfold_private TvmLean.Semantics.Exec.Arith.LessInt TvmLean.execLessIntCore
  mvcgen [hnext]
  all_goals wf_vc

theorem execInstrArithEqInt_WF : FamilyWF execInstrArithEqInt := by
  intro i next hi hnext
  mvcgen [execInstrArithEqInt, hnext]
  all_goals wf_vc

theorem execInstrArithGtInt_WF : FamilyWF execInstrArithGtInt := by
  intro i next hi hnext
  mvcgen [execInstrArithGtInt, hnext]
  all_goals wf_vc

theorem execInstrArithNeqInt_WF : FamilyWF execInstrArithNeqInt := by
  intro i next hi hnext
  mvcgen [execInstrArithNeqInt, hnext]
  all_goals wf_vc

theorem execInstrArithPushNull_WF : FamilyWF execInstrArithPushNull := by
  intro i next hi hnext
  mvcgen [execInstrArithPushNull, hnext]
  all_goals wf_vc

theorem execInstrArithIsNull_WF : FamilyWF execInstrArithIsNull := by
  intro i next hi hnext
  mvcgen [execInstrArithIsNull, hnext]
  all_goals wf_vc

theorem execInstrArithNullSwapIf_WF : FamilyWF execInstrArithNullSwapIf := by
  intro i next hi hnext
  mvcgen [execInstrArithNullSwapIf, hnext]
  all_goals wf_vc

theorem execInstrArithNullSwapIfNot_WF : FamilyWF execInstrArithNullSwapIfNot := by
  intro i next hi hnext
  mvcgen [execInstrArithNullSwapIfNot, hnext]
  all_goals wf_vc

theorem execInstrArithNullRotrIf_WF : FamilyWF execInstrArithNullRotrIf := by
  intro i next hi hnext
  mvcgen [execInstrArithNullRotrIf, hnext]
  all_goals wf_vc

theorem execInstrArithNullRotrIfNot_WF : FamilyWF execInstrArithNullRotrIfNot := by
  intro i next hi hnext
  mvcgen [execInstrArithNullRotrIfNot, hnext]
  all_goals wf_vc

theorem execInstrArithNullSwapIf2_WF : FamilyWF execInstrArithNullSwapIf2 := by
  intro i next hi hnext
  mvcgen [execInstrArithNullSwapIf2, hnext]
  all_goals wf_vc

theorem execInstrArithNullSwapIfNot2_WF : FamilyWF execInstrArithNullSwapIfNot2 := by
  intro i next hi hnext
  mvcgen [execInstrArithNullSwapIfNot2, hnext]
  all_goals wf_vc

theorem execInstrArithNullRotrIf2_WF : FamilyWF execInstrArithNullRotrIf2 := by
  intro i next hi hnext
  mvcgen [execInstrArithNullRotrIf2, hnext]
  all_goals wf_vc

theorem execInstrArithNullRotrIfNot2_WF : FamilyWF execInstrArithNullRotrIfNot2 := by
  intro i next hi hnext
  mvcgen [execInstrArithNullRotrIfNot2, hnext]
  all_goals wf_vc

theorem execInstrArith_WF : FamilyWF execInstrArith := by
  intro i next hi hnext
  unfold execInstrArith
  exact execInstrArithContExt_WF i _ hi <|
    execInstrArithExt_WF i _ hi <|
    execInstrArithInc_WF i _ hi <|
    execInstrArithQinc_WF i _ hi <|
    execInstrArithDec_WF i _ hi <|
    execInstrArithQdec_WF i _ hi <|
    execInstrArithNegate_WF i _ hi <|
    execInstrArithQnegate_WF i _ hi <|
    execInstrArithQpow2_WF i _ hi <|
    execInstrArithAdd_WF i _ hi <|
    execInstrArithQadd_WF i _ hi <|
    execInstrArithAddInt_WF i _ hi <|
    execInstrArithSub_WF i _ hi <|
    execInstrArithQsub_WF i _ hi <|
    execInstrArithQsubr_WF i _ hi <|
    execInstrArithSubr_WF i _ hi <|
    execInstrArithMulInt_WF i _ hi <|
    execInstrArithMul_WF i _ hi <|
    execInstrArithQmul_WF i _ hi <|
    execInstrArithMin_WF i _ hi <|
    execInstrArithMax_WF i _ hi <|
    execInstrArithQmax_WF i _ hi <|
    execInstrArithMinmax_WF i _ hi <|
    execInstrArithAbs_WF i _ hi <|
    execInstrArithBitsize_WF i _ hi <|
    execInstrArithUbitsize_WF i _ hi <|
    execInstrArithMulShrModConst_WF i _ hi <|
    execInstrArithDivMod_WF i _ hi <|
    execInstrArithMulDivMod_WF i _ hi <|
    execInstrArithLshiftConst_WF i _ hi <|
    execInstrArithRshiftConst_WF i _ hi <|
    execInstrArithLshift_WF i _ hi <|
    execInstrArithRshift_WF i _ hi <|
    execInstrArithEqual_WF i _ hi <|
    execInstrArithNeq_WF i _ hi <|
    execInstrArithAnd_WF i _ hi <|
    execInstrArithOr_WF i _ hi <|
    execInstrArithXor_WF i _ hi <|
    execInstrArithNot_WF i _ hi <|
    execInstrArithSgn_WF i _ hi <|
    execInstrArithLess_WF i _ hi <|
    execInstrArithLeq_WF i _ hi <|
    execInstrArithGreater_WF i _ hi <|
    execInstrArithGeq_WF i _ hi <|
    execInstrArithCmp_WF i _ hi <|
    execInstrArithLessInt_WF i _ hi <|
    execInstrArithEqInt_WF i _ hi <|
    execInstrArithGtInt_WF i _ hi <|
    execInstrArithNeqInt_WF i _ hi <|
    execInstrArithPushNull_WF i _ hi <|
    execInstrArithIsNull_WF i _ hi <|
    execInstrArithNullSwapIf_WF i _ hi <|
    execInstrArithNullSwapIfNot_WF i _ hi <|
    execInstrArithNullRotrIf_WF i _ hi <|
    execInstrArithNullRotrIfNot_WF i _ hi <|
    execInstrArithNullSwapIf2_WF i _ hi <|
    execInstrArithNullSwapIfNot2_WF i _ hi <|
    execInstrArithNullRotrIf2_WF i _ hi <|
    execInstrArithNullRotrIfNot2_WF i _ hi <|
    hnext

end TvmLean

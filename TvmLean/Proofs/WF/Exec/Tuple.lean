import TvmLean.Proofs.WF.Calls

/-!
# The Tuple family keeps states well-formed

`execInstrTuple_WF : FamilyWF execInstrTuple`, one theorem per handler of
`TvmLean/Semantics/Exec/Tuple/` (the pattern of `Step.lean`; `TupleWF`: the operations carry no
cell). The tuple operations only move values of well-formed tuples and stacks. The loops pushing
the elements of a tuple (`UNTUPLE`, `UNPACKFIRST`, `EXPLODE` and their variable forms) take the
invariant `VmState.WF`; the loops of `TUPLE` and `TUPLEVAR` collecting popped values also that
the values collected are well-formed (`WF.not_mem_mk_nil` of `Calls.lean`: `grind` does not see
that the literal empty array has no element).
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

/-- What a handler of `execInstrTuple` owes (its operations carry no cell). -/
def TupleWF (h : TupleInstr → VM Unit → VM Unit) : Prop :=
  ∀ op next, next.KeepsWF → (h op next).KeepsWF

theorem execTupleOpMktuple_WF : TupleWF execTupleOpMktuple := by
  intro op next hnext
  mvcgen [execTupleOpMktuple, hnext] invariants
  · post⟨fun p st => ⌜st.WF ∧ ∀ v ∈ p.2, v.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc [WF.not_mem_mk_nil]

theorem execTupleOpIndex_WF : TupleWF execTupleOpIndex := by
  intro op next hnext
  mvcgen [execTupleOpIndex, hnext]
  all_goals wf_vc

theorem execTupleOpIndex2_WF : TupleWF execTupleOpIndex2 := by
  intro op next hnext
  mvcgen [execTupleOpIndex2, hnext]
  all_goals wf_vc

theorem execTupleOpIndex3_WF : TupleWF execTupleOpIndex3 := by
  intro op next hnext
  mvcgen [execTupleOpIndex3, hnext]
  all_goals wf_vc

theorem execTupleOpUntuple_WF : TupleWF execTupleOpUntuple := by
  intro op next hnext
  mvcgen [execTupleOpUntuple, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

theorem execTupleOpUnpackFirst_WF : TupleWF execTupleOpUnpackFirst := by
  intro op next hnext
  mvcgen [execTupleOpUnpackFirst, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

theorem execTupleOpExplode_WF : TupleWF execTupleOpExplode := by
  intro op next hnext
  mvcgen [execTupleOpExplode, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

theorem execTupleOpSetIndex_WF : TupleWF execTupleOpSetIndex := by
  intro op next hnext
  mvcgen [execTupleOpSetIndex, hnext]
  all_goals wf_vc

theorem execTupleOpIndexQ_WF : TupleWF execTupleOpIndexQ := by
  intro op next hnext
  mvcgen [execTupleOpIndexQ, hnext]
  all_goals wf_vc

theorem execTupleOpSetIndexQ_WF : TupleWF execTupleOpSetIndexQ := by
  intro op next hnext
  mvcgen [execTupleOpSetIndexQ, hnext]
  all_goals wf_vc

theorem execTupleOpMktupleVar_WF : TupleWF execTupleOpMktupleVar := by
  intro op next hnext
  mvcgen [execTupleOpMktupleVar, hnext] invariants
  · post⟨fun p st => ⌜st.WF ∧ ∀ v ∈ p.2, v.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc [WF.not_mem_mk_nil]

theorem execTupleOpIndexVar_WF : TupleWF execTupleOpIndexVar := by
  intro op next hnext
  mvcgen [execTupleOpIndexVar, hnext]
  all_goals wf_vc

theorem execTupleOpUntupleVar_WF : TupleWF execTupleOpUntupleVar := by
  intro op next hnext
  mvcgen [execTupleOpUntupleVar, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

theorem execTupleOpUnpackFirstVar_WF : TupleWF execTupleOpUnpackFirstVar := by
  intro op next hnext
  mvcgen [execTupleOpUnpackFirstVar, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

theorem execTupleOpExplodeVar_WF : TupleWF execTupleOpExplodeVar := by
  intro op next hnext
  mvcgen [execTupleOpExplodeVar, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

theorem execTupleOpSetIndexVar_WF : TupleWF execTupleOpSetIndexVar := by
  intro op next hnext
  mvcgen [execTupleOpSetIndexVar, hnext]
  all_goals wf_vc

theorem execTupleOpIndexVarQ_WF : TupleWF execTupleOpIndexVarQ := by
  intro op next hnext
  mvcgen [execTupleOpIndexVarQ, hnext]
  all_goals wf_vc

theorem execTupleOpSetIndexVarQ_WF : TupleWF execTupleOpSetIndexVarQ := by
  intro op next hnext
  mvcgen [execTupleOpSetIndexVarQ, hnext]
  all_goals wf_vc

theorem execTupleOpTlen_WF : TupleWF execTupleOpTlen := by
  intro op next hnext
  mvcgen [execTupleOpTlen, hnext]
  all_goals wf_vc

theorem execTupleOpQtlen_WF : TupleWF execTupleOpQtlen := by
  intro op next hnext
  mvcgen [execTupleOpQtlen, hnext]
  all_goals wf_vc

theorem execTupleOpIsTuple_WF : TupleWF execTupleOpIsTuple := by
  intro op next hnext
  mvcgen [execTupleOpIsTuple, hnext]
  all_goals wf_vc

theorem execTupleOpLast_WF : TupleWF execTupleOpLast := by
  intro op next hnext
  mvcgen [execTupleOpLast, hnext]
  all_goals wf_vc

theorem execTupleOpTpush_WF : TupleWF execTupleOpTpush := by
  intro op next hnext
  mvcgen [execTupleOpTpush, hnext]
  all_goals wf_vc

theorem execTupleOpTpop_WF : TupleWF execTupleOpTpop := by
  intro op next hnext
  mvcgen [execTupleOpTpop, hnext]
  all_goals wf_vc

theorem execInstrTuple_WF : FamilyWF execInstrTuple := by
  intro i next hi hnext
  unfold execInstrTuple
  split
  · rename_i op
    exact execTupleOpMktuple_WF op _ <|
      execTupleOpIndex_WF op _ <|
      execTupleOpIndex2_WF op _ <|
      execTupleOpIndex3_WF op _ <|
      execTupleOpUntuple_WF op _ <|
      execTupleOpUnpackFirst_WF op _ <|
      execTupleOpExplode_WF op _ <|
      execTupleOpSetIndex_WF op _ <|
      execTupleOpIndexQ_WF op _ <|
      execTupleOpSetIndexQ_WF op _ <|
      execTupleOpMktupleVar_WF op _ <|
      execTupleOpIndexVar_WF op _ <|
      execTupleOpUntupleVar_WF op _ <|
      execTupleOpUnpackFirstVar_WF op _ <|
      execTupleOpExplodeVar_WF op _ <|
      execTupleOpSetIndexVar_WF op _ <|
      execTupleOpIndexVarQ_WF op _ <|
      execTupleOpSetIndexVarQ_WF op _ <|
      execTupleOpTlen_WF op _ <|
      execTupleOpQtlen_WF op _ <|
      execTupleOpIsTuple_WF op _ <|
      execTupleOpLast_WF op _ <|
      execTupleOpTpush_WF op _ <|
      execTupleOpTpop_WF op _ <|
      hnext
  · exact hnext

end TvmLean

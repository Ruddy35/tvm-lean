import TvmLean.Proofs.WF.Calls

/-!
# The Exception family keeps states well-formed

`execInstrException_WF : FamilyWF execInstrException`, one theorem per handler of
`TvmLean/Semantics/Exec/Exception/` (the pattern of `Step.lean`). The throws jump to `c2` with a
well-formed argument (`VM.throwToHandler` with `VmState.WF.throwException(Arg)`, tactic
`wf_throw`). `TRY` and `TRYARGS` (C++ `exec_try`) save `c0`..`c2` in the continuation after them
(`OrdCregs.c012_WF`) and define `c2` and `c0` of the handler (`Continuation.WF.defineC2`, and
`Continuation.WF.defineC0` of `Calls.lean`: a slot already set is kept, an empty one takes a
well-formed continuation).
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

theorem OrdCregs.WF.defineC2Slot {cr : OrdCregs} (h : cr.WF) {c : Continuation} (hc : c.WF) :
    (match cr.c2 with | some _ => cr | none => { cr with c2 := some c }).WF := by
  split
  · exact h
  · rw [OrdCregs.wf_iff] at h ⊢
    obtain ⟨h0, h1, _, h3, h4, h5, h7⟩ := h
    exact ⟨h0, h1, by simp only [Option.some.injEq]; rintro k rfl; exact hc, h3, h4, h5, h7⟩

/-- C++ `define_c2`: a well-formed continuation saved as `c2` of a well-formed one. -/
theorem Continuation.WF.defineC2 {k c : Continuation} (hk : k.WF) (hc : c.WF) :
    (k.defineC2 c).WF := by
  have hf := hk.forceCdata
  unfold Continuation.defineC2
  dsimp only
  split
  · rename_i heq
    rw [heq] at hf
    simp only [Continuation.wf_ordinary] at hf ⊢
    exact ⟨hf.1, hf.2.1, hf.2.2.1.defineC2Slot hc, hf.2.2.2⟩
  · rename_i heq
    rw [heq] at hf
    simp only [Continuation.wf_envelope] at hf ⊢
    exact ⟨hf.1, hf.2.1.defineC2Slot hc, hf.2.2⟩
  · exact hf

/-- The control registers `TRY` saves in the continuation after it (C++ `extract_cc(7)`). -/
theorem OrdCregs.c012_WF {a b c : Continuation} (ha : a.WF) (hb : b.WF) (hc : c.WF) :
    ({ OrdCregs.empty with c0 := some a, c1 := some b, c2 := some c } : OrdCregs).WF := by
  rw [OrdCregs.wf_iff]
  simp [OrdCregs.empty, ha, hb, hc]

/-- The handler `raise` of `VM.throwToHandler` for `THROW` and `THROWARG`. -/
macro "wf_throw" : tactic => `(tactic| first
  | (apply VmState.WF.throwException; assumption)
  | (apply VmState.WF.throwExceptionArg; assumption; wf_vc)
  | wf_vc [Continuation.WF.defineC0, Continuation.WF.defineC2, OrdCregs.c012_WF])

theorem execInstrExceptionThrow_WF : FamilyWF execInstrExceptionThrow := by
  intro i next hi hnext
  mvcgen [execInstrExceptionThrow, hnext]
  all_goals wf_throw

theorem execInstrExceptionThrowIf_WF : FamilyWF execInstrExceptionThrowIf := by
  intro i next hi hnext
  mvcgen [execInstrExceptionThrowIf, hnext]
  all_goals wf_throw

theorem execInstrExceptionThrowIfNot_WF : FamilyWF execInstrExceptionThrowIfNot := by
  intro i next hi hnext
  mvcgen [execInstrExceptionThrowIfNot, hnext]
  all_goals wf_throw

theorem execInstrExceptionThrowArg_WF : FamilyWF execInstrExceptionThrowArg := by
  intro i next hi hnext
  mvcgen [execInstrExceptionThrowArg, hnext]
  all_goals wf_throw

theorem execInstrExceptionThrowArgIf_WF : FamilyWF execInstrExceptionThrowArgIf := by
  intro i next hi hnext
  mvcgen [execInstrExceptionThrowArgIf, hnext]
  all_goals wf_throw

theorem execInstrExceptionThrowArgIfNot_WF : FamilyWF execInstrExceptionThrowArgIfNot := by
  intro i next hi hnext
  mvcgen [execInstrExceptionThrowArgIfNot, hnext]
  all_goals wf_throw

theorem execInstrExceptionThrowAny_WF : FamilyWF execInstrExceptionThrowAny := by
  intro i next hi hnext
  mvcgen [execInstrExceptionThrowAny, hnext]
  all_goals wf_throw

theorem execInstrExceptionTry_WF : FamilyWF execInstrExceptionTry := by
  intro i next hi hnext
  mvcgen [execInstrExceptionTry, hnext]
  all_goals wf_throw

theorem execInstrException_WF : FamilyWF execInstrException := by
  intro i next hi hnext
  unfold execInstrException
  exact execInstrExceptionThrow_WF i _ hi <| execInstrExceptionThrowIf_WF i _ hi <|
    execInstrExceptionThrowIfNot_WF i _ hi <| execInstrExceptionThrowArg_WF i _ hi <|
    execInstrExceptionThrowArgIf_WF i _ hi <| execInstrExceptionThrowArgIfNot_WF i _ hi <|
    execInstrExceptionThrowAny_WF i _ hi <| execInstrExceptionTry_WF i _ hi <| hnext

end TvmLean

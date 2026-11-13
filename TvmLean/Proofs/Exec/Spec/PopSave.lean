import TvmLean.Proofs.Exec.Spec.ContCtr
import TvmLean.Proofs.Exec.Spec.ContReg
import TvmLean.Proofs.Exec.Spec.ContSave

/-!
# Specifications: `POPSAVE`

`POPSAVE c<i>` (C++ `exec_popsave_ctr`, contops.cpp) on the stack `s v`: register `i` read and saved
in `c0` (`Continuation.defineCtr`; kept as it was where `c0` refuses it, the refusal ignored), then
`v` set as register `i` (`VmState.setCtr`):

* `Spec.popSave_c0`: for `c0` itself the saved copy is replaced at once: a continuation `v` becomes
  `c0` (`POP c0`);
* `Spec.popSave_c1` .. `Spec.popSave_c7`: register `i` set to `v` of its type and `c0` saving the old
  register `i` (`Spec.popSaveC0`, computed in a run: `Continuation.defineCtr_quit` of `Spec/ContSave.lean`
  with the lemmas of `Spec/ContMany.lean`);
* `Spec.popSave_any`: for any `i ≠ 0` and any value, as the handler runs it (`VmState.setCtr`, type_chk
  for a value of another type; range_chk for an index that names no register, `VmState.getCtr`).
-/

namespace TvmLean

/-- The saved registers refuse a value only with type_chk. -/
theorem OrdCregs.defineFromValue_error (c : OrdCregs) (i : Nat) (v : Value) (b : Bool) (e : Excno)
    (h : c.defineFromValue i v b = .error e) : e = .typeChk := by
  unfold OrdCregs.defineFromValue at h
  repeat' split at h
  all_goals first | (cases h; done) | (cases h; rfl) | skip

/-- `Continuation.defineCtr` fails only with type_chk. -/
theorem Continuation.defineCtr_error (k : Continuation) (i : Nat) (v : Value) (b : Bool) (e : Excno)
    (h : k.defineCtr i v b = .error e) : e = .typeChk := by
  unfold Continuation.defineCtr at h
  generalize k.forceCdata = k' at h
  simp only at h
  cases k' with
  | ordinary code saved cregs cdata =>
    cases hc : cregs.defineFromValue i v b with
    | error e' =>
      simp only [hc] at h
      cases h
      exact OrdCregs.defineFromValue_error _ _ _ _ _ hc
    | ok c' => simp only [hc] at h; cases h
  | envelope ext cregs cdata =>
    cases hc : cregs.defineFromValue i v b with
    | error e' =>
      simp only [hc] at h
      cases h
      exact OrdCregs.defineFromValue_error _ _ _ _ _ hc
    | ok c' => simp only [hc] at h; cases h
  | _ => cases h

namespace Spec

set_option maxHeartbeats 4000000

/-- `c0` with `old` saved as its register `i`, kept as it was where it refuses (`POPSAVE`). -/
@[vm_run] def popSaveC0 (c0 : Continuation) (i : Nat) (old : Value) : Continuation :=
  match c0.defineCtr i old with
  | .ok k => k
  | .error _ => c0

/-- `POPSAVE c0` on the stack `s k`: `k` becomes `c0`. -/
@[vm_spec] theorem popSave_c0 (st : VmState) (s : Stack) (k : Continuation) (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr (.contExt (.popSave 0))) st =
      (.ok (), { st with stack := s, regs := { st.regs with c0 := k } }) := by
  cases h0 : st.regs.c0.defineCtr 0 (.cont st.regs.c0) with
  | error e =>
    obtain rfl := Continuation.defineCtr_error _ _ _ _ _ h0
    vm_simp [hs, h0, VmState.setCtr]
  | ok k' => vm_simp [hs, h0, VmState.setCtr]

/-- `POPSAVE c1` on the stack `s v`. -/
@[vm_spec] theorem popSave_c1 (st : VmState) (s : Stack) (v : Continuation) (hs : st.stack = s.push (.cont v)) :
    ExceptT.run (execInstr (.contExt (.popSave 1))) st =
      (.ok (), { st with stack := s,
                         regs := { st.regs with c1 := v, c0 := popSaveC0 st.regs.c0 1 (.cont st.regs.c1) } }) := by
  unfold popSaveC0
  cases h0 : st.regs.c0.defineCtr 1 (.cont st.regs.c1) with
  | error e =>
    obtain rfl := Continuation.defineCtr_error _ _ _ _ _ h0
    vm_simp [hs, h0, VmState.setCtr]
  | ok k => vm_simp [hs, h0, VmState.setCtr]

/-- `POPSAVE c2` on the stack `s v`. -/
@[vm_spec] theorem popSave_c2 (st : VmState) (s : Stack) (v : Continuation) (hs : st.stack = s.push (.cont v)) :
    ExceptT.run (execInstr (.contExt (.popSave 2))) st =
      (.ok (), { st with stack := s,
                         regs := { st.regs with c2 := v, c0 := popSaveC0 st.regs.c0 2 (.cont st.regs.c2) } }) := by
  unfold popSaveC0
  cases h0 : st.regs.c0.defineCtr 2 (.cont st.regs.c2) with
  | error e =>
    obtain rfl := Continuation.defineCtr_error _ _ _ _ _ h0
    vm_simp [hs, h0, VmState.setCtr]
  | ok k => vm_simp [hs, h0, VmState.setCtr]

/-- `POPSAVE c3` on the stack `s v`. -/
@[vm_spec] theorem popSave_c3 (st : VmState) (s : Stack) (v : Continuation) (hs : st.stack = s.push (.cont v)) :
    ExceptT.run (execInstr (.contExt (.popSave 3))) st =
      (.ok (), { st with stack := s,
                         regs := { st.regs with c3 := v, c0 := popSaveC0 st.regs.c0 3 (.cont st.regs.c3) } }) := by
  unfold popSaveC0
  cases h0 : st.regs.c0.defineCtr 3 (.cont st.regs.c3) with
  | error e =>
    obtain rfl := Continuation.defineCtr_error _ _ _ _ _ h0
    vm_simp [hs, h0, VmState.setCtr]
  | ok k => vm_simp [hs, h0, VmState.setCtr]

/-- `POPSAVE c4` on the stack `s v`. -/
@[vm_spec] theorem popSave_c4 (st : VmState) (s : Stack) (v : Cell) (hs : st.stack = s.push (.cell v)) :
    ExceptT.run (execInstr (.contExt (.popSave 4))) st =
      (.ok (), { st with stack := s,
                         regs := { st.regs with c4 := v, c0 := popSaveC0 st.regs.c0 4 (.cell st.regs.c4) } }) := by
  unfold popSaveC0
  cases h0 : st.regs.c0.defineCtr 4 (.cell st.regs.c4) with
  | error e =>
    obtain rfl := Continuation.defineCtr_error _ _ _ _ _ h0
    vm_simp [hs, h0, VmState.setCtr]
  | ok k => vm_simp [hs, h0, VmState.setCtr]

/-- `POPSAVE c5` on the stack `s v`. -/
@[vm_spec] theorem popSave_c5 (st : VmState) (s : Stack) (v : Cell) (hs : st.stack = s.push (.cell v)) :
    ExceptT.run (execInstr (.contExt (.popSave 5))) st =
      (.ok (), { st with stack := s,
                         regs := { st.regs with c5 := v, c0 := popSaveC0 st.regs.c0 5 (.cell st.regs.c5) } }) := by
  unfold popSaveC0
  cases h0 : st.regs.c0.defineCtr 5 (.cell st.regs.c5) with
  | error e =>
    obtain rfl := Continuation.defineCtr_error _ _ _ _ _ h0
    vm_simp [hs, h0, VmState.setCtr]
  | ok k => vm_simp [hs, h0, VmState.setCtr]

/-- `POPSAVE c7` on the stack `s v`. -/
@[vm_spec] theorem popSave_c7 (st : VmState) (s : Stack) (v : Array Value) (hs : st.stack = s.push (.tuple v)) :
    ExceptT.run (execInstr (.contExt (.popSave 7))) st =
      (.ok (), { st with stack := s,
                         regs := { st.regs with c7 := v, c0 := popSaveC0 st.regs.c0 7 (.tuple st.regs.c7) } }) := by
  unfold popSaveC0
  cases h0 : st.regs.c0.defineCtr 7 (.tuple st.regs.c7) with
  | error e =>
    obtain rfl := Continuation.defineCtr_error _ _ _ _ _ h0
    vm_simp [hs, h0, VmState.setCtr]
  | ok k => vm_simp [hs, h0, VmState.setCtr]

/-- `POPSAVE c<i>` for `i ≠ 0` on the stack `s v`, any value (not a lemma of the runs: its result
splits on `VmState.setCtr`; they use `popSave_c1` .. `popSave_c7`). -/
theorem popSave_any (st : VmState) (s : Stack) (v : Value) (i : Nat) (hi : i ≠ 0)
    (hs : st.stack = s.push v) :
    ExceptT.run (execInstr (.contExt (.popSave i))) st =
      match st.getCtr i with
      | .error e => (.error e, { st with stack := s })
      | .ok old =>
          match ({ st with stack := s } : VmState).setCtr i v with
          | .ok st1 => (.ok (), { st1 with regs := { st1.regs with c0 := popSaveC0 st.regs.c0 i old } })
          | .error e => (.error e, { st with stack := s }) := by
  cases h : st.getCtr i with
  | error e => vm_simp [hs, h, VmState.getCtr_stack]
  | ok old =>
    unfold popSaveC0
    cases h1 : ({ st with stack := s } : VmState).setCtr i v with
    | error e1 =>
      cases h0 : st.regs.c0.defineCtr i old with
      | error e =>
        obtain rfl := Continuation.defineCtr_error _ _ _ _ _ h0
        vm_simp [hs, h, h0, h1, hi, VmState.getCtr_stack]
      | ok k => vm_simp [hs, h, h0, h1, hi, VmState.getCtr_stack]
    | ok st1 =>
      cases h0 : st.regs.c0.defineCtr i old with
      | error e =>
        obtain rfl := Continuation.defineCtr_error _ _ _ _ _ h0
        vm_simp [hs, h, h0, h1, hi, VmState.getCtr_stack]
      | ok k => vm_simp [hs, h, h0, h1, hi, VmState.getCtr_stack]

end Spec

end TvmLean

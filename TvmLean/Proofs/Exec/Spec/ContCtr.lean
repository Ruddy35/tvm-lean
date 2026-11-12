import TvmLean.Proofs.Exec.Spec.ContMany

/-!
# Specifications: a register saved in a continuation, in `c0`, in `c1`

In the format of `Proofs/Exec/Spec/ContMany.lean` (C++ contops.cpp): the value is saved by
`Continuation.defineCtr` (from version 14 a register the continuation already saves is kept, else
type_chk):

* `SETCONTCTR c<i>` (C++ `exec_setcont_ctr`, `i & 15`) on the stack `s v k`: `v` saved as `c<i>` of
  `k`, which is pushed;
* `SETRETCTR c<i>`, `SETALTCTR c<i>` (C++ `exec_setret_ctr`, `exec_setalt_ctr`) on the stack `s v`:
  `v` saved as `c<i>` of `c0` (of `c1`);
* `SAVEALTCTR c<i>` (C++ `exec_savealt_ctr`): `c<i>` (`null` for an index that names none,
  `VmState.ctrOrNull`) saved as `c<i>` of `c1`; `SAVEBOTHCTR c<i>` (C++ `exec_saveboth_ctr`): `c<i>`
  saved in `c0` and in `c1`, each kept as it was where it is refused; range_chk for an index that
  names no register.
-/

namespace TvmLean

/-- The registers read fail only on an index that names none (range_chk). -/
theorem VmState.getCtr_error (st : VmState) (n : Nat) (e : Excno) (h : st.getCtr n = .error e) : e = .rangeChk := by
  unfold VmState.getCtr at h
  split at h <;> cases h <;> rfl

/-- Register `i`, `null` for an index that names none (what `SAVEALTCTR` saves, C++
`st->get(idx)`). -/
def VmState.ctrOrNull (st : VmState) (i : Nat) : Value :=
  match st.getCtr i with
  | .ok v => v
  | .error _ => .null

namespace Spec

set_option maxHeartbeats 4000000

/-- `SETCONTCTR c<i>` on the stack `s v k`. -/
@[vm_spec] theorem setContCtr (st : VmState) (s : Stack) (v : Value) (k : Continuation) (i : Nat)
    (hs : st.stack = (s.push v).push (.cont k)) :
    ExceptT.run (execInstr (.setContCtr i)) st =
      match k.defineCtr (i &&& 15) v (decide (14 ≤ st.globalVersion)) with
      | .ok k' => (.ok (), { st with stack := s.push (.cont k') })
      | .error e => (.error e, { st with stack := s }) := by
  vm_simp [hs]
  all_goals (generalize k.defineCtr (i &&& 15) v (decide (14 ≤ st.globalVersion)) = r
             rcases r with e | k' <;> vm_simp)

/-- `SETRETCTR c<i>` on the stack `s v`. -/
@[vm_spec] theorem setRetCtr (st : VmState) (s : Stack) (v : Value) (i : Nat) (hs : st.stack = s.push v) :
    ExceptT.run (execInstr (.contExt (.setRetCtr i))) st =
      match st.regs.c0.defineCtr i v (decide (14 ≤ st.globalVersion)) with
      | .ok c0' => (.ok (), { st with stack := s, regs := { st.regs with c0 := c0' } })
      | .error e => (.error e, { st with stack := s }) := by
  vm_simp [hs]
  all_goals (generalize st.regs.c0.defineCtr i v (decide (14 ≤ st.globalVersion)) = r
             rcases r with e | k' <;> vm_simp)

/-- `SETALTCTR c<i>` on the stack `s v`. -/
@[vm_spec] theorem setAltCtr (st : VmState) (s : Stack) (v : Value) (i : Nat) (hs : st.stack = s.push v) :
    ExceptT.run (execInstr (.contExt (.setAltCtr i))) st =
      match st.regs.c1.defineCtr i v (decide (14 ≤ st.globalVersion)) with
      | .ok c1' => (.ok (), { st with stack := s, regs := { st.regs with c1 := c1' } })
      | .error e => (.error e, { st with stack := s }) := by
  vm_simp [hs]
  all_goals (generalize st.regs.c1.defineCtr i v (decide (14 ≤ st.globalVersion)) = r
             rcases r with e | k' <;> vm_simp)

/-- `SAVEALTCTR c<i>`. -/
@[vm_spec] theorem saveAltCtr (st : VmState) (i : Nat) :
    ExceptT.run (execInstr (.contExt (.saveAltCtr i))) st =
      match st.regs.c1.defineCtr i (st.ctrOrNull i) (decide (14 ≤ st.globalVersion)) with
      | .ok c1' => (.ok (), { st with regs := { st.regs with c1 := c1' } })
      | .error e => (.error e, st) := by
  unfold VmState.ctrOrNull
  cases h : st.getCtr i with
  | ok v =>
    vm_simp [h]
    all_goals (generalize st.regs.c1.defineCtr i v (decide (14 ≤ st.globalVersion)) = r
               rcases r with e | k' <;> vm_simp)
  | error e =>
    obtain rfl := VmState.getCtr_error st i e h
    vm_simp [h]
    all_goals (generalize st.regs.c1.defineCtr i .null (decide (14 ≤ st.globalVersion)) = r
               rcases r with e | k' <;> vm_simp)

/-- `SAVEBOTHCTR c<i>`. -/
@[vm_spec] theorem saveBothCtr (st : VmState) (i : Nat) :
    ExceptT.run (execInstr (.contExt (.saveBothCtr i))) st =
      match st.getCtr i with
      | .ok v => (.ok (), { st with regs := { st.regs with
          c0 := match st.regs.c0.defineCtr i v with | .ok k => k | .error _ => st.regs.c0,
          c1 := match st.regs.c1.defineCtr i v with | .ok k => k | .error _ => st.regs.c1 } })
      | .error e => (.error e, st) := by
  cases h : st.getCtr i with
  | error e => vm_simp [h]
  | ok v =>
    cases h0 : st.regs.c0.defineCtr i v <;> cases h1 : st.regs.c1.defineCtr i v <;> vm_simp [h, h0, h1]

end Spec

end TvmLean

import TvmLean.Proofs.Exec.Spec.CallArgs
import TvmLean.Proofs.Exec.Spec.LoopBrk

/-!
# Specifications: `CALLCC`, `CALLCCARGS`, `TRYARGS`, `BLESSARGS`

The forms of `CALLCCVARARGS`, `TRY` and `BLESSVARARGS` with their counts in the opcode (C++
contops.cpp), written as the model's handlers run them:

* `CALLCC` (C++ `exec_callcc`) on the stack `s k` while running `code`: the rest of the code saving
  `c0` and `c1` (`extract_cc(3)`, `VM.run_extractCc_3`) pushed, then the jump to `k`;
* `CALLCCARGS p,r` (C++ `exec_callcc_args`): `callccVarArgsTail p r` (`Spec.callccVarArgs`);
* `TRYARGS p,r` (C++ `exec_try_args`) on the stack `s c h` while running `code`: as `TRY`
  (`Spec.try_`), the stack under the top `p` values kept in the closure data of the continuation
  after the `TRY` (with `r` values returned), the top `p` the stack of the body, its depth charged;
* `BLESSARGS copy,more` (C++ `exec_bless_args`): `copy ≤ 15`, `more` in `-1..14` (range_chk, which
  the opcode never gives), then as `BLESSVARARGS` (`VM.blessArgsCommon`).
-/

namespace TvmLean.Spec

set_option maxHeartbeats 4000000 in
/-- `CALLCC` on the stack `s k` while running `code`. -/
@[vm_spec] theorem callcc (st : VmState) (s : Stack) (k : Continuation) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr .callcc) st =
      ExceptT.run (VM.jump k) { st with
        stack := s.push (.cont (.ordinary code (.quit 0)
          { OrdCregs.empty with c0 := some st.regs.c0, c1 := some st.regs.c1 } OrdCdata.empty)),
        regs := { st.regs with c0 := .quit 0, c1 := .quit 1 } } := by
  vm_simp [hs, hcc]

set_option maxHeartbeats 4000000 in
/-- `CALLCCARGS p,r`: what `CALLCCVARARGS` runs after its counts, with `p` and `r`. -/
@[vm_spec] theorem callccArgs (st : VmState) (p : Nat) (r : Int) :
    ExceptT.run (execInstr (.callccArgs p r)) st = ExceptT.run (callccVarArgsTail (Int.ofNat p) r) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, callccVarArgsTail, Int.ofNat_eq_coe, Int.natCast_nonneg,
    decide_true, if_true, Int.toNat_natCast]

set_option maxHeartbeats 4000000 in
/-- `TRYARGS p,r` on the stack `s c h` while running `code`; stk_und if `s` has fewer than `p`
values. -/
@[vm_spec] theorem tryArgs (st : VmState) (s : Stack) (c h : Continuation) (p r : Nat) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata)
    (hs : st.stack = (s.push (.cont c)).push (.cont h)) (hcc : st.cc = .ordinary code saved cregs cdata) :
    ExceptT.run (execInstr (.tryArgs p r)) st =
      if p ≤ s.size then
        (.ok (), { ({ st with stack := s.extract (s.size - p) s.size }.consumeStackGas p) with
          regs := { st.regs with
            c0 := .ordinary code (.quit 0)
              { OrdCregs.empty with c0 := some st.regs.c0, c1 := some st.regs.c1, c2 := some st.regs.c2 }
              { stack := s.take (s.size - p), nargs := Int.ofNat r }
            c1 := .quit 1
            c2 := (h.defineC2 st.regs.c2).defineC0 (.ordinary code (.quit 0)
              { OrdCregs.empty with c0 := some st.regs.c0, c1 := some st.regs.c1, c2 := some st.regs.c2 }
              { stack := s.take (s.size - p), nargs := Int.ofNat r }) }
          cc := c })
      else (.error .stkUnd, st) := by
  by_cases h4 : p ≤ s.size
  · have h4' : ¬ s.size + 2 < p + 2 := by omega
    have h5 : (s.extract (s.size - p) s.size).size = p := by
      simp only [Array.size_extract]; omega
    vm_simp [hs, hcc, h4, h4', h5, VmState.consumeStackGas, VmState.consumeGas]
  · have h4' : s.size + 2 < p + 2 := by omega
    vm_simp [hs, h4, h4']

set_option maxHeartbeats 4000000 in
/-- `BLESSARGS copy,more` on the stack `s cs`: the slice `cs` becomes an ordinary continuation whose
closure data are the top `copy` values of `s` (their depth charged) and `more`; stk_und (the stack
as it was) if `s` has fewer. -/
@[vm_spec] theorem blessArgs (st : VmState) (s : Stack) (cs : Slice) (copy : Nat) (more : Int)
    (hs : st.stack = s.push (.slice cs)) :
    ExceptT.run (execInstr (.blessArgs copy more)) st =
      if 15 < copy then (.error .rangeChk, st)
      else if more < -1 ∨ 14 < more then (.error .rangeChk, st)
      else if copy ≤ s.size then
        (.ok (), { ({ st with stack := s.take (s.size - copy) }.consumeStackGas copy) with
          stack := (s.take (s.size - copy)).push (.cont (.ordinary cs (.quit 0) OrdCregs.empty
            { stack := s.extract (s.size - copy) s.size, nargs := more })) })
      else (.error .stkUnd, st) := by
  -- the conditions on the arguments decided before `vm_simp` (whose contextual `simp` loops on a
  -- branch assuming a false literal)
  by_cases h1 : 15 < copy
  · vm_simp [h1]
  · have h1' : ¬ copy > 15 := h1
    by_cases h2 : more < -1 ∨ 14 < more
    · have h2' : more < -1 ∨ more > 14 := h2
      simp only [h1, h2, if_true, if_false]
      simp only [TvmLean.Exec.reduceExecInstrRun, h1', h2', decide_true, if_true, if_false]
      vm_simp
    · have h2' : ¬ (more < -1 ∨ more > 14) := h2
      have h3 : ¬ (more < -1 ∨ 255 < more) := by omega
      simp only [h1, h2, if_false]
      simp only [TvmLean.Exec.reduceExecInstrRun, h1', h2', decide_false, Bool.false_eq_true, if_false]
      vm_simp [hs, h3, VM.blessArgsCommon, VmState.consumeStackGas, VmState.consumeGas]
      by_cases h4 : copy ≤ s.size
      · have h4' : ¬ s.size + 1 < copy + 1 := by omega
        have h5 : (s.extract (s.size - copy) s.size).size = copy := by
          simp only [Array.size_extract]; omega
        simp only [h4, h4', h5, if_true, if_false]
      · have h4' : s.size + 1 < copy + 1 := by omega
        simp only [h4, h4', if_true, if_false]

end TvmLean.Spec

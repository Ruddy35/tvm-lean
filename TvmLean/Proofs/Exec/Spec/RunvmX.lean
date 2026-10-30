import TvmLean.Proofs.Exec.Spec.Runvm

/-!
# Specification: `RUNVMX`

`RUNVMX` (C++ `exec_runvmx`, contops.cpp) takes the mode of `RUNVM` from the stack (`0..4095`,
range_chk else) and runs as `RUNVM mode` (`runChildVm`, the depth of the child's instructions read
from the gas before the mode is popped). In a plain mode (`Runvm.Plain`: no argument popped but the
code and the values) it is `Runvm.run` (TvmLean/Proofs/Exec/Spec/Runvm.lean), the child's run a term.
-/

namespace TvmLean

/-- `RUNVMX` pops its mode, then runs as `RUNVM` with it (the dispatch of `execInstr`). -/
theorem execInstr_runvmx (st : VmState) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      VM.bindRes (ExceptT.run (popNatUpToSigned 4095) st) (fun mode => do
        let st' ← get
        let st'' ← runChildVm (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1)) st' mode
        set st'') := by
  simp only [TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok]

/-- `VM.popNatUpTo max` on a stack with an integer on top: range_chk if it is negative or above
`max`. -/
theorem Runvm.run_popNatUpTo_of (st : VmState) (t : Stack) (m : Int) (max : Nat)
    (h : st.stack = t.push (.int (.num m))) :
    ExceptT.run (VM.popNatUpTo max) st =
      if m < 0 then (.error .rangeChk, { st with stack := t })
      else if m.toNat > max then (.error .rangeChk, { st with stack := t })
      else (.ok m.toNat, { st with stack := t }) := by
  unfold VM.popNatUpTo
  rw [VM.run_bind, Runvm.run_popInt_of _ _ _ h, VM.bindRes_ok]
  by_cases h1 : m < 0
  · simp [h1, VM.run_throw]
  · by_cases h2 : m.toNat > max
    · simp [h1, h2, VM.run_throw]
    · simp [h1, h2]
      rfl

namespace Spec

set_option maxHeartbeats 4000000 in
/-- **`RUNVMX`** (C++ `exec_runvmx`) on the stack `s n code mode`, the mode in a plain mode of
`RUNVM` (`Runvm.Plain`): range_chk for a mode out of `0..4095`, else `Runvm.run`, the child run on
the code and the top `n` values of `s`. -/
@[vm_spec] theorem runvmx (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (hm : Runvm.Plain m.toNat)
    (hs : st.stack = ((s.push (.int (.num n))).push (.slice code)).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      if m < 0 then (.error .rangeChk, { st with stack := (s.push (.int (.num n))).push (.slice code) })
      else if 4095 < m.toNat then
        (.error .rangeChk, { st with stack := (s.push (.int (.num n))).push (.slice code) })
      else VM.bindRes (Runvm.run (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
          { st with stack := (s.push (.int (.num n))).push (.slice code) } s n code m.toNat)
          (fun st' => set st') := by
  rw [execInstr_runvmx, popNatUpToSigned, Runvm.run_popNatUpTo_of st _ m 4095 hs]
  by_cases h1 : m < 0
  · rw [if_pos h1, if_pos h1]; rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : 4095 < m.toNat
    · rw [if_pos (show m.toNat > 4095 from h2), if_pos h2]; rfl
    · rw [if_neg (show ¬ m.toNat > 4095 from h2), if_neg h2, VM.bindRes_ok, VM.run_bind, VM.run_get,
        VM.bindRes_ok, VM.run_bind, runChildVm_plain _ _ s n code _ hm rfl]

end Spec

end TvmLean

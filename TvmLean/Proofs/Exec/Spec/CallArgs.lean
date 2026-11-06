import TvmLean.Proofs.Exec.Spec.VarArgs

/-!
# Specifications: counts in the opcode (`CALLXARGS`, `JMPXARGS`, `RETARGS`) and `CALLCCVARARGS`

The calls, jumps and returns with a number of arguments or results, written as the model's handlers
run them; the call, jump or return itself is the model's (`VM.call`, `VM.jump`, `VM.ret`), which
the lemmas of `vm_run` on calls and jumps take on for the continuations they cover (as
`Spec.callxVarArgs`, `Spec.retVarArgs` of TvmLean/Proofs/Exec/Spec/VarArgs.lean):

* `CALLXARGS p,r` (C++ `exec_callx_args`, `exec_callx_args_p`, contops.cpp: `r = -1` for the second
  form) on the stack `s k`: `VM.call k p r` from the stack `s`;
* `JMPXARGS p` (C++ `exec_jmpx_args`): `VM.jump k p` from the stack `s`;
* `RETARGS n` (C++ `exec_ret_args`): `VM.ret (n & 15)`;
* `CALLCCVARARGS` (C++ `exec_callcc_varargs`) on the stack `s k p r`: the counts in `-1..254`
  (range_chk), then the call of `k` with the current continuation (`VM.extractCc 3 p r`) pushed.
-/

namespace TvmLean

namespace Spec

set_option maxHeartbeats 4000000 in
/-- `CALLXARGS p,r` on the stack `s k`: the call of `k` with `p` arguments and `r` results. -/
@[vm_spec] theorem callxArgs (st : VmState) (s : Stack) (k : Continuation) (p : Nat) (r : Int)
    (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr (.callxArgs p r)) st = ExceptT.run (VM.call k (Int.ofNat p) r) { st with stack := s } := by
  vm_simp [hs]

set_option maxHeartbeats 4000000 in
/-- `JMPXARGS p` on the stack `s k`: the jump to `k` with `p` arguments. -/
@[vm_spec] theorem jmpxArgs (st : VmState) (s : Stack) (k : Continuation) (p : Nat)
    (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr (.jmpxArgs p)) st = ExceptT.run (VM.jump k (Int.ofNat p)) { st with stack := s } := by
  vm_simp [hs]

/-- `RETARGS n`: the return with `n & 15` values. -/
@[vm_spec] theorem retArgs (st : VmState) (n : Nat) :
    ExceptT.run (execInstr (.retArgs n)) st = ExceptT.run (VM.ret (Int.ofNat (n &&& 0xf))) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]

/-- What `CALLCCVARARGS` runs after its counts: the call of `k` with `p` arguments and `r` results
and the current continuation pushed (`execInstrFlowCallcc`). -/
def callccVarArgsTail (p r : Int) : VM Unit := do
  let need : Nat := if decide (p ≥ 0) then p.toNat + 1 else 0
  VM.checkUnderflow need
  let cont ← VM.popCont
  let cc ← VM.extractCc 3 p r
  VM.push (.cont cc)
  VM.jump cont

set_option maxHeartbeats 8000000 in
/-- `CALLCCVARARGS` on the stack `s k p r`: both counts in `-1..254` (range_chk), then
`callccVarArgsTail p r` from the stack `s k`. -/
@[vm_spec] theorem callccVarArgs (st : VmState) (s : Stack) (k : Value) (p r : Int)
    (hs : st.stack = ((s.push k).push (.int (.num p))).push (.int (.num r))) :
    ExceptT.run (execInstr .callccVarArgs) st =
      if r < -1 ∨ r > 254 then (.error .rangeChk, { st with stack := (s.push k).push (.int (.num p)) })
      else if p < -1 ∨ p > 254 then (.error .rangeChk, { st with stack := s.push k })
      else ExceptT.run (callccVarArgsTail p r) { st with stack := s.push k } := by
  vm_simp [hs, callccVarArgsTail]

end Spec

end TvmLean

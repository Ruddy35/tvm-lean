import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: the control registers other than `c4`

`PUSH cN` and `POP cN` (C++ `exec_push_ctr`, `exec_pop_ctr`, contops.cpp) for the continuations
`c0`–`c3`, the action list `c5` and the environment `c7`, in the format of
`Proofs/Exec/Spec/Stack.lean` (`c4`: `Spec.pushRoot`, `Spec.popRoot`,
TvmLean/Proofs/Exec/Spec/TonEnv.lean). A value of the wrong type raises type_chk; these lemmas take
the value of the right type on top of the stack.
-/

namespace TvmLean.Spec

/-- `PUSH c0` (C++ `exec_push_ctr`): `c0` is pushed. -/
@[vm_spec] theorem pushCtr0 (st : VmState) :
    ExceptT.run (execInstr (.pushCtr 0)) st = (.ok (), { st with stack := st.stack.push (.cont st.regs.c0) }) := by
  vm_simp [VmState.getCtr]

/-- `PUSH c1`. -/
@[vm_spec] theorem pushCtr1 (st : VmState) :
    ExceptT.run (execInstr (.pushCtr 1)) st = (.ok (), { st with stack := st.stack.push (.cont st.regs.c1) }) := by
  vm_simp [VmState.getCtr]

/-- `PUSH c2`. -/
@[vm_spec] theorem pushCtr2 (st : VmState) :
    ExceptT.run (execInstr (.pushCtr 2)) st = (.ok (), { st with stack := st.stack.push (.cont st.regs.c2) }) := by
  vm_simp [VmState.getCtr]

/-- `PUSH c3`. -/
@[vm_spec] theorem pushCtr3 (st : VmState) :
    ExceptT.run (execInstr (.pushCtr 3)) st = (.ok (), { st with stack := st.stack.push (.cont st.regs.c3) }) := by
  vm_simp [VmState.getCtr]

/-- `PUSH c5`: the action list is pushed. -/
@[vm_spec] theorem pushCtr5 (st : VmState) :
    ExceptT.run (execInstr (.pushCtr 5)) st = (.ok (), { st with stack := st.stack.push (.cell st.regs.c5) }) := by
  vm_simp [VmState.getCtr]

/-- `PUSH c7`: the environment tuple is pushed. -/
@[vm_spec] theorem pushCtr7 (st : VmState) :
    ExceptT.run (execInstr (.pushCtr 7)) st = (.ok (), { st with stack := st.stack.push (.tuple st.regs.c7) }) := by
  vm_simp [VmState.getCtr]

/-- `POP c0` (C++ `exec_pop_ctr`): the continuation on top becomes `c0`. -/
@[vm_spec] theorem popCtr0 (st : VmState) (s : Stack) (k : Continuation) (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr (.popCtr 0)) st = (.ok (), { st with stack := s, regs := { st.regs with c0 := k } }) := by
  vm_simp [hs, VmState.setCtr]

/-- `POP c1`. -/
@[vm_spec] theorem popCtr1 (st : VmState) (s : Stack) (k : Continuation) (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr (.popCtr 1)) st = (.ok (), { st with stack := s, regs := { st.regs with c1 := k } }) := by
  vm_simp [hs, VmState.setCtr]

/-- `POP c2`. -/
@[vm_spec] theorem popCtr2 (st : VmState) (s : Stack) (k : Continuation) (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr (.popCtr 2)) st = (.ok (), { st with stack := s, regs := { st.regs with c2 := k } }) := by
  vm_simp [hs, VmState.setCtr]

/-- `POP c3`. -/
@[vm_spec] theorem popCtr3 (st : VmState) (s : Stack) (k : Continuation) (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr (.popCtr 3)) st = (.ok (), { st with stack := s, regs := { st.regs with c3 := k } }) := by
  vm_simp [hs, VmState.setCtr]

/-- `POP c5`: the cell on top becomes the action list. -/
@[vm_spec] theorem popCtr5 (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr (.popCtr 5)) st = (.ok (), { st with stack := s, regs := { st.regs with c5 := c } }) := by
  vm_simp [hs, VmState.setCtr]

/-- `POP c7`: the tuple on top becomes the environment. -/
@[vm_spec] theorem popCtr7 (st : VmState) (s : Stack) (t : Array Value) (hs : st.stack = s.push (.tuple t)) :
    ExceptT.run (execInstr (.popCtr 7)) st = (.ok (), { st with stack := s, regs := { st.regs with c7 := t } }) := by
  vm_simp [hs, VmState.setCtr]

end TvmLean.Spec

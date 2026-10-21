import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: registers and the blockchain environment

In the format of `Proofs/Exec/Spec/Stack.lean`: the persistent data `c4` (`PUSHROOT`, `POPROOT`),
`ACCEPT`, and the parameters of `c7` (`NOW`).
-/

namespace TvmLean.Spec

/-- `PUSHROOT` = `PUSH c4` (C++ `exec_push_ctr`): the data cell is pushed. -/
@[vm_spec] theorem pushRoot (st : VmState) :
    ExceptT.run (execInstr (.pushCtr 4)) st = (.ok (), { st with stack := st.stack.push (.cell st.regs.c4) }) := by
  vm_simp [VmState.getCtr]

/-- `POPROOT` = `POP c4` (C++ `exec_pop_ctr`): the cell on top becomes the data. -/
@[vm_spec] theorem popRoot (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr (.popCtr 4)) st =
      (.ok (), { st with stack := s, regs := { st.regs with c4 := c } }) := by
  vm_simp [hs, VmState.setCtr]

/-- `ACCEPT` (C++ `exec_accept`): the gas limit becomes the maximum (`GasLimits.changeLimit` to
`GasLimits.infty`, which sets the gas credit to 0). -/
@[vm_spec] theorem accept (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .accept)) st =
      (.ok (), { st with gas := st.gas.changeLimit GasLimits.infty }) := by
  vm_simp

/-- `NOW` = `GETPARAM 3` (C++ `exec_get_param`) when `c7` is the parameters tuple (as the compute
phase makes it, `SmartContractInfo.toC7`): its entry 3 is pushed. -/
@[vm_spec] theorem now (st : VmState) (params : Array Value) (hc7 : st.regs.c7 = #[.tuple params]) (hp : 3 < params.size) :
    ExceptT.run (execInstr (.tonEnvOp .now)) st = (.ok (), { st with stack := st.stack.push params[3]! }) := by
  vm_simp [hc7, hp]
  done

end TvmLean.Spec

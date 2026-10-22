import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: registers and the blockchain environment

In the format of `Proofs/Exec/Spec/Stack.lean`: the persistent data `c4` (`PUSHROOT`, `POPROOT`),
`ACCEPT`, and the parameters of `c7` (`NOW`, `BALANCE`, `MYADDR`, `GETPARAM i` and its other
aliases). A parameter is entry `i` of the tuple `c7[0]` (`SmartContractInfo.params`); the
specifications take that tuple as a hypothesis on `c7` (`c7[0]! = .tuple params`, which
`vm_run` finds among the hypotheses of the goal), so `c7` itself may stay unknown.
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

/-- The gas limits after `ACCEPT` (`GasLimits.changeLimit` to `GasLimits.infty`) when the maximum
is at most `GasLimits.infty` = 2^63 - 1 (it is a 64-bit amount): limit and base become the maximum, the credit
0, and the gas left grows by the difference of the bases. -/
@[vm_run] theorem _root_.TvmLean.GasLimits.changeLimit_infty (g : GasLimits) (h : g.gasMax ≤ 9223372036854775807) :
    g.changeLimit GasLimits.infty =
      { g with gasCredit := 0, gasLimit := g.gasMax, gasRemaining := g.gasRemaining + (g.gasMax - g.gasBase),
               gasBase := g.gasMax } := by
  have hi : GasLimits.infty = 9223372036854775807 := by decide
  have h0 : ¬ (GasLimits.infty < 0) := by rw [hi]; decide
  have hl : (if GasLimits.infty > g.gasMax then g.gasMax else GasLimits.infty) = g.gasMax := by
    rw [hi]; split <;> omega
  simp only [GasLimits.changeLimit, GasLimits.changeBase, h0, if_false, hl]

/-- `NOW` = `GETPARAM 3` (C++ `exec_get_param`) when `c7` is the parameters tuple (as the compute
phase makes it, `SmartContractInfo.toC7`): its entry 3 is pushed. -/
@[vm_spec] theorem now (st : VmState) (params : Array Value) (hc7 : st.regs.c7 = #[.tuple params]) (hp : 3 < params.size) :
    ExceptT.run (execInstr (.tonEnvOp .now)) st = (.ok (), { st with stack := st.stack.push params[3]! }) := by
  vm_simp [hc7, hp]
  done

/-- `GETPARAM i` (C++ `exec_get_param`) when `c7[0]` is the tuple `params` of more than `i`
entries: entry `i` is pushed. -/
@[vm_spec] theorem getParam (st : VmState) (i : Nat) (params : Array Value) (h0 : 0 < st.regs.c7.size)
    (hc7 : st.regs.c7[0]! = .tuple params) (hp : i < params.size) :
    ExceptT.run (execInstr (.tonEnvOp (.getParam i))) st = (.ok (), { st with stack := st.stack.push params[i]! }) := by
  vm_simp [h0, hc7, hp]

/-- `NOW` = `GETPARAM 3` with `c7[0]` a tuple `params` (any `c7`). -/
@[vm_spec] theorem now' (st : VmState) (params : Array Value) (h0 : 0 < st.regs.c7.size)
    (hc7 : st.regs.c7[0]! = .tuple params) (hp : 3 < params.size) :
    ExceptT.run (execInstr (.tonEnvOp .now)) st = (.ok (), { st with stack := st.stack.push params[3]! }) := by
  vm_simp [h0, hc7, hp]

/-- `BALANCE` = `GETPARAM 7` (the pair `[grams, extra]`). -/
@[vm_spec] theorem balance (st : VmState) (params : Array Value) (h0 : 0 < st.regs.c7.size)
    (hc7 : st.regs.c7[0]! = .tuple params) (hp : 7 < params.size) :
    ExceptT.run (execInstr (.tonEnvOp .balance)) st = (.ok (), { st with stack := st.stack.push params[7]! }) := by
  vm_simp [h0, hc7, hp]

/-- The parameter aliases of `GETPARAM` (C++ `exec_get_var_param` callers): `BLOCKLT` 4, `LTIME` 5,
`RANDSEED` 6, `MYADDR` 8, `CONFIGROOT` 9, `MYCODE` 10, `INCOMINGVALUE` 11, `STORAGEFEES` 12. -/
theorem pushC7Param (st : VmState) (i : Nat) (params : Array Value) (h0 : 0 < st.regs.c7.size)
    (hc7 : st.regs.c7[0]! = .tuple params) (hp : i < params.size) :
    ExceptT.run (VM.pushC7Param i) st = (.ok (), { st with stack := st.stack.push params[i]! }) := by
  vm_simp [VM.pushC7Param, h0, hc7, hp]

/-- `MYADDR` = `GETPARAM 8`. -/
@[vm_spec] theorem myAddr (st : VmState) (params : Array Value) (h0 : 0 < st.regs.c7.size)
    (hc7 : st.regs.c7[0]! = .tuple params) (hp : 8 < params.size) :
    ExceptT.run (execInstr (.tonEnvOp .myAddr)) st = (.ok (), { st with stack := st.stack.push params[8]! }) := by
  vm_simp [pushC7Param st 8 params h0 hc7 hp]

/-- `LTIME` = `GETPARAM 5`. -/
@[vm_spec] theorem lTime (st : VmState) (params : Array Value) (h0 : 0 < st.regs.c7.size)
    (hc7 : st.regs.c7[0]! = .tuple params) (hp : 5 < params.size) :
    ExceptT.run (execInstr (.tonEnvOp .lTime)) st = (.ok (), { st with stack := st.stack.push params[5]! }) := by
  vm_simp [pushC7Param st 5 params h0 hc7 hp]

/-- `BLOCKLT` = `GETPARAM 4`. -/
@[vm_spec] theorem blockLt (st : VmState) (params : Array Value) (h0 : 0 < st.regs.c7.size)
    (hc7 : st.regs.c7[0]! = .tuple params) (hp : 4 < params.size) :
    ExceptT.run (execInstr (.tonEnvOp .blockLt)) st = (.ok (), { st with stack := st.stack.push params[4]! }) := by
  vm_simp [pushC7Param st 4 params h0 hc7 hp]

/-- `MYCODE` = `GETPARAM 10`. -/
@[vm_spec] theorem myCode (st : VmState) (params : Array Value) (h0 : 0 < st.regs.c7.size)
    (hc7 : st.regs.c7[0]! = .tuple params) (hp : 10 < params.size) :
    ExceptT.run (execInstr (.tonEnvOp .myCode)) st = (.ok (), { st with stack := st.stack.push params[10]! }) := by
  vm_simp [pushC7Param st 10 params h0 hc7 hp]

/-- `INCOMINGVALUE` = `GETPARAM 11`. -/
@[vm_spec] theorem incomingValue (st : VmState) (params : Array Value) (h0 : 0 < st.regs.c7.size)
    (hc7 : st.regs.c7[0]! = .tuple params) (hp : 11 < params.size) :
    ExceptT.run (execInstr (.tonEnvOp .incomingValue)) st = (.ok (), { st with stack := st.stack.push params[11]! }) := by
  vm_simp [pushC7Param st 11 params h0 hc7 hp]

/-- `COMMIT` (C++ `exec_commit`): `c4` and `c5` become the committed state if they are at most
`max_data_depth` deep and of level 0, else cell_ov (`VmState.tryCommit`). -/
@[vm_spec] theorem commit (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .commit)) st =
      if (st.tryCommit).1 then (.ok (), (st.tryCommit).2) else (.error .cellOv, st) := by
  vm_simp

end TvmLean.Spec

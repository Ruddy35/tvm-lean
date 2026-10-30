import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: `GETGLOB`, `SETGLOB`, `SETGASLIMIT`

In the format of `Proofs/Exec/Spec/Stack.lean`:

* `GETGLOB k` (C++ `exec_get_global`, tonops.cpp): the entry `k` of `c7`, null past its end;
* `SETGLOB k` (C++ `exec_set_global`): the entry `k` of `c7` set to the value popped, `c7`
  extended with nulls if it is shorter (`tupleExtendSetIndex`; nothing for a null past its end),
  the new tuple's entries charged (`VmState.consumeTupleGas`);
* `SETGASLIMIT` (C++ `exec_set_gas_limit`, `exec_set_gas_generic`): the limit `n` (`2^63` and
  above unlimited, `GasLimits.infty`; 0 if `n ≤ 0`); below the gas consumed out of gas, else
  `GasLimits.changeLimit`.
-/

namespace TvmLean.Spec

/-- `GETGLOB k` (C++ `exec_get_global`): `c7[k]`, null if `c7` is shorter. -/
@[vm_spec] theorem getGlob (st : VmState) (idx : Nat) :
    ExceptT.run (execInstr (.tonEnvOp (.getGlob idx))) st =
      if idx < st.regs.c7.size then (.ok (), { st with stack := st.stack.push st.regs.c7[idx]! })
      else (.ok (), { st with stack := st.stack.push .null }) := by
  by_cases h : idx < st.regs.c7.size <;> vm_simp [h]

/-- `SETGLOB k` (C++ `exec_set_global`) on the stack `s x`: `c7` with its entry `k` set to `x`
(`tupleExtendSetIndex`: the tuple and the number of entries to charge). -/
@[vm_spec] theorem setGlob (st : VmState) (s : Stack) (x : Value) (idx : Nat) (hs : st.stack = s.push x) :
    ExceptT.run (execInstr (.tonEnvOp (.setGlob idx))) st =
      (.ok (), if 0 < (tupleExtendSetIndex st.regs.c7 idx x).2 then
          { st with stack := s, regs := { st.regs with c7 := (tupleExtendSetIndex st.regs.c7 idx x).1 } }.consumeTupleGas
            (tupleExtendSetIndex st.regs.c7 idx x).2
        else { st with stack := s, regs := { st.regs with c7 := (tupleExtendSetIndex st.regs.c7 idx x).1 } }) := by
  vm_simp [hs]
  first
  | (cases tupleExtendSetIndex st.regs.c7 idx x with
     | mk t pay => by_cases hp : 0 < pay <;> vm_simp [hp])
  | (split <;> rename_i t pay h <;> by_cases hp : 0 < pay <;> vm_simp [hp, h])

/-- `SETGASLIMIT` (C++ `exec_set_gas_limit`) on the stack `s n`: the limit `n` if `0 < n < 2^63`,
unlimited from `2^63`, 0 if `n ≤ 0`; out of gas (the limits as they were) if it is below the gas
consumed. -/
@[vm_spec] theorem setGasLimit (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.tonEnvOp .setGasLimit)) st =
      if (if 0 < n then (if n < 9223372036854775808 then n else GasLimits.infty) else 0) < st.gas.gasConsumed then
        (.error .outOfGas, { st with stack := s })
      else
        (.ok (), { st with
          stack := s
          gas := st.gas.changeLimit (if 0 < n then (if n < 9223372036854775808 then n else GasLimits.infty) else 0) }) := by
  vm_simp [hs, Nat.reduceShiftLeft]

end TvmLean.Spec

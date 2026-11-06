import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: `GETGLOB`, `SETGLOB`, `SETGASLIMIT`

In the format of `Proofs/Exec/Spec/Stack.lean`:

* `GETGLOB k` (C++ `exec_get_global`, tonops.cpp): the entry `k` of `c7`, null past its end;
* `SETGLOB k` (C++ `exec_set_global`): the entry `k` of `c7` set to the value popped, `c7`
  extended with nulls if it is shorter (`tupleExtendSetIndex`; nothing for a null past its end),
  the new tuple's entries charged (`VmState.consumeTupleGas`);
* `GETGLOBVAR`, `SETGLOBVAR` (C++ `exec_get_global_var`, `exec_set_global_var`): the same with the
  index `k` popped (range_chk outside `0..254`, C++ `pop_smallint_range(254)`);
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

/-- `GETGLOBVAR` (C++ `exec_get_global_var`, tonops.cpp:222) on the stack `s k`: `GETGLOB k`
(range_chk outside `0..254`). -/
@[vm_spec] theorem getGlobVar (st : VmState) (s : Stack) (k : Int) (hs : st.stack = s.push (.int (.num k))) :
    ExceptT.run (execInstr (.tonEnvOp .getGlobVar)) st =
      if 0 ≤ k ∧ k ≤ 254 then
        if k.toNat < st.regs.c7.size then (.ok (), { st with stack := s.push st.regs.c7[k.toNat]! })
        else (.ok (), { st with stack := s.push .null })
      else (.error .rangeChk, { st with stack := s }) := by
  by_cases hm : 0 ≤ k ∧ k ≤ 254
  · have h1 : ¬ k < 0 := by omega
    have h2 : ¬ k.toNat > 254 := by omega
    rw [if_pos hm]
    by_cases h : k.toNat < st.regs.c7.size <;> vm_simp [hs, h1, h2, h]
  · rw [if_neg hm]
    by_cases h1 : k < 0
    · vm_simp [hs, h1]
    · have h2 : k.toNat > 254 := by omega
      vm_simp [hs, h1, h2]

/-- `SETGLOBVAR` (C++ `exec_set_global_var`, tonops.cpp:253) on the stack `s x k`: `SETGLOB k` of
`x` (range_chk outside `0..254`, `x` left). -/
@[vm_spec] theorem setGlobVar (st : VmState) (s : Stack) (x : Value) (k : Int)
    (hs : st.stack = (s.push x).push (.int (.num k))) :
    ExceptT.run (execInstr (.tonEnvOp .setGlobVar)) st =
      if 0 ≤ k ∧ k ≤ 254 then
        (.ok (), if 0 < (tupleExtendSetIndex st.regs.c7 k.toNat x).2 then
            { st with stack := s, regs := { st.regs with c7 := (tupleExtendSetIndex st.regs.c7 k.toNat x).1 } }.consumeTupleGas
              (tupleExtendSetIndex st.regs.c7 k.toNat x).2
          else { st with stack := s, regs := { st.regs with c7 := (tupleExtendSetIndex st.regs.c7 k.toNat x).1 } })
      else (.error .rangeChk, { st with stack := s.push x }) := by
  by_cases hm : 0 ≤ k ∧ k ≤ 254
  · have h1 : ¬ k < 0 := by omega
    have h2 : ¬ k.toNat > 254 := by omega
    rw [if_pos hm]
    vm_simp [hs, h1, h2]
    first
    | (cases tupleExtendSetIndex st.regs.c7 k.toNat x with
       | mk t pay => by_cases hp : 0 < pay <;> vm_simp [hp])
    | (split <;> rename_i t pay h <;> by_cases hp : 0 < pay <;> vm_simp [hp, h])
  · rw [if_neg hm]
    by_cases h1 : k < 0
    · vm_simp [hs, h1]
    · have h2 : k.toNat > 254 := by omega
      vm_simp [hs, h1, h2]

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

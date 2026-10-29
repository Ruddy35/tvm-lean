import TvmLean.Proofs.Exec.Spec.Tuple

/-!
# Specifications: the tuple instructions with the count or index on the stack

In the format of `Proofs/Exec/Spec/Tuple.lean` (one gas per entry of the tuple made or taken apart,
`gas := st.gas.consume (n * tupleEntryGasPrice)`): the count or index on top of the stack, popped
by `pop_smallint_range` (range_chk for a negative one or one above the bound, the operand below it
left), then the instruction with the constant argument:

* `UNPACKFIRSTVAR` (C++ `exec_untuple_first_var`, tupleops.cpp:181): `UNPACKFIRST n`;
* `EXPLODEVAR` (C++ `exec_explode_tuple_var`, tupleops.cpp:202): `EXPLODE n`;
* `SETINDEXVARQ` (C++ `exec_tuple_quiet_set_index_var`, tupleops.cpp:258): `SETINDEXQ k`, on a
  tuple and on null.

The loops of the handlers that push the entries of a tuple are `VM.run_push_entries`.
-/

namespace TvmLean.Spec

/-- `UNPACKFIRSTVAR` (C++ `exec_untuple_first_var`, tupleops.cpp:181-186, opcode `6F83`): the count
`n` on top, `0 ≤ n ≤ 255` (range_chk); the first `n` entries of a tuple of at least `n` (and at
most 255) entries below replace it (type_chk otherwise), as `UNPACKFIRST n`. -/
@[vm_spec] theorem unpackFirstVar (st : VmState) (s : Stack) (items : Array Value) (n : Int)
    (hs : st.stack = (s.push (.tuple items)).push (.int (.num n))) :
    ExceptT.run (execInstr (.tupleOp .unpackFirstVar)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if 255 < n.toNat then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if 255 < items.size ∨ items.size < n.toNat then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := s ++ items.extract 0 n.toNat,
                              gas := st.gas.consume (n.toNat * tupleEntryGasPrice) }) := by
  vm_simp [hs]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i h
        rw [VM.run_push_entries _ _ _ (by omega)]
        vm_simp [VmState.consumeTupleGas, VmState.consumeGas]

/-- `EXPLODEVAR` (C++ `exec_explode_tuple_var`, tupleops.cpp:202-207, opcode `6F84`): the bound `n`
on top, `0 ≤ n ≤ 255` (range_chk); a tuple of at most `n` entries below is replaced by its entries
and their number (type_chk for a longer one), as `EXPLODE n`. -/
@[vm_spec] theorem explodeVar (st : VmState) (s : Stack) (items : Array Value) (n : Int)
    (hs : st.stack = (s.push (.tuple items)).push (.int (.num n))) :
    ExceptT.run (execInstr (.tupleOp .explodeVar)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if 255 < n.toNat then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if n.toNat < items.size then (.error .typeChk, { st with stack := s })
      else if 255 < items.size then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := (s ++ items).push (.int (.num items.size)),
                              gas := st.gas.consume (items.size * tupleEntryGasPrice) }) := by
  vm_simp [hs]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [VM.run_push_entries _ _ _ (Nat.le_refl _)]
        vm_simp [VmState.consumeTupleGas, VmState.consumeGas]

/-- The handler of `SETINDEXVARQ` run with its conditions decided by the hypotheses, before
`vm_simp` (whose contextual `simp` on the handler as written, the join points of its `do` blocks
written out in each branch, does not finish): `VM.run_ite_throw` keeps the checks linear. -/
local macro "tuple_var_pre" : tactic =>
  `(tactic| simp only [TvmLean.Exec.reduceExecInstrRun, TvmLean.Exec.unfoldModelRun, VM.run_bind, VM.run_get,
    VM.run_pure, VM.run_pop, VM.run_popInt, VM.run_checkUnderflow, Array.size_push, Nat.zero_lt_succ, dite_true,
    VM.back_push, Array.pop_push, VM.bindRes_ok, VM.bindRes_error, VM.run_throw, ↓VM.run_ite_throw, if_true,
    if_false, Bool.false_eq_true, *])

/-- `SETINDEXVARQ` (C++ `exec_tuple_quiet_set_index_var`, tupleops.cpp:258-263, opcode `6F87`) on
a tuple: the index `k` on top, `0 ≤ k ≤ 254` (range_chk); as `SETINDEXQ k`: the entry `k` of the
tuple becomes the value above it, a tuple too short extended with nulls (unless the value is null:
the tuple stays). -/
@[vm_spec] theorem setIndexVarQ (st : VmState) (s : Stack) (items : Array Value) (x : Value) (k : Int)
    (hs : st.stack = ((s.push (.tuple items)).push x).push (.int (.num k))) :
    ExceptT.run (execInstr (.tupleOp .setIndexVarQ)) st =
      if k < 0 then (.error .rangeChk, { st with stack := (s.push (.tuple items)).push x })
      else if 254 < k.toNat then (.error .rangeChk, { st with stack := (s.push (.tuple items)).push x })
      else if 255 < items.size then (.error .typeChk, { st with stack := s })
      else if items.size ≤ k.toNat then
        if x == .null then (.ok (), { st with stack := s.push (.tuple items) })
        else (.ok (), { st with
          stack := s.push (.tuple ((items ++ Array.replicate (k.toNat + 1 - items.size) Value.null).set! k.toNat x)),
          gas := st.gas.consume ((k.toNat + 1 : Nat) * tupleEntryGasPrice) })
      else (.ok (), { st with stack := s.push (.tuple (items.set! k.toNat x)),
                              gas := st.gas.consume (items.size * tupleEntryGasPrice) }) := by
  have hsz : ¬ s.size + 1 + 1 + 1 < 3 := by omega
  by_cases hk : k < 0
  · tuple_var_pre
  by_cases hk' : 254 < k.toNat
  · tuple_var_pre
  have h255 : ¬ k.toNat ≥ 255 := by omega
  by_cases h3 : 255 < items.size
  · tuple_var_pre
  by_cases h1 : items.size ≤ k.toNat <;> by_cases h2 : (x == Value.null) = true <;>
    tuple_var_pre <;> vm_simp [VmState.consumeTupleGas, VmState.consumeGas]

/-- `SETINDEXVARQ` on null: the index `k` on top, `0 ≤ k ≤ 254` (range_chk); a tuple of `k + 1`
nulls with the value at `k` (null if the value is null), as `SETINDEXQ k` on null. -/
@[vm_spec] theorem setIndexVarQ_null (st : VmState) (s : Stack) (x : Value) (k : Int)
    (hs : st.stack = ((s.push .null).push x).push (.int (.num k))) :
    ExceptT.run (execInstr (.tupleOp .setIndexVarQ)) st =
      if k < 0 then (.error .rangeChk, { st with stack := (s.push .null).push x })
      else if 254 < k.toNat then (.error .rangeChk, { st with stack := (s.push .null).push x })
      else if x == .null then (.ok (), { st with stack := s.push .null })
      else (.ok (), { st with stack := s.push (.tuple ((Array.replicate (k.toNat + 1) Value.null).set! k.toNat x)),
                              gas := st.gas.consume ((k.toNat + 1 : Nat) * tupleEntryGasPrice) }) := by
  have hsz : ¬ s.size + 1 + 1 + 1 < 3 := by omega
  by_cases hk : k < 0
  · tuple_var_pre
  by_cases hk' : 254 < k.toNat
  · tuple_var_pre
  have h255 : ¬ k.toNat ≥ 255 := by omega
  by_cases h2 : (x == Value.null) = true <;>
    tuple_var_pre <;> vm_simp [VmState.consumeTupleGas, VmState.consumeGas]

end TvmLean.Spec

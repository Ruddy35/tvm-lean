import TvmLean.Proofs.Exec.Eval
import TvmLean.Proofs.Exec.Spec.StackExt

/-!
# Specifications: tuples and null

In the format of `Proofs/Exec/Spec/Stack.lean`. A tuple instruction charges one gas per entry of
the tuple it makes or takes apart (`VmState.consumeTupleGas`, without a check: the gas of the step
finds it), written `gas := st.gas.consume (n * tupleEntryGasPrice)`. A tuple taken from the stack
has at most 255 entries in C++ (`pop_tuple_range(255)`); the model checks it where C++ does
(type_chk otherwise).

* `TUPLE n`, `UNTUPLE n`, `UNPACKFIRST n`, `EXPLODE n` (their loops over the entries as `Array`
  operations: `VM.run_pop_loop`, `foldl_push_range`), `INDEX`, `INDEX2`, `INDEX3` (the inner tuples
  given), `INDEXQ`, `SETINDEX`, `SETINDEXQ` (on a tuple and on null), `TLEN`, `QTLEN`, `ISTUPLE`,
  `LAST`, `TPUSH`, `TPOP`;
* `TUPLEVAR`, `UNTUPLEVAR`, `INDEXVAR` (the count or index from the stack);
* `NULL`, `ISNULL`, `NULLSWAPIF`, `NULLSWAPIFNOT`, `NULLROTRIF`, `NULLROTRIFNOT` and their `2` forms.
-/

namespace TvmLean

/-- Pushing the entries `a .. a+k-1` of `items` one by one appends them. -/
theorem foldl_push_range (items : Array Value) (a k : Nat) (s : Stack) (h : a + k ≤ items.size) :
    (List.range' a k).foldl (fun s i => s.push items[i]!) s = s ++ items.extract a (a + k) := by
  induction k generalizing a s with
  | zero => simp; omega
  | succ k ih =>
    rw [List.range'_succ, List.foldl_cons, ih (a + 1) _ (by omega)]
    apply Array.ext
    · simp; omega
    · intro i h1 h2
      simp only [Array.getElem_append, Array.size_push, Array.getElem_push, Array.getElem_extract]
      grind

theorem extract_pop_push (a : Array Value) (k : Nat) (h : k + 1 ≤ a.size) (h0 : 0 < a.size) :
    a.extract (a.size - (k + 1)) a.size = (a.pop.extract (a.pop.size - k) a.pop.size).push (a.back h0) := by
  apply Array.ext
  · simp; omega
  · intro j h1 h2
    simp only [Array.getElem_push, Array.getElem_extract, Array.size_extract, Array.size_pop, Array.getElem_pop,
      Array.back_eq_getElem]
    split
    · congr 1; omega
    · congr 1; simp at h1 h2; omega

theorem take_pop (a : Array Value) (k : Nat) (h : k + 1 ≤ a.size) :
    a.pop.take (a.pop.size - k) = a.take (a.size - (k + 1)) := by
  apply Array.ext
  · simp; omega
  · intro j h1 h2
    simp [Array.getElem_pop]

/-- The loop of `TUPLE` (C++ `exec_mktuple`): popping `l.length` values one by one onto `items`
appends them, the top first. -/
theorem VM.run_pop_loop (l : List Nat) (items : Array Value) (st : VmState) (h : l.length ≤ st.stack.size) :
    ExceptT.run (forIn l items fun _ r => do
        let v ← VM.pop
        pure PUnit.unit
        pure (ForInStep.yield (r.push v))) st =
      (.ok (items ++ (st.stack.extract (st.stack.size - l.length) st.stack.size).reverse),
        { st with stack := st.stack.take (st.stack.size - l.length) }) := by
  induction l generalizing items st with
  | nil => simp; rfl
  | cons i l ih =>
    have h0 : 0 < st.stack.size := by simp at h; omega
    rw [List.forIn_cons, VM.run_bind, VM.run_bind, VM.run_pop, dif_pos h0, VM.bindRes_ok]
    simp only [VM.run_bind, VM.run_pure, VM.bindRes_ok]
    rw [ih _ _ (by simp at h ⊢; omega)]
    simp only [List.length_cons] at h ⊢
    rw [extract_pop_push _ _ h h0, take_pop _ _ h, Array.reverse_push, Array.push_eq_append, Array.append_assoc]

/-- `if c then throw e` followed by `R` in `do` notation, which writes `R` in both branches: the
exception, or `R`. Used before the branches are visited (`↓`), it keeps the run of a handler with
several such checks linear in their number. -/
theorem VM.run_ite_throw {α : Type} (c : Prop) [Decidable c] (e : Excno) (R : VM α) (st : VmState) :
    ExceptT.run (if c then ((throw e : VM PUnit) >>= fun _ => R) else ((pure PUnit.unit : VM PUnit) >>= fun _ => R)) st =
      if c then (.error e, st) else ExceptT.run R st := by
  split <;> rfl

/-- The loop of `UNTUPLE` and the like: pushing the entries `0 .. n-1` of `items`. -/
theorem VM.run_push_entries (items : Array Value) (n : Nat) (st : VmState) (h : n ≤ items.size) :
    ExceptT.run (forIn [:n] PUnit.unit fun i _ => do
        VM.push items[i]!
        pure (ForInStep.yield PUnit.unit)) st =
      (.ok PUnit.unit, { st with stack := st.stack ++ items.extract 0 n }) := by
  rw [Std.Range.forIn_eq_forIn_range',
    VM.run_forIn_stack _ _ (fun i s => s.push items[i]!) (fun _ => True) (by simp) (by intro i _ st' _; rfl) _ trivial]
  simp only [Std.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [foldl_push_range items 0 n _ (by omega), Nat.zero_add]

namespace Spec

/-! ## Making and taking apart tuples -/

/-- `TUPLE n` (C++ `exec_mktuple`): the top `n` values become a tuple, the deepest first. -/
@[vm_spec] theorem mktuple (st : VmState) (n : Nat) :
    ExceptT.run (execInstr (.tupleOp (.mktuple n))) st =
      if n ≤ st.stack.size then
        (.ok (), { st with stack := (st.stack.take (st.stack.size - n)).push
                                      (.tuple (st.stack.extract (st.stack.size - n) st.stack.size)),
                           gas := st.gas.consume (n * tupleEntryGasPrice) })
      else (.error .stkUnd, st) := by
  vm_simp
  split
  · rw [Std.Range.forIn_eq_forIn_range']
    rw [VM.run_pop_loop _ _ _ (by simp [Std.Range.size]; omega)]
    vm_simp [Std.Range.size, VmState.consumeTupleGas, VmState.consumeGas, Array.reverse_reverse, List.length_range',
      Nat.div_one, Array.empty_append]
  · rfl

/-- `UNTUPLE n` (C++ `exec_untuple`): a tuple of `n` entries is replaced by its entries, the first
deepest; type_chk for a tuple of another size. -/
@[vm_spec] theorem untuple (st : VmState) (s : Stack) (items : Array Value) (n : Nat)
    (hs : st.stack = s.push (.tuple items)) :
    ExceptT.run (execInstr (.tupleOp (.untuple n))) st =
      if items.size = n then
        (.ok (), { st with stack := s ++ items, gas := st.gas.consume (n * tupleEntryGasPrice) })
      else (.error .typeChk, { st with stack := s }) := by
  vm_simp [hs]
  split
  · rename_i h
    rw [VM.run_push_entries _ _ _ (by omega)]
    subst h
    vm_simp [VmState.consumeTupleGas, VmState.consumeGas]
  · rfl

/-- `UNPACKFIRST n` (C++ `exec_untuple_first`): the first `n` entries of a tuple of at least `n`
(and at most 255) entries replace it. -/
@[vm_spec] theorem unpackFirst (st : VmState) (s : Stack) (items : Array Value) (n : Nat)
    (hs : st.stack = s.push (.tuple items)) :
    ExceptT.run (execInstr (.tupleOp (.unpackFirst n))) st =
      if 255 < items.size ∨ items.size < n then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := s ++ items.extract 0 n, gas := st.gas.consume (n * tupleEntryGasPrice) }) := by
  vm_simp [hs]
  split
  · rfl
  · rename_i h
    rw [VM.run_push_entries _ _ _ (by omega)]
    vm_simp [VmState.consumeTupleGas, VmState.consumeGas]

/-- `EXPLODE n` (C++ `exec_explode_tuple`): a tuple of at most `n` entries is replaced by its
entries and their number. -/
@[vm_spec] theorem explode (st : VmState) (s : Stack) (items : Array Value) (n : Nat)
    (hs : st.stack = s.push (.tuple items)) :
    ExceptT.run (execInstr (.tupleOp (.explode n))) st =
      if n < items.size then (.error .typeChk, { st with stack := s })
      else if 255 < items.size then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := (s ++ items).push (.int (.num items.size)),
                              gas := st.gas.consume (items.size * tupleEntryGasPrice) }) := by
  vm_simp [hs]
  split
  · rfl
  · split
    · rfl
    · rw [VM.run_push_entries _ _ _ (Nat.le_refl _)]
      vm_simp [VmState.consumeTupleGas, VmState.consumeGas]

/-- `TUPLEVAR` (C++ `exec_mktuple_var`): the count `n` on top, `0 ≤ n ≤ 255` (range_chk); the
next `n` values become a tuple, as `TUPLE n`. -/
@[vm_spec] theorem mktupleVar (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.tupleOp .mktupleVar)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if 255 < n.toNat then (.error .rangeChk, { st with stack := s })
      else if n.toNat ≤ s.size then
        (.ok (), { st with stack := (s.take (s.size - n.toNat)).push (.tuple (s.extract (s.size - n.toNat) s.size)),
                           gas := st.gas.consume (n.toNat * tupleEntryGasPrice) })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs]
  split
  · rfl
  · split
    · rfl
    · split
      · rw [Std.Range.forIn_eq_forIn_range']
        rw [VM.run_pop_loop _ _ _ (by simp [Std.Range.size]; omega)]
        vm_simp [Std.Range.size, VmState.consumeTupleGas, VmState.consumeGas, Array.reverse_reverse,
          List.length_range', Nat.div_one, Array.empty_append]
      · rfl

/-- `UNTUPLEVAR` (C++ `exec_untuple_var`): the count `n` on top, `0 ≤ n ≤ 255` (range_chk); a
tuple of exactly `n` entries below (type_chk otherwise) is replaced by its entries, as
`UNTUPLE n`. -/
@[vm_spec] theorem untupleVar (st : VmState) (s : Stack) (items : Array Value) (n : Int)
    (hs : st.stack = (s.push (.tuple items)).push (.int (.num n))) :
    ExceptT.run (execInstr (.tupleOp .untupleVar)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if 255 < n.toNat then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if items.size ≠ n.toNat then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := s ++ items, gas := st.gas.consume (n.toNat * tupleEntryGasPrice) }) := by
  vm_simp [hs, bne_iff_ne]
  split
  · rfl
  · split
    · rfl
    · by_cases he : items.size = n.toNat
      · have h255 : ¬ 255 < items.size := by omega
        simp only [he, not_true_eq_false]
        rw [VM.run_push_entries _ _ _ (by omega)]
        vm_simp [VmState.consumeTupleGas, VmState.consumeGas, ← he, false_or, h255]
      · simp only [he, not_false_eq_true, true_or, if_true, if_false]

/-! ## Entries -/

/-- `INDEX k` (C++ `exec_tuple_index`): the entry `k` of a tuple; range_chk if there is none. -/
@[vm_spec] theorem index (st : VmState) (s : Stack) (items : Array Value) (k : Nat)
    (hs : st.stack = s.push (.tuple items)) :
    ExceptT.run (execInstr (.tupleOp (.index k))) st =
      if k < items.size then (.ok (), { st with stack := s.push items[k]! })
      else (.error .rangeChk, { st with stack := s }) := by
  vm_simp [hs]

/-- `INDEX2 i,j` (C++ `exec_tuple_index2`) when the entry `i` is the tuple `t1`: its entry `j`. -/
@[vm_spec] theorem index2 (st : VmState) (s : Stack) (items t1 : Array Value) (i j : Nat)
    (hs : st.stack = s.push (.tuple items)) (h1 : items[i]! = .tuple t1) :
    ExceptT.run (execInstr (.tupleOp (.index2 i j))) st =
      if 255 < items.size then (.error .typeChk, { st with stack := s })
      else if items.size ≤ i then (.error .rangeChk, { st with stack := s })
      else if 255 < t1.size then (.error .typeChk, { st with stack := s })
      else if t1.size ≤ j then (.error .rangeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push t1[j]! }) := by
  vm_simp [hs, h1]

/-- `INDEX3 i,j,k` (C++ `exec_tuple_index3`) when the entry `i` is the tuple `t1` and its entry
`j` the tuple `t2`: the entry `k` of `t2`. -/
@[vm_spec] theorem index3 (st : VmState) (s : Stack) (items t1 t2 : Array Value) (i j k : Nat)
    (hs : st.stack = s.push (.tuple items)) (h1 : items[i]! = .tuple t1) (h2 : t1[j]! = .tuple t2) :
    ExceptT.run (execInstr (.tupleOp (.index3 i j k))) st =
      if 255 < items.size then (.error .typeChk, { st with stack := s })
      else if items.size ≤ i then (.error .rangeChk, { st with stack := s })
      else if 255 < t1.size then (.error .typeChk, { st with stack := s })
      else if t1.size ≤ j then (.error .rangeChk, { st with stack := s })
      else if 255 < t2.size then (.error .typeChk, { st with stack := s })
      else if t2.size ≤ k then (.error .rangeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push t2[k]! }) := by
  simp only [TvmLean.Exec.reduceExecInstrRun, TvmLean.Exec.unfoldModelRun, VM.run_bind, VM.run_get, VM.run_pop, hs,
    Array.size_push, Nat.zero_lt_succ, dite_true, VM.back_push, Array.pop_push, VM.bindRes_ok, ↓VM.run_ite_throw]
  vm_simp [h1, h2]

/-- `INDEXQ k` (C++ `exec_tuple_quiet_index`) on a tuple: the entry `k`, null if there is none. -/
@[vm_spec] theorem indexQ (st : VmState) (s : Stack) (items : Array Value) (k : Nat)
    (hs : st.stack = s.push (.tuple items)) :
    ExceptT.run (execInstr (.tupleOp (.indexQ k))) st =
      if 255 < items.size then (.error .typeChk, { st with stack := s })
      else if k < items.size then (.ok (), { st with stack := s.push items[k]! })
      else (.ok (), { st with stack := s.push .null }) := by
  vm_simp [hs]

/-- `INDEXQ k` on null: null. -/
@[vm_spec] theorem indexQ_null (st : VmState) (s : Stack) (k : Nat) (hs : st.stack = s.push .null) :
    ExceptT.run (execInstr (.tupleOp (.indexQ k))) st = (.ok (), { st with stack := s.push .null }) := by
  vm_simp [hs]

/-- `INDEXVAR` (C++ `exec_tuple_index_var`): the index `k` on top, `0 ≤ k ≤ 254` (range_chk); the
entry `k` of the tuple below. -/
@[vm_spec] theorem indexVar (st : VmState) (s : Stack) (items : Array Value) (k : Int)
    (hs : st.stack = (s.push (.tuple items)).push (.int (.num k))) :
    ExceptT.run (execInstr (.tupleOp .indexVar)) st =
      if k < 0 then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if 254 < k.toNat then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if 255 < items.size then (.error .typeChk, { st with stack := s })
      else if k.toNat < items.size then (.ok (), { st with stack := s.push items[k.toNat]! })
      else (.error .rangeChk, { st with stack := s }) := by
  vm_simp [hs]

/-- `SETINDEX k` (C++ `exec_tuple_set_index`): the entry `k` of the tuple below the top becomes
the top; range_chk if there is none. -/
@[vm_spec] theorem setIndex (st : VmState) (s : Stack) (items : Array Value) (x : Value) (k : Nat)
    (hs : st.stack = (s.push (.tuple items)).push x) :
    ExceptT.run (execInstr (.tupleOp (.setIndex k))) st =
      if 255 < items.size then (.error .typeChk, { st with stack := s })
      else if items.size ≤ k then (.error .rangeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push (.tuple (items.set! k x)),
                              gas := st.gas.consume (items.size * tupleEntryGasPrice) }) := by
  vm_simp [hs, VmState.consumeTupleGas, VmState.consumeGas, VM.size_set!]

/-- `SETINDEXQ k` (C++ `exec_tuple_quiet_set_index`) on a tuple: as `SETINDEX`, a tuple too short
extended with nulls (unless the value is null: the tuple stays); range_chk for `k ≥ 255`. -/
@[vm_spec] theorem setIndexQ (st : VmState) (s : Stack) (items : Array Value) (x : Value) (k : Nat)
    (hs : st.stack = (s.push (.tuple items)).push x) :
    ExceptT.run (execInstr (.tupleOp (.setIndexQ k))) st =
      if 255 ≤ k then (.error .rangeChk, { st with stack := s })
      else if 255 < items.size then (.error .typeChk, { st with stack := s })
      else if items.size ≤ k then
        if x == .null then (.ok (), { st with stack := s.push (.tuple items) })
        else (.ok (), { st with stack := s.push (.tuple ((items ++ Array.replicate (k + 1 - items.size) Value.null).set! k x)),
                                gas := st.gas.consume ((k + 1 : Nat) * tupleEntryGasPrice) })
      else (.ok (), { st with stack := s.push (.tuple (items.set! k x)),
                              gas := st.gas.consume (items.size * tupleEntryGasPrice) }) := by
  simp only [TvmLean.Exec.reduceExecInstrRun, TvmLean.Exec.unfoldModelRun, VM.run_bind, VM.run_get, VM.run_pop, hs,
    Array.size_push, Nat.zero_lt_succ, dite_true, VM.back_push, Array.pop_push, VM.bindRes_ok, ↓VM.run_ite_throw]
  by_cases h0 : 255 ≤ k
  · simp only [ge_iff_le, h0, if_true]
  by_cases h3 : 255 < items.size
  · simp only [ge_iff_le, h0, h3, gt_iff_lt, if_true, if_false]
  by_cases h1 : items.size ≤ k <;> by_cases h2 : (x == Value.null) = true <;>
    simp only [ge_iff_le, gt_iff_lt, h0, h1, h2, h3, if_true, if_false, Bool.false_eq_true] <;>
    vm_simp [VmState.consumeTupleGas, VmState.consumeGas]

/-- `SETINDEXQ k` on null: a tuple of `k + 1` nulls with the value at `k` (null if the value is
null); range_chk for `k ≥ 255`. -/
@[vm_spec] theorem setIndexQ_null (st : VmState) (s : Stack) (x : Value) (k : Nat)
    (hs : st.stack = (s.push .null).push x) :
    ExceptT.run (execInstr (.tupleOp (.setIndexQ k))) st =
      if 255 ≤ k then (.error .rangeChk, { st with stack := s })
      else if x == .null then (.ok (), { st with stack := s.push .null })
      else (.ok (), { st with stack := s.push (.tuple ((Array.replicate (k + 1) Value.null).set! k x)),
                              gas := st.gas.consume ((k + 1 : Nat) * tupleEntryGasPrice) }) := by
  simp only [TvmLean.Exec.reduceExecInstrRun, TvmLean.Exec.unfoldModelRun, VM.run_bind, VM.run_get, VM.run_pop, hs,
    Array.size_push, Nat.zero_lt_succ, dite_true, VM.back_push, Array.pop_push, VM.bindRes_ok, ↓VM.run_ite_throw]
  by_cases h0 : 255 ≤ k
  · simp only [ge_iff_le, h0, if_true]
  by_cases h2 : (x == Value.null) = true <;>
    simp only [ge_iff_le, gt_iff_lt, h0, h2, if_true, if_false, Bool.false_eq_true] <;>
    vm_simp [VmState.consumeTupleGas, VmState.consumeGas]

/-- `TLEN` (C++ `exec_tuple_length`): the number of entries of a tuple. -/
@[vm_spec] theorem tlen (st : VmState) (s : Stack) (items : Array Value) (hs : st.stack = s.push (.tuple items)) :
    ExceptT.run (execInstr (.tupleOp .tlen)) st =
      if 255 < items.size then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push (.int (.num items.size)) }) := by
  vm_simp [hs]

/-- `QTLEN` (C++ `exec_tuple_length_quiet`) on a tuple: its number of entries. -/
@[vm_spec] theorem qtlen (st : VmState) (s : Stack) (items : Array Value) (hs : st.stack = s.push (.tuple items)) :
    ExceptT.run (execInstr (.tupleOp .qtlen)) st =
      if 255 < items.size then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push (.int (.num items.size)) }) := by
  vm_simp [hs]

/-- `QTLEN` on a value that is not a tuple: -1. -/
@[vm_spec] theorem qtlen_other (st : VmState) (s : Stack) (v : Value) (hv : ∀ t, v ≠ .tuple t)
    (hs : st.stack = s.push v) :
    ExceptT.run (execInstr (.tupleOp .qtlen)) st = (.ok (), { st with stack := s.push (.int (.num (-1))) }) := by
  cases v <;> first | (exact absurd rfl (hv _)) | vm_simp [hs]

/-- `ISTUPLE` (C++ `exec_is_tuple`): -1 for a tuple, 0 for any other value. -/
@[vm_spec] theorem isTuple (st : VmState) (s : Stack) (v : Value) (hs : st.stack = s.push v) :
    ExceptT.run (execInstr (.tupleOp .isTuple)) st =
      (.ok (), { st with stack := s.push (.int (.num (match v with | .tuple _ => -1 | _ => 0))) }) := by
  cases v <;> vm_simp [hs]

/-- `LAST` (C++ `exec_tuple_last`): the last entry of a tuple of 1 to 255 entries. -/
@[vm_spec] theorem last (st : VmState) (s : Stack) (items : Array Value) (hs : st.stack = s.push (.tuple items)) :
    ExceptT.run (execInstr (.tupleOp .last)) st =
      if 255 < items.size ∨ items.size < 1 then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push items[items.size - 1]! }) := by
  vm_simp [hs]

/-- `TPUSH` (C++ `exec_tuple_push`): the top is appended to the tuple below it (of at most 254
entries). -/
@[vm_spec] theorem tpush (st : VmState) (s : Stack) (items : Array Value) (x : Value)
    (hs : st.stack = (s.push (.tuple items)).push x) :
    ExceptT.run (execInstr (.tupleOp .tpush)) st =
      if 254 < items.size then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push (.tuple (items.push x)),
                              gas := st.gas.consume ((items.size + 1 : Nat) * tupleEntryGasPrice) }) := by
  vm_simp [hs, VmState.consumeTupleGas, VmState.consumeGas]

/-- `TPOP` (C++ `exec_tuple_pop`): the last entry of a tuple of 1 to 255 entries is taken off and
pushed above the rest of the tuple. -/
@[vm_spec] theorem tpop (st : VmState) (s : Stack) (items : Array Value) (hs : st.stack = s.push (.tuple items)) :
    ExceptT.run (execInstr (.tupleOp .tpop)) st =
      if 255 < items.size ∨ items.size < 1 then (.error .typeChk, { st with stack := s })
      else (.ok (), { st with stack := (s.push (.tuple items.pop)).push items[items.size - 1]!,
                              gas := st.gas.consume ((items.size - 1 : Nat) * tupleEntryGasPrice) }) := by
  vm_simp [hs, VmState.consumeTupleGas, VmState.consumeGas]

/-! ## Null -/

/-- `NULL` = `PUSHNULL` (C++ `exec_push_null`). -/
@[vm_spec] theorem pushNull (st : VmState) :
    ExceptT.run (execInstr .pushNull) st = (.ok (), { st with stack := st.stack.push .null }) := by
  vm_simp

/-- `ISNULL` (C++ `exec_is_null`): -1 for null, 0 for any other value. -/
@[vm_spec] theorem isNull (st : VmState) (s : Stack) (v : Value) (hs : st.stack = s.push v) :
    ExceptT.run (execInstr .isNull) st =
      (.ok (), { st with stack := s.push (.int (.num (match v with | .null => -1 | _ => 0))) }) := by
  cases v <;> vm_simp [hs]

/-- `NULLSWAPIF` (C++ `exec_null_swap_if`): a null is put below a nonzero integer on top. -/
@[vm_spec] theorem nullSwapIf (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .nullSwapIf) st =
      if x ≠ 0 then (.ok (), { st with stack := (s.push .null).push (.int (.num x)) })
      else (.ok (), { st with stack := s.push (.int (.num x)) }) := by
  vm_simp [hs, Std.Range.forIn_eq_forIn_range', Std.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons,
    List.forIn_nil, Nat.reduceDiv, bne_iff_ne]

/-- `NULLSWAPIFNOT` (C++ `exec_null_swap_if`): a null is put below a zero on top. -/
@[vm_spec] theorem nullSwapIfNot (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .nullSwapIfNot) st =
      if x = 0 then (.ok (), { st with stack := (s.push .null).push (.int (.num x)) })
      else (.ok (), { st with stack := s.push (.int (.num x)) }) := by
  vm_simp [hs, Std.Range.forIn_eq_forIn_range', Std.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons,
    List.forIn_nil, Nat.reduceDiv, bne_iff_ne]

/-- `NULLROTRIF` (C++ `exec_null_swap_if`, depth 1): a null is put below the two top values when
the top is a nonzero integer. -/
@[vm_spec] theorem nullRotrIf (st : VmState) (s : Stack) (a : Value) (x : Int)
    (hs : st.stack = (s.push a).push (.int (.num x))) :
    ExceptT.run (execInstr .nullRotrIf) st =
      if x ≠ 0 then (.ok (), { st with stack := ((s.push .null).push a).push (.int (.num x)) })
      else (.ok (), { st with stack := (s.push a).push (.int (.num x)) }) := by
  vm_simp [hs, Std.Range.forIn_eq_forIn_range', Std.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons,
    List.forIn_nil, Nat.reduceDiv, bne_iff_ne]

/-- `NULLROTRIFNOT` (C++ `exec_null_swap_if`, depth 1): as `NULLROTRIF` for a zero. -/
@[vm_spec] theorem nullRotrIfNot (st : VmState) (s : Stack) (a : Value) (x : Int)
    (hs : st.stack = (s.push a).push (.int (.num x))) :
    ExceptT.run (execInstr .nullRotrIfNot) st =
      if x = 0 then (.ok (), { st with stack := ((s.push .null).push a).push (.int (.num x)) })
      else (.ok (), { st with stack := (s.push a).push (.int (.num x)) }) := by
  vm_simp [hs, Std.Range.forIn_eq_forIn_range', Std.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons,
    List.forIn_nil, Nat.reduceDiv, bne_iff_ne]

/-- `NULLSWAPIF2` (C++ `exec_null_swap_if_many`): two nulls are put below a nonzero integer on
top. -/
@[vm_spec] theorem nullSwapIf2 (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .nullSwapIf2) st =
      if x ≠ 0 then (.ok (), { st with stack := ((s.push .null).push .null).push (.int (.num x)) })
      else (.ok (), { st with stack := s.push (.int (.num x)) }) := by
  vm_simp [hs, Std.Range.forIn_eq_forIn_range', Std.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons,
    List.forIn_nil, Nat.reduceDiv, bne_iff_ne]

/-- `NULLSWAPIFNOT2` (C++ `exec_null_swap_if_many`): two nulls below a zero on top. -/
@[vm_spec] theorem nullSwapIfNot2 (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .nullSwapIfNot2) st =
      if x = 0 then (.ok (), { st with stack := ((s.push .null).push .null).push (.int (.num x)) })
      else (.ok (), { st with stack := s.push (.int (.num x)) }) := by
  vm_simp [hs, Std.Range.forIn_eq_forIn_range', Std.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons,
    List.forIn_nil, Nat.reduceDiv, bne_iff_ne]

/-- `NULLROTRIF2` (C++ `exec_null_swap_if_many`, depth 1): two nulls below the two top values when
the top is a nonzero integer. -/
@[vm_spec] theorem nullRotrIf2 (st : VmState) (s : Stack) (a : Value) (x : Int)
    (hs : st.stack = (s.push a).push (.int (.num x))) :
    ExceptT.run (execInstr .nullRotrIf2) st =
      if x ≠ 0 then (.ok (), { st with stack := (((s.push .null).push .null).push a).push (.int (.num x)) })
      else (.ok (), { st with stack := (s.push a).push (.int (.num x)) }) := by
  vm_simp [hs, Std.Range.forIn_eq_forIn_range', Std.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons,
    List.forIn_nil, Nat.reduceDiv, bne_iff_ne]

/-- `NULLROTRIFNOT2` (C++ `exec_null_swap_if_many`, depth 1): as `NULLROTRIF2` for a zero. -/
@[vm_spec] theorem nullRotrIfNot2 (st : VmState) (s : Stack) (a : Value) (x : Int)
    (hs : st.stack = (s.push a).push (.int (.num x))) :
    ExceptT.run (execInstr .nullRotrIfNot2) st =
      if x = 0 then (.ok (), { st with stack := (((s.push .null).push .null).push a).push (.int (.num x)) })
      else (.ok (), { st with stack := (s.push a).push (.int (.num x)) }) := by
  vm_simp [hs, Std.Range.forIn_eq_forIn_range', Std.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons,
    List.forIn_nil, Nat.reduceDiv, bne_iff_ne]

end Spec

end TvmLean

import TvmLean.Proofs.Exec.Spec.TupleVar

/-!
# Specifications: `SETINDEXVAR`, `INDEXVARQ`

In the format of `Proofs/Exec/Spec/Tuple.lean`: the index on top of the stack, popped by
`pop_smallint_range(254)` (range_chk for a negative one or one above 254, the operands below it
left), then the instruction with the constant index:

* `SETINDEXVAR` (C++ `exec_tuple_set_index_var`, tupleops.cpp:229): `SETINDEX k`;
* `INDEXVARQ` (C++ `exec_tuple_quiet_index_var`, tupleops.cpp:130): `INDEXQ k`, on a tuple and on null.
-/

namespace TvmLean.Spec

/-- `SETINDEXVAR` (C++ `exec_tuple_set_index_var`) on the stack `s t x k`: `SETINDEX k` (range_chk
for an index outside `0..254`, or past the end of the tuple). -/
@[vm_spec] theorem setIndexVar (st : VmState) (s : Stack) (items : Array Value) (x : Value) (k : Int)
    (hs : st.stack = ((s.push (.tuple items)).push x).push (.int (.num k))) :
    ExceptT.run (execInstr (.tupleOp .setIndexVar)) st =
      if k < 0 then (.error .rangeChk, { st with stack := (s.push (.tuple items)).push x })
      else if 254 < k.toNat then (.error .rangeChk, { st with stack := (s.push (.tuple items)).push x })
      else if 255 < items.size then (.error .typeChk, { st with stack := s })
      else if items.size ≤ k.toNat then (.error .rangeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push (.tuple (items.set! k.toNat x)),
                              gas := st.gas.consume (items.size * tupleEntryGasPrice) }) := by
  vm_simp [hs, VmState.consumeTupleGas, VmState.consumeGas, VM.size_set!]

/-- `INDEXVARQ` (C++ `exec_tuple_quiet_index_var`) on the stack `s t k`: `INDEXQ k` (range_chk for
an index outside `0..254`). -/
@[vm_spec] theorem indexVarQ (st : VmState) (s : Stack) (items : Array Value) (k : Int)
    (hs : st.stack = (s.push (.tuple items)).push (.int (.num k))) :
    ExceptT.run (execInstr (.tupleOp .indexVarQ)) st =
      if k < 0 then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if 254 < k.toNat then (.error .rangeChk, { st with stack := s.push (.tuple items) })
      else if 255 < items.size then (.error .typeChk, { st with stack := s })
      else if k.toNat < items.size then (.ok (), { st with stack := s.push items[k.toNat]! })
      else (.ok (), { st with stack := s.push .null }) := by
  vm_simp [hs]

/-- `INDEXVARQ` on null: null (range_chk for an index outside `0..254`). -/
@[vm_spec] theorem indexVarQ_null (st : VmState) (s : Stack) (k : Int)
    (hs : st.stack = (s.push .null).push (.int (.num k))) :
    ExceptT.run (execInstr (.tupleOp .indexVarQ)) st =
      if k < 0 then (.error .rangeChk, { st with stack := s.push .null })
      else if 254 < k.toNat then (.error .rangeChk, { st with stack := s.push .null })
      else (.ok (), { st with stack := s.push .null }) := by
  vm_simp [hs]

end TvmLean.Spec

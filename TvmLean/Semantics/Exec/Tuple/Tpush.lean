import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpTpush (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .tpush =>
      let x ← VM.pop
      let t ← VM.pop
      match t with
      | .tuple items =>
          -- C++ exec_tuple_push: pop_tuple_range(254) raises type_chk for a tuple of invalid size
          if items.size > 254 then
            throw .typeChk
          let out := items.push x
          VM.push (.tuple out)
          modify fun st => st.consumeTupleGas out.size
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean

import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowJmpRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .jmpRef code =>
      -- C++ `ref_to_cont(load_cell_slice_ref)`: the load is charged, a library cell runs its
      -- library's root, other exotic cells are cell_und
      let code ← VM.loadCellSlice code.cell
      VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | .jmpRefData code =>
      -- C++ `exec_do_with_ref` builds `cont = ref_to_cont(cell)` (`load_cell_slice_ref`) before the
      -- JMPREFDATA lambda runs, so the load and its errors come before `push_code()`
      let code ← VM.loadCellSlice code.cell
      VM.pushCode
      VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | _ => next

end TvmLean

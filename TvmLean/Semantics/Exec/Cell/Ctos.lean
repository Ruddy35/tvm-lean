import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellCtos (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ctos =>
      let c ← VM.popCell
      -- C++ `load_cell_slice_ref`: the load is charged, a library cell loads as its library's root,
      -- other exotic cells are cell_und
      VM.push (.slice (← VM.loadCellSlice c))
  | _ => next

end TvmLean

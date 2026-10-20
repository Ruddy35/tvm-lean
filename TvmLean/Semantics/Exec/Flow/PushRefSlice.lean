import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowPushRefSlice (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushRefSlice c =>
      -- Matches C++ `exec_push_ref` (cellops.cpp), mode 1: load cell slice (charges cell load).
      -- C++ `load_cell_slice_ref`: the load is charged, a library cell loads as its library's root,
      -- other exotic cells are cell_und
      VM.push (.slice (← VM.loadCellSlice c))
  | _ => next

end TvmLean

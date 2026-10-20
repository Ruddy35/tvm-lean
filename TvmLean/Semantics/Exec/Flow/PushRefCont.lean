import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowPushRefCont (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushRefCont c =>
      -- C++ `load_cell_slice_ref`: the load is charged, a library cell loads as its library's root,
      -- other exotic cells are cell_und
      VM.push (.cont (.ordinary (← VM.loadCellSlice c) (.quit 0) OrdCregs.empty OrdCdata.empty))
  | _ => next

end TvmLean

import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callRef code =>
      -- C++ `CALLREF`: `ref_to_cont(load_cell_slice_ref(ref))`; the load is charged, a library cell
      -- runs its library's root, other exotic cells are cell_und
      let code ← VM.loadCellSlice code.cell
      VM.call (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | _ => next

end TvmLean

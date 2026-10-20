import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfjmpref (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifjmpref code =>
      if (← VM.popBool) then
        -- C++ `ref_to_cont(load_cell_slice_ref)`: a library cell runs its library's root, other
        -- exotic cells are cell_und
        let code ← VM.loadCellSlice code.cell
        VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | _ => next

end TvmLean

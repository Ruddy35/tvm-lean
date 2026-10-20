import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellLdrefRtos (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ldrefRtos =>
      let s ← VM.popSlice
      if s.haveRefs 1 then
        let c := s.cell.refs[s.refPos]!
        let s' := { s with refPos := s.refPos + 1 }
        -- C++ pushes the remainder, then `load_cell_slice_ref`: the load is charged, a library
        -- cell loads as its library's root, other exotic cells are cell_und
        VM.push (.slice s')
        VM.push (.slice (← VM.loadCellSlice c))
      else
        throw .cellUnd
  | _ => next

end TvmLean

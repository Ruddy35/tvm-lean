import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpSdepth (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .sdepth =>
      -- C++ `exec_slice_depth` (cellops.cpp:1397-1401): `CellSlice::get_depth`, the depth of the
      -- references left in the slice (`Slice.depth`), not of the slice's cell
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.depth)
  | _ => next

end TvmLean

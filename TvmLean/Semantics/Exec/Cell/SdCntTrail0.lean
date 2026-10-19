import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdCntTrail0 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdCntTrail0 =>
      let s ← VM.popSlice
      let rem : Nat := s.bitsRemaining
      let endPos : Nat := s.cell.bits.size
      let cnt : Nat := countWhile rem (fun c => s.cell.bits[endPos - 1 - c]! == false) 0
      VM.pushSmallInt (Int.ofNat cnt)
  | _ => next

end TvmLean

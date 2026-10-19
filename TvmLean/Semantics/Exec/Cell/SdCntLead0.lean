import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdCntLead0 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdCntLead0 =>
      let s ← VM.popSlice
      let rem : Nat := s.bitsRemaining
      let cnt : Nat := countWhile rem (fun c => s.cell.bits[s.bitPos + c]! == false) 0
      VM.pushSmallInt (Int.ofNat cnt)
  | _ => next

end TvmLean

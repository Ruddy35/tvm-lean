import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCryptoHashCU (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cryptoOp .hashCU =>
      let c ← VM.popCell
      let h := Cell.hashBytes c
      let n := bytesToNatBE h
      VM.pushIntQuiet (.num (Int.ofNat n)) false
  | _ => next

end TvmLean

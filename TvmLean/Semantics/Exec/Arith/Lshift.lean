import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithLshift (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .lshift =>
      VM.checkUnderflow 2
      let shift ← VM.popNatUpTo 1023
      let x ← VM.popInt
      match x with
      | .nan =>
          -- C++ `exec_lshift` (arithops.cpp:814-822): since version 13 NaN stays NaN; before, the
          -- BigInt shift of NaN is computed
          VM.pushIntQuiet (if (← get).globalVersion ≥ 13 then .nan else IntVal.nanLshiftCpp shift) false
      | .num n =>
          if shift ≥ 260 then
            VM.pushIntQuiet .nan false
          else
            VM.pushIntQuiet (.num (n * intPow2 shift)) false
  | _ => next

end TvmLean

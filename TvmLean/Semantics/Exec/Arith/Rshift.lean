import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithRshift (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .rshift =>
      VM.checkUnderflow 2
      let shift ← VM.popNatUpTo 1023
      let x ← VM.popInt
      match x with
      | .nan =>
          -- C++ `exec_rshift` (arithops.cpp:833-841): since version 13 NaN stays NaN; before, the
          -- BigInt shift of NaN is computed
          VM.pushIntQuiet (if (← get).globalVersion ≥ 13 then .nan else IntVal.nanRshiftCpp shift) false
      | .num n => VM.pushIntQuiet (.num (floorDivPow2 n shift)) false
  | _ => next

end TvmLean

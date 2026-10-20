import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithRshiftConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .rshiftConst quiet bits =>
      let x ← VM.popInt
      match x with
      | .nan =>
          -- C++ `exec_rshift_tinyint8` (arithops.cpp:792-806): since TVM 14 NaN stays NaN; before,
          -- the BigInt shift of NaN is computed (`IntVal.nanRshiftCpp`)
          let gv : Nat := (← get).globalVersion
          let invalidCompat : IntVal := if gv ≥ 14 then .nan else IntVal.nanRshiftCpp bits
          VM.pushIntQuiet invalidCompat quiet
      | .num n => VM.pushIntQuiet (.num (floorDivPow2 n bits)) quiet
  | _ => next

end TvmLean

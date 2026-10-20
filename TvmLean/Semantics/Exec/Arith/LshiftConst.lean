import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithLshiftConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .lshiftConst quiet bits =>
      let x ← VM.popInt
      match x with
      | .nan =>
          -- C++ `exec_lshift_tinyint8` (arithops.cpp:775-790): since TVM 14 NaN stays NaN; before,
          -- the BigInt shift of NaN is computed (`IntVal.nanLshiftCpp`)
          let gv : Nat := (← get).globalVersion
          let invalidCompat : IntVal := if gv ≥ 14 then .nan else IntVal.nanLshiftCpp bits
          VM.pushIntQuiet invalidCompat quiet
      | .num n => VM.pushIntQuiet (.num (n * intPow2 bits)) quiet
  | _ => next

end TvmLean

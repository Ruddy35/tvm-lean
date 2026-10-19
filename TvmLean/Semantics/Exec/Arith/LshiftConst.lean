import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithLshiftConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .lshiftConst quiet bits =>
      let x ← VM.popInt
      match x with
      | .nan =>
          -- Match C++ `exec_lshift_tinyint8`: invalid integers are shifted via
          -- `AnyIntView::lshift_any`, where small shifts preserve NaN but
          -- shifts by whole words normalize invalid-zero to integer zero.
          -- Since TVM 14 NaN stays NaN (before, a C++ BigInt quirk turned it into a number).
          let gv : Nat := (← get).globalVersion
          let invalidCompat : IntVal :=
            if gv ≥ 14 then .nan else
            if bits = 0 then
              .nan
            else if bits < 64 then
              .nan
            else
              .num 0
          VM.pushIntQuiet invalidCompat quiet
      | .num n => VM.pushIntQuiet (.num (n * intPow2 bits)) quiet
  | _ => next

end TvmLean

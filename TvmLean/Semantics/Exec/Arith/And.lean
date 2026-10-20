import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithAnd (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .and_ =>
      VM.checkUnderflow 2
      let y ← VM.popInt
      let x ← VM.popInt
      -- C++ `exec_and` (arithops.cpp:873): since version 13 a NaN operand gives NaN; before, the BigInt
      -- operation is computed
      let gv : Nat := (← get).globalVersion
      match x, y with
      | .nan, _ | _, .nan => VM.pushIntQuiet (if gv ≥ 13 then .nan else IntVal.nanAndCpp x y) false
      | .num a, .num b =>
          let ba ←
            match intToBitsTwos a 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bb ←
            match intToBitsTwos b 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bc := bitsAnd ba bb
          let c := bitsToIntSignedTwos bc
          VM.pushIntQuiet (.num c) false
  | _ => next

end TvmLean

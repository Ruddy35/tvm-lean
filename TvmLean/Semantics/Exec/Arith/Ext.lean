import TvmLean.Semantics.Exec.Common

namespace TvmLean

private def popLongLike : VM Int := do
  let x ← VM.popInt
  match x with
  | .nan => pure (-1)
  | .num n => pure n

private def shiftOutOfRange (shift : Int) (max : Nat) : Bool :=
  decide (shift < 0 ∨ shift > Int.ofNat max)

private def bigintWordShift : Nat := 52
private def bigintWordBits : Nat := 64
private def bigintBase : Int := intPow2 bigintWordShift
private def bigintHalf : Int := intPow2 (bigintWordShift - 1)

/-- Loop body of `intToBigInt52Digits` with explicit fuel. Each step strictly decreases `|q|`
(the digit `d` satisfies `|d| ≤ base/2`), so `n.natAbs + 1` steps always suffice. -/
private def intToBigInt52DigitsAux (q : Int) (out : Array Int) : Nat → Array Int
  | 0 => out
  | fuel + 1 =>
      if q != 0 then
        let r : Int := Int.emod q bigintBase
        let d : Int :=
          if decide (r >= bigintHalf) then
            r - bigintBase
          else
            r
        intToBigInt52DigitsAux ((q - d) / bigintBase) (out.push d) fuel
      else
        out

private def intToBigInt52Digits (n : Int) : Array Int :=
  if n == 0 then
    #[0]
  else
    let out := intToBigInt52DigitsAux n #[] (n.natAbs + 1)
    if out.isEmpty then #[0] else out

private def addAnyNoNormalize (x y : Array Int) : Array Int :=
  if y.size <= x.size then
    Id.run do
      let mut out := x
      for i in [0:y.size] do
        out := out.set! i (out[i]! + y[i]!)
      out
  else
    Id.run do
      let mut out := y
      for i in [0:x.size] do
        out := out.set! i (out[i]! + x[i]!)
      out

private def rshiftPow2RoundAddCompat (x w : Int) (shift : Nat) (roundMode : Int) : Int :=
  -- C++ `exec_shrmod` (ADD* variants) applies `rshift` to a non-normalized
  -- temporary (`tmp += w` without normalize). For very large shifts, `rshift_any`
  -- uses fast-path sign checks on the non-normalized top word, which can differ
  -- from mathematically rounded `(x + w) / 2^shift`. Mirror that behavior here.
  let tmp : Int := x + w
  let xDigits := intToBigInt52Digits x
  let wDigits := intToBigInt52Digits w
  let tmpDigits := addAnyNoNormalize xDigits wDigits
  let fastLimit : Nat := tmpDigits.size * bigintWordShift + (bigintWordBits - bigintWordShift)
  if shift > fastLimit then
    let top : Int := tmpDigits[tmpDigits.size - 1]!
    if roundMode == 0 then
      0
    else if decide (roundMode < 0) then
      if decide (top < 0) then -1 else 0
    else
      if decide (top > 0) then 1 else 0
  else
    rshiftPow2Round tmp shift roundMode

private def rshiftPow2RoundInvalidCompat (shift : Nat) (roundMode : Int) : IntVal :=
  if shift == 0 then
    .nan
  else
    let fastLimit : Nat := bigintWordBits - bigintWordShift
    if decide (roundMode < 0) && shift > fastLimit then
      .num (-1)
    else
      .num 0

set_option maxHeartbeats 1000000 in
def execInstrArithExt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .arithExt op =>
      match op with
      | .invalidArgs _ _ =>
          -- rounding mode 3 in a division family: C++ charges the instruction's gas
          -- (OpcodeInstrFixed::dispatch), then exec_* raises inv_opcode
          throw .invOpcode
      | .qaddInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushIntQuiet (.num (a + n)) true
      | .qmulInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushIntQuiet (.num (a * n)) true
      | .qeqInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushSmallInt (if a = n then -1 else 0)
      | .qneqInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushSmallInt (if a ≠ n then -1 else 0)
      | .qgtInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushSmallInt (if a > n then -1 else 0)
      | .fitsConst unsigned quiet bits =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan quiet
          | .num n =>
              let ok :=
                if unsigned then
                  intUnsignedFitsBits n bits
                else
                  intSignedFitsBits n bits
              if ok then
                VM.push (.int x)
              else if quiet then
                VM.push (.int .nan)
              else
                throw .intOv
      | .lshiftVar quiet =>
          VM.checkUnderflow 2
          let shiftRaw ← popLongLike
          let badShift := shiftOutOfRange shiftRaw 1023
          -- C++ `exec_lshift` (arithops.cpp:814-822): before version 13 a shift outside 0..1023 is
          -- range_chk in the quiet form too, and NaN is shifted as a BigInt
          let gv : Nat := (← get).globalVersion
          if (!quiet || gv < 13) && badShift then
            throw .rangeChk
          let x ← VM.popInt
          if badShift then
            VM.pushIntQuiet .nan quiet
          else
            let shift : Nat := shiftRaw.toNat
            match x with
            | .nan => VM.pushIntQuiet (if gv ≥ 13 then .nan else IntVal.nanLshiftCpp shift) quiet
            | .num n =>
                let qWords : Nat := shift / bigintWordShift
                let isZeroHugeInvalid : Bool :=
                  n = 0 && (intToBigInt52Digits n).size + qWords > 5
                if isZeroHugeInvalid then
                  VM.pushIntQuiet .nan quiet
                else
                  VM.pushIntQuiet (.num (n * intPow2 shift)) quiet
      | .rshiftVar quiet =>
          VM.checkUnderflow 2
          let shiftRaw ← popLongLike
          let badShift := shiftOutOfRange shiftRaw 1023
          -- C++ `exec_rshift` (arithops.cpp:833-841): before version 13 a shift outside 0..1023 is
          -- range_chk in the quiet form too, and NaN is shifted as a BigInt
          let gv : Nat := (← get).globalVersion
          if (!quiet || gv < 13) && badShift then
            throw .rangeChk
          let x ← VM.popInt
          if badShift then
            VM.pushIntQuiet .nan quiet
          else
            let shift : Nat := shiftRaw.toNat
            match x with
            | .nan => VM.pushIntQuiet (if gv ≥ 13 then .nan else IntVal.nanRshiftCpp shift) quiet
            | .num n => VM.pushIntQuiet (.num (floorDivPow2 n shift)) quiet
      | .shrMod mulMode addMode d roundMode quiet zOpt =>
          -- C++ `exec_mulshrmod` and `exec_shrmod` (arithops.cpp:530, 350): the ADD forms (result
          -- mode 0) exist from version 4, before that they are inv_opcode
          if addMode && (← get).globalVersion < 4 then throw .invOpcode
          if mulMode then
            -- MULRSHIFT/MULMODPOW2 family: runtime shift range checks are relaxed in quiet mode
            -- (global version >= 13), producing NaN instead of throwing.
            -- Like C++ `exec_mulshrmod`, enforce stack depth before popping shift:
            -- runtime-shift variants need 3 args (`x y z`) or 4 with add-mode.
            -- const-shift variants need 2 args (`x y`) or 3 with add-mode.
            let st ← get
            let need : Nat :=
              if zOpt.isSome then
                if addMode then 3 else 2
              else
                if addMode then 4 else 3
            if st.stack.size < need then
              throw .stkUnd
            let shiftRaw ←
              match zOpt with
              | some z => pure (Int.ofNat z)
              | none => popLongLike
            let badShift := shiftOutOfRange shiftRaw 256
            -- C++ `exec_mulshrmod` (arithops.cpp:542-560): before version 13 a shift outside
            -- 0..256 is range_chk in the quiet forms too, and NaN operands are computed as BigInts
            let gv : Nat := (← get).globalVersion
            if (!quiet || gv < 13) && badShift then
              throw .rangeChk
            let w ← if addMode then VM.popInt else pure (.num 0)
            let y ← VM.popInt
            let x ← VM.popInt
            if badShift then
              if d == 3 then
                VM.pushIntQuiet .nan quiet
                VM.pushIntQuiet .nan quiet
              else
                VM.pushIntQuiet .nan quiet
            else
              match x, y, w with
              | .num xn, .num yn, .num wn =>
                  let shift : Nat := shiftRaw.toNat
                  let roundMode' : Int :=
                    if zOpt.isNone && shift == 0 then
                      -1
                    else
                      roundMode
                  if roundMode' != -1 && roundMode' != 0 && roundMode' != 1 then
                    throw .invOpcode
                  let tmp0 : Int := xn * yn
                  let tmp : Int := if addMode then tmp0 + wn else tmp0
                  match d with
                  | 1 =>
                      let q := rshiftPow2Round tmp shift roundMode'
                      VM.pushIntQuiet (.num q) quiet
                  | 2 =>
                      let r := modPow2Round tmp shift roundMode'
                      VM.pushIntQuiet (.num r) quiet
                  | 3 =>
                      let q := rshiftPow2Round tmp shift roundMode'
                      let r := modPow2Round tmp shift roundMode'
                      VM.pushIntQuiet (.num q) quiet
                      VM.pushIntQuiet (.num r) quiet
                  | _ =>
                      throw .invOpcode
              | _, _, _ =>
                  if gv ≥ 13 then
                    if d == 3 then
                      VM.pushIntQuiet .nan quiet
                      VM.pushIntQuiet .nan quiet
                    else
                      VM.pushIntQuiet .nan quiet
                  else
                    -- before version 13: `x * y + w` with a NaN operand is NaN (`add_mul_any`,
                    -- bigint.hpp:952), its shift `IntVal.nanRshiftCpp`, its remainder NaN
                    -- (`mod_pow2_any`, bigint.hpp:1443); a shift by 0 rounds down (arithops.cpp:547)
                    let shift : Nat := shiftRaw.toNat
                    let q := IntVal.nanRshiftCpp shift (if shift == 0 then -1 else roundMode)
                    match d with
                    | 1 => VM.pushIntQuiet q quiet
                    | 2 => VM.pushIntQuiet .nan quiet
                    | _ =>
                        VM.pushIntQuiet q quiet
                        VM.pushIntQuiet .nan quiet
          else
            -- RSHIFT/MODPOW2 family: runtime shift is strict `pop_smallint_range(256)` even in quiet mode.
            let st ← get
            let need : Nat :=
              if zOpt.isSome then
                if addMode then 2 else 1
              else
                if addMode then 3 else 2
            if st.stack.size < need then
              throw .stkUnd
            -- C++ `exec_shrmod`: since TVM 14 an invalid shift in quiet mode does not throw
            -- `range_chk`; a NaN operand or invalid shift yields NaN result(s).
            let gv : Nat := (← get).globalVersion
            let sv : Nat × Bool ←
              match zOpt with
              | some z => pure (z, true)
              | none =>
                  if gv ≥ 14 then
                    let raw ← popLongLike
                    let bad := shiftOutOfRange raw 256
                    if (!quiet) && bad then
                      throw .rangeChk
                    pure (if bad then 0 else raw.toNat, !bad)
                  else
                    let s ← VM.popNatUpTo 256
                    pure (s, true)
            let shift : Nat := sv.1
            let validShift : Bool := sv.2
            let w ← if addMode then VM.popInt else pure (.num 0)
            let x ← VM.popInt
            let anyNan : Bool :=
              match x, w with
              | .num _, .num _ => false
              | _, _ => true
            if gv ≥ 14 && (!validShift || anyNan) then
              VM.pushIntQuiet .nan quiet
              if d == 3 then
                VM.pushIntQuiet .nan quiet
            else
              let roundMode' : Int :=
                if zOpt.isNone && shift == 0 then
                  -1
                else
                  roundMode
              if roundMode' != -1 && roundMode' != 0 && roundMode' != 1 then
                throw .invOpcode
              let hasInvalid : Bool :=
                match x, w with
                | .num _, .num _ => false
                | _, _ => true
              if hasInvalid then
                let qCompat := rshiftPow2RoundInvalidCompat shift roundMode'
                match d with
                | 1 =>
                    VM.pushIntQuiet qCompat quiet
                | 2 =>
                    VM.pushIntQuiet .nan quiet
                | 3 =>
                    VM.pushIntQuiet qCompat quiet
                    VM.pushIntQuiet .nan quiet
                | _ =>
                    throw .invOpcode
              else
                match x, w with
                | .num xn, .num wn =>
                    let tmp : Int := if addMode then xn + wn else xn
                    let qCompat : Int :=
                      if addMode then
                        rshiftPow2RoundAddCompat xn wn shift roundMode'
                      else
                        rshiftPow2Round tmp shift roundMode'
                    match d with
                    | 1 =>
                        VM.pushIntQuiet (.num qCompat) quiet
                    | 2 =>
                        let r := modPow2Round tmp shift roundMode'
                        VM.pushIntQuiet (.num r) quiet
                    | 3 =>
                        let r := modPow2Round tmp shift roundMode'
                        VM.pushIntQuiet (.num qCompat) quiet
                        VM.pushIntQuiet (.num r) quiet
                    | _ =>
                        throw .invOpcode
                | _, _ =>
                    throw .invOpcode
      | .shlDivMod d roundMode addMode quiet zOpt =>
          -- C++ `exec_shldivmod` (arithops.cpp:643): the ADD forms (result mode 0) exist from version 4,
          -- before that they are inv_opcode
          if addMode && (← get).globalVersion < 4 then throw .invOpcode
          -- TVM `exec_shldivmod` checks arity first, then pops runtime shift
          -- (when present), then divisor.
          let st ← get
          let need : Nat :=
            if zOpt.isSome then
              if addMode then 3 else 2
            else
              if addMode then 4 else 3
          if st.stack.size < need then
            throw .stkUnd
          let shiftRaw ←
            match zOpt with
            | some z => pure (Int.ofNat z)
            | none => popLongLike
          let badShift := shiftOutOfRange shiftRaw 256
          -- C++ `exec_shldivmod` (arithops.cpp:655-673): before version 13 a shift outside 0..256 is
          -- range_chk in the quiet forms too, and NaN operands are computed as BigInts
          let gv : Nat := (← get).globalVersion
          if (!quiet || gv < 13) && badShift then
            throw .rangeChk
          let y ← VM.popInt
          let w ← if addMode then VM.popInt else pure (.num 0)
          let x0 ← VM.popInt
          -- before version 13 `x << shift` of a NaN `x` is the BigInt shift of NaN in a 514-bit
          -- BigInt (`DoubleInt`, 10 words): a valid 0 for a shift of at least one 52-bit word
          -- (`lshift_any`, bigint.hpp:1611); the sum and the division then take NaN on to the results
          let x : IntVal :=
            match x0 with
            | .nan => if gv < 13 ∧ 52 ≤ shiftRaw then .num 0 else .nan
            | v => v
          if badShift then
              if d == 3 then
                VM.pushIntQuiet .nan quiet
                VM.pushIntQuiet .nan quiet
              else
                VM.pushIntQuiet .nan quiet
          else
            match x, w, y with
            | .num xn, .num wn, .num yn =>
                if yn = 0 then
                  if d == 3 then
                    VM.pushIntQuiet .nan quiet
                    VM.pushIntQuiet .nan quiet
                  else
                    VM.pushIntQuiet .nan quiet
                else if roundMode != -1 && roundMode != 0 && roundMode != 1 then
                  throw .invOpcode
                else
                  let shift : Nat := shiftRaw.toNat
                  let tmp : Int := xn * intPow2 shift + wn
                  let (q, r) := divModRound tmp yn roundMode
                  match d with
                  | 1 =>
                      VM.pushIntQuiet (.num q) quiet
                  | 2 =>
                      VM.pushIntQuiet (.num r) quiet
                  | 3 =>
                      VM.pushIntQuiet (.num q) quiet
                      VM.pushIntQuiet (.num r) quiet
                  | _ =>
                      throw .invOpcode
            | _, _, _ =>
                if d == 3 then
                  VM.pushIntQuiet .nan quiet
                  VM.pushIntQuiet .nan quiet
                else
                  VM.pushIntQuiet .nan quiet
  | _ => next

end TvmLean

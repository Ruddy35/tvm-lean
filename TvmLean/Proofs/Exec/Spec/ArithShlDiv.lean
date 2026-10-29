import TvmLean.Proofs.Exec.Spec.ArithRound

/-!
# Specifications: shift left and divide with rounding (`exec_shldivmod`)

In the format of `Proofs/Exec/Spec/ArithExt.lean`, the operands finite integers (`IntVal.num`): the
instructions of C++ `exec_shldivmod` (arithops.cpp:633; opcodes `A9Cx` and the quiet `B7A9Cx`,
arithops.cpp:755, 769; `A9Dxyy` the shift a constant, arithops.cpp:757, which has no quiet form),
every rounding mode the decoder makes (`rm`: -1 down, 0 to nearest with ties up, 1 up):

* `LSHIFTDIV`, `LSHIFTDIVR`, `LSHIFTDIVC` (`shlDivMod 1`), `LSHIFTMOD`, `LSHIFTMODR`, `LSHIFTMODC`
  (`shlDivMod 2`), `LSHIFTDIVMOD`, `LSHIFTDIVMODR`, `LSHIFTDIVMODC` (`shlDivMod 3`), and
  `LSHIFTADDDIVMOD`, `LSHIFTADDDIVMODR`, `LSHIFTADDDIVMODC` (from global version 4), their quiet
  forms, the shift on the stack: `shlDivVar`, `shlModVar`, `shlDivModVar`, `shlAddDivModVar`;
* the `#` forms `LSHIFT#DIV`, `LSHIFT#MOD`, `LSHIFT#DIVMOD`, `LSHIFT#ADDDIVMOD` (each `R`, `C`):
  `shlDivConst`, `shlModConst`, `shlDivModConst`, `shlAddDivModConst`.

The results are `divModRound` of `x * 2^n` (`+ w`) by `y` (`divModRound_floor` of
`Spec/ArithExt.lean`, `divModRound_ceil`, `divModRound_nearest` of `Spec/ArithRound.lean`: the
operations of `Int` for a positive divisor); a zero divisor gives NaN (int_ov unless quiet). A shift
from the stack outside `0..256` is range_chk, from global version 13 NaN in the quiet forms
(arithops.cpp:655, 664-670); a result that does not fit 257 bits is int_ov, NaN if quiet; the
results are pushed in order. The handler is run by `vm_simp` after its conditions on the literals
of the instruction are decided (`shift_pre`).
-/

namespace TvmLean.Spec

/- The proofs of this module are elaborated one after the other, as in `Spec/ArithExt.lean`. -/
set_option Elab.async false

/-! ## The shift on the stack -/

set_option maxHeartbeats 4000000 in
/-- `LSHIFTDIV`, `LSHIFTDIVR`, `LSHIFTDIVC` (`A9C4`-`A9C6`) and their quiet forms (`B7A9Cx`; C++
`exec_shldivmod`, arithops.cpp:633, result mode 1): the quotient of `divModRound (x * 2^n) y rm`. -/
@[vm_spec] theorem shlDivVar (st : VmState) (s : Stack) (x y n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shlDivMod 1 rm false quiet none))) st =
      if (if quiet then st.globalVersion < 13 ∧ (n < 0 ∨ 256 < n) else n < 0 ∨ 256 < n) then
        (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.int (.num y)) })
      else if n < 0 ∨ 256 < n then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if y = 0 then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * 2 ^ n.toNat) y rm).1 ∧ (divModRound (x * 2 ^ n.toNat) y rm).1 < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num ((divModRound (x * 2 ^ n.toNat) y rm).1))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false,
    quiet_or_and, quiet_or_and']

set_option maxHeartbeats 4000000 in
/-- `LSHIFTMOD`, `LSHIFTMODR`, `LSHIFTMODC` (`A9C8`-`A9CA`) and their quiet forms (C++
`exec_shldivmod`, arithops.cpp:633, result mode 2): the remainder of `divModRound (x * 2^n) y rm`. -/
@[vm_spec] theorem shlModVar (st : VmState) (s : Stack) (x y n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shlDivMod 2 rm false quiet none))) st =
      if (if quiet then st.globalVersion < 13 ∧ (n < 0 ∨ 256 < n) else n < 0 ∨ 256 < n) then
        (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.int (.num y)) })
      else if n < 0 ∨ 256 < n then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if y = 0 then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * 2 ^ n.toNat) y rm).2 ∧ (divModRound (x * 2 ^ n.toNat) y rm).2 < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num ((divModRound (x * 2 ^ n.toNat) y rm).2))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false,
    quiet_or_and, quiet_or_and']

set_option maxHeartbeats 4000000 in
/-- `LSHIFTDIVMOD`, `LSHIFTDIVMODR`, `LSHIFTDIVMODC` (`A9CC`-`A9CE`) and their quiet forms (C++
`exec_shldivmod`, arithops.cpp:633, result mode 3): the quotient, then the remainder. A quotient
that does not fit is int_ov with nothing pushed, a remainder that does not fit with the quotient
pushed (NaN for either if quiet). -/
@[vm_spec] theorem shlDivModVar (st : VmState) (s : Stack) (x y n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shlDivMod 3 rm false quiet none))) st =
      if (if quiet then st.globalVersion < 13 ∧ (n < 0 ∨ 256 < n) else n < 0 ∨ 256 < n) then
        (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.int (.num y)) })
      else if n < 0 ∨ 256 < n then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if y = 0 then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * 2 ^ n.toNat) y rm).1 ∧ (divModRound (x * 2 ^ n.toNat) y rm).1 < 2 ^ 256 then
        if -2 ^ 256 ≤ (divModRound (x * 2 ^ n.toNat) y rm).2 ∧ (divModRound (x * 2 ^ n.toNat) y rm).2 < 2 ^ 256 then
          (.ok (), { st with
            stack :=
              (s.push (.int (.num ((divModRound (x * 2 ^ n.toNat) y rm).1)))).push
                (.int (.num ((divModRound (x * 2 ^ n.toNat) y rm).2))) })
        else if quiet then
          (.ok (), { st with
            stack := (s.push (.int (.num ((divModRound (x * 2 ^ n.toNat) y rm).1)))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num ((divModRound (x * 2 ^ n.toNat) y rm).1))) })
      else if quiet then
        if -2 ^ 256 ≤ (divModRound (x * 2 ^ n.toNat) y rm).2 ∧ (divModRound (x * 2 ^ n.toNat) y rm).2 < 2 ^ 256 then
          (.ok (), { st with
            stack := (s.push (.int .nan)).push (.int (.num ((divModRound (x * 2 ^ n.toNat) y rm).2))) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false,
    quiet_or_and, quiet_or_and']

set_option maxHeartbeats 4000000 in
/-- `LSHIFTADDDIVMOD`, `LSHIFTADDDIVMODR`, `LSHIFTADDDIVMODC` (`A9C0`-`A9C2`) and their quiet
forms (C++ `exec_shldivmod`, arithops.cpp:633, result mode 0, from global version 4,
arithops.cpp:643-649): the quotient and the remainder of `x * 2^n + w` by `y`, as in
`shlDivModVar`. -/
@[vm_spec] theorem shlAddDivModVar (st : VmState) (s : Stack) (x w y n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = (((s.push (.int (.num x))).push (.int (.num w))).push (.int (.num y))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shlDivMod 3 rm true quiet none))) st =
      if st.globalVersion < 4 then (.error .invOpcode, st)
      else if (if quiet then st.globalVersion < 13 ∧ (n < 0 ∨ 256 < n) else n < 0 ∨ 256 < n) then
        (.error .rangeChk, { st with stack := ((s.push (.int (.num x))).push (.int (.num w))).push (.int (.num y)) })
      else if n < 0 ∨ 256 < n then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if y = 0 then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * 2 ^ n.toNat + w) y rm).1 ∧
          (divModRound (x * 2 ^ n.toNat + w) y rm).1 < 2 ^ 256 then
        if -2 ^ 256 ≤ (divModRound (x * 2 ^ n.toNat + w) y rm).2 ∧
            (divModRound (x * 2 ^ n.toNat + w) y rm).2 < 2 ^ 256 then
          (.ok (), { st with
            stack :=
              (s.push (.int (.num ((divModRound (x * 2 ^ n.toNat + w) y rm).1)))).push
                (.int (.num ((divModRound (x * 2 ^ n.toNat + w) y rm).2))) })
        else if quiet then
          (.ok (), { st with stack :=
            (s.push (.int (.num ((divModRound (x * 2 ^ n.toNat + w) y rm).1)))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num ((divModRound (x * 2 ^ n.toNat + w) y rm).1))) })
      else if quiet then
        if -2 ^ 256 ≤ (divModRound (x * 2 ^ n.toNat + w) y rm).2 ∧
            (divModRound (x * 2 ^ n.toNat + w) y rm).2 < 2 ^ 256 then
          (.ok (), { st with stack :=
            (s.push (.int .nan)).push (.int (.num ((divModRound (x * 2 ^ n.toNat + w) y rm).2))) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false,
    quiet_or_and, quiet_or_and']

/-! ## The shift a constant (`#`, `A9Dxyy`: `z` is `yy + 1`) -/

set_option maxHeartbeats 4000000 in
/-- `LSHIFT#DIV`, `LSHIFT#DIVR`, `LSHIFT#DIVC` (`A9D4yy`-`A9D6yy`; C++ `exec_shldivmod`,
arithops.cpp:633, mode 2, result mode 1). -/
@[vm_spec] theorem shlDivConst (st : VmState) (s : Stack) (x y rm : Int) (z : Nat)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hz : z ≤ 256)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.arithExt (.shlDivMod 1 rm false false (some z)))) st =
      if y = 0 then (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * 2 ^ z) y rm).1 ∧ (divModRound (x * 2 ^ z) y rm).1 < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num ((divModRound (x * 2 ^ z) y rm).1))) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false, hz,
    show ¬ (z : Int) > 256 by omega]

set_option maxHeartbeats 4000000 in
/-- `LSHIFT#MOD`, `LSHIFT#MODR`, `LSHIFT#MODC` (`A9D8yy`-`A9DAyy`; C++ `exec_shldivmod`,
arithops.cpp:633, mode 2, result mode 2). -/
@[vm_spec] theorem shlModConst (st : VmState) (s : Stack) (x y rm : Int) (z : Nat)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hz : z ≤ 256)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.arithExt (.shlDivMod 2 rm false false (some z)))) st =
      if y = 0 then (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * 2 ^ z) y rm).2 ∧ (divModRound (x * 2 ^ z) y rm).2 < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num ((divModRound (x * 2 ^ z) y rm).2))) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false, hz,
    show ¬ (z : Int) > 256 by omega]

set_option maxHeartbeats 4000000 in
/-- `LSHIFT#DIVMOD`, `LSHIFT#DIVMODR`, `LSHIFT#DIVMODC` (`A9DCyy`-`A9DEyy`; C++ `exec_shldivmod`,
arithops.cpp:633, mode 2, result mode 3): the quotient, then the remainder. -/
@[vm_spec] theorem shlDivModConst (st : VmState) (s : Stack) (x y rm : Int) (z : Nat)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hz : z ≤ 256)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.arithExt (.shlDivMod 3 rm false false (some z)))) st =
      if y = 0 then (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * 2 ^ z) y rm).1 ∧ (divModRound (x * 2 ^ z) y rm).1 < 2 ^ 256 then
        if -2 ^ 256 ≤ (divModRound (x * 2 ^ z) y rm).2 ∧ (divModRound (x * 2 ^ z) y rm).2 < 2 ^ 256 then
          (.ok (), { st with
            stack :=
              (s.push (.int (.num ((divModRound (x * 2 ^ z) y rm).1)))).push
                (.int (.num ((divModRound (x * 2 ^ z) y rm).2))) })
        else (.error .intOv, { st with stack := s.push (.int (.num ((divModRound (x * 2 ^ z) y rm).1))) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false, hz,
    show ¬ (z : Int) > 256 by omega]

set_option maxHeartbeats 4000000 in
/-- `LSHIFT#ADDDIVMOD`, `LSHIFT#ADDDIVMODR`, `LSHIFT#ADDDIVMODC` (`A9D0yy`-`A9D2yy`; C++
`exec_shldivmod`, arithops.cpp:633, mode 2, result mode 0, from global version 4): the quotient and
the remainder of `x * 2^z + w` by `y`. -/
@[vm_spec] theorem shlAddDivModConst (st : VmState) (s : Stack) (x w y rm : Int) (z : Nat)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hz : z ≤ 256)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num w))).push (.int (.num y))) :
    ExceptT.run (execInstr (.arithExt (.shlDivMod 3 rm true false (some z)))) st =
      if st.globalVersion < 4 then (.error .invOpcode, st)
      else if y = 0 then (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * 2 ^ z + w) y rm).1 ∧ (divModRound (x * 2 ^ z + w) y rm).1 < 2 ^ 256 then
        if -2 ^ 256 ≤ (divModRound (x * 2 ^ z + w) y rm).2 ∧ (divModRound (x * 2 ^ z + w) y rm).2 < 2 ^ 256 then
          (.ok (), { st with
            stack :=
              (s.push (.int (.num ((divModRound (x * 2 ^ z + w) y rm).1)))).push
                (.int (.num ((divModRound (x * 2 ^ z + w) y rm).2))) })
        else (.error .intOv, { st with stack := s.push (.int (.num ((divModRound (x * 2 ^ z + w) y rm).1))) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false, hz,
    show ¬ (z : Int) > 256 by omega]

end TvmLean.Spec

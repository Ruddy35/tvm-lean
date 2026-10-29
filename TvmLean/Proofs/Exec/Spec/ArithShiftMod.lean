import TvmLean.Proofs.Exec.Spec.ArithRound

/-!
# Specifications: the right shifts with rounding, quotient and remainder (`exec_shrmod`)

As `Spec/ArithShift.lean`, the forms of C++ `exec_shrmod` (arithops.cpp:337) with two results, the
quotient then the remainder:

* `RSHIFTMOD`, `RSHIFTMODR`, `RSHIFTMODC` (`shrMod false false 3`) and their quiet forms, the shift
  on the stack: `shrModVar`; `RSHIFT#MOD` (each `R`, `C`): `shrModConst`;
* `ADDRSHIFTMOD`, `ADDRSHIFTMODR`, `ADDRSHIFTMODC` and their quiet forms (`shrMod false true 3`,
  from global version 4): `addShrModVar`; `ADDRSHIFT#MOD` (each `R`, `C`): `addShrModConst`.

The quotient of the `ADD` forms is `addShrQuot` (`Spec/ArithRound.lean`), the rounded quotient of
`x + w` for a shift of at most 64 bits (`addShrQuot_eq`), beyond that the sign of the top digit of
a sum C++ does not normalize (arithops.cpp:388-396); the model's private
`rshiftPow2RoundAddCompat` is rewritten to it by `rw_model_private`. A quotient that does not fit
257 bits is int_ov with nothing pushed, a remainder that does not fit with the quotient pushed
(NaN for either if quiet).
-/

namespace TvmLean.Spec

/- The proofs of this module are elaborated one after the other, as in `Spec/ArithExt.lean`. -/
set_option Elab.async false

/-! ## The shift on the stack -/

set_option maxHeartbeats 4000000 in
/-- `RSHIFTMOD`, `RSHIFTMODR`, `RSHIFTMODC` (`A92C`-`A92E`) and their quiet forms (C++
`exec_shrmod`, arithops.cpp:337, result mode 3): the quotient, then the remainder; the shift as in
`shrVar`. A quotient that does not fit is int_ov with nothing pushed, a remainder that does not fit
with the quotient pushed (NaN for either if quiet). -/
@[vm_spec] theorem shrModVar (st : VmState) (s : Stack) (x n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shrMod false false 3 rm quiet none))) st =
      if 14 ≤ st.globalVersion then
        if (if quiet then False else n < 0 ∨ 256 < n) then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
        else if n < 0 ∨ 256 < n then
          if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
          else (.error .intOv, { st with stack := s })
        else if -2 ^ 256 ≤ rshiftPow2Round x n.toNat rm ∧ rshiftPow2Round x n.toNat rm < 2 ^ 256 then
          if -2 ^ 256 ≤ modPow2Round x n.toNat rm ∧ modPow2Round x n.toNat rm < 2 ^ 256 then
            (.ok (), { st with stack :=
              (s.push (.int (.num (rshiftPow2Round x n.toNat rm)))).push (.int (.num (modPow2Round x n.toNat rm))) })
          else if quiet then
            (.ok (), { st with stack := (s.push (.int (.num (rshiftPow2Round x n.toNat rm)))).push (.int .nan) })
          else (.error .intOv, { st with stack := s.push (.int (.num (rshiftPow2Round x n.toNat rm))) })
        else if quiet then
          if -2 ^ 256 ≤ modPow2Round x n.toNat rm ∧ modPow2Round x n.toNat rm < 2 ^ 256 then
            (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num (modPow2Round x n.toNat rm))) })
          else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if n < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 256 < n.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if -2 ^ 256 ≤ rshiftPow2Round x n.toNat rm ∧ rshiftPow2Round x n.toNat rm < 2 ^ 256 then
        if -2 ^ 256 ≤ modPow2Round x n.toNat rm ∧ modPow2Round x n.toNat rm < 2 ^ 256 then
          (.ok (), { st with stack :=
            (s.push (.int (.num (rshiftPow2Round x n.toNat rm)))).push (.int (.num (modPow2Round x n.toNat rm))) })
        else if quiet then
          (.ok (), { st with stack := (s.push (.int (.num (rshiftPow2Round x n.toNat rm)))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num (rshiftPow2Round x n.toNat rm))) })
      else if quiet then
        if -2 ^ 256 ≤ modPow2Round x n.toNat rm ∧ modPow2Round x n.toNat rm < 2 ^ 256 then
          (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num (modPow2Round x n.toNat rm))) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false, quiet_and,
    quiet_and']

set_option maxHeartbeats 4000000 in
/-- `ADDRSHIFTMOD`, `ADDRSHIFTMODR`, `ADDRSHIFTMODC` (`A920`-`A922`) and their quiet forms (C++
`exec_shrmod`, arithops.cpp:337, result mode 0, from global version 4, arithops.cpp:350-353): the
quotient of `x + w` as C++ computes it (`addShrQuot`, arithops.cpp:388-394), then the remainder of
`x + w` (arithops.cpp:395); the shift as in `shrVar`, the results as in `shrModVar`. -/
@[vm_spec] theorem addShrModVar (st : VmState) (s : Stack) (x w n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num w))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shrMod false true 3 rm quiet none))) st =
      if st.globalVersion < 4 then (.error .invOpcode, st)
      else if 14 ≤ st.globalVersion then
        if (if quiet then False else n < 0 ∨ 256 < n) then
          (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.int (.num w)) })
        else if n < 0 ∨ 256 < n then
          if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
          else (.error .intOv, { st with stack := s })
        else if -2 ^ 256 ≤ addShrQuot x w n.toNat rm ∧ addShrQuot x w n.toNat rm < 2 ^ 256 then
          if -2 ^ 256 ≤ modPow2Round (x + w) n.toNat rm ∧ modPow2Round (x + w) n.toNat rm < 2 ^ 256 then
            (.ok (), { st with stack :=
              (s.push (.int (.num (addShrQuot x w n.toNat rm)))).push (.int (.num (modPow2Round (x + w) n.toNat rm))) })
          else if quiet then
            (.ok (), { st with stack := (s.push (.int (.num (addShrQuot x w n.toNat rm)))).push (.int .nan) })
          else (.error .intOv, { st with stack := s.push (.int (.num (addShrQuot x w n.toNat rm))) })
        else if quiet then
          if -2 ^ 256 ≤ modPow2Round (x + w) n.toNat rm ∧ modPow2Round (x + w) n.toNat rm < 2 ^ 256 then
            (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num (modPow2Round (x + w) n.toNat rm))) })
          else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if n < 0 then (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.int (.num w)) })
      else if 256 < n.toNat then (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.int (.num w)) })
      else if -2 ^ 256 ≤ addShrQuot x w n.toNat rm ∧ addShrQuot x w n.toNat rm < 2 ^ 256 then
        if -2 ^ 256 ≤ modPow2Round (x + w) n.toNat rm ∧ modPow2Round (x + w) n.toNat rm < 2 ^ 256 then
          (.ok (), { st with stack :=
            (s.push (.int (.num (addShrQuot x w n.toNat rm)))).push (.int (.num (modPow2Round (x + w) n.toNat rm))) })
        else if quiet then
          (.ok (), { st with stack := (s.push (.int (.num (addShrQuot x w n.toNat rm)))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num (addShrQuot x w n.toNat rm))) })
      else if quiet then
        if -2 ^ 256 ≤ modPow2Round (x + w) n.toNat rm ∧ modPow2Round (x + w) n.toNat rm < 2 ^ 256 then
          (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num (modPow2Round (x + w) n.toNat rm))) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  rw_model_private rshiftPow2RoundAddCompat => addShrQuot
  vm_simp [hs, unfoldPrivateRun, addShrQuot_ite_zero, rshiftPow2Round_ite_zero, modPow2Round_ite_zero,
    roundMode_ite_ok _ rm hrm, roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false,
    and_false, quiet_and, quiet_and']

/-! ## The shift a constant (`#`, `A93xyy`: `z` is `yy + 1`, arithops.cpp:342-345) -/

set_option maxHeartbeats 4000000 in
/-- `RSHIFT#MOD`, `RSHIFTR#MOD`, `RSHIFTC#MOD` (`A93Cyy`-`A93Eyy`; C++ `exec_shrmod`,
arithops.cpp:337, mode 2, result mode 3): the quotient, then the remainder. -/
@[vm_spec] theorem shrModConst (st : VmState) (s : Stack) (x rm : Int) (z : Nat)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.shrMod false false 3 rm false (some z)))) st =
      if -2 ^ 256 ≤ rshiftPow2Round x z rm ∧ rshiftPow2Round x z rm < 2 ^ 256 then
        if -2 ^ 256 ≤ modPow2Round x z rm ∧ modPow2Round x z rm < 2 ^ 256 then
          (.ok (), { st with
            stack := (s.push (.int (.num (rshiftPow2Round x z rm)))).push (.int (.num (modPow2Round x z rm))) })
        else (.error .intOv, { st with stack := s.push (.int (.num (rshiftPow2Round x z rm))) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false]

set_option maxHeartbeats 4000000 in
/-- `ADDRSHIFT#MOD`, `ADDRSHIFTR#MOD`, `ADDRSHIFTC#MOD` (`A930yy`-`A932yy`; C++ `exec_shrmod`,
arithops.cpp:337, mode 2, result mode 0, from global version 4): `addShrQuot`, then the remainder of
`x + w` (arithops.cpp:388-396). -/
@[vm_spec] theorem addShrModConst (st : VmState) (s : Stack) (x w rm : Int) (z : Nat)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hs : st.stack = (s.push (.int (.num x))).push (.int (.num w))) :
    ExceptT.run (execInstr (.arithExt (.shrMod false true 3 rm false (some z)))) st =
      if st.globalVersion < 4 then (.error .invOpcode, st)
      else if -2 ^ 256 ≤ addShrQuot x w z rm ∧ addShrQuot x w z rm < 2 ^ 256 then
        if -2 ^ 256 ≤ modPow2Round (x + w) z rm ∧ modPow2Round (x + w) z rm < 2 ^ 256 then
          (.ok (), { st with stack :=
            (s.push (.int (.num (addShrQuot x w z rm)))).push (.int (.num (modPow2Round (x + w) z rm))) })
        else (.error .intOv, { st with stack := s.push (.int (.num (addShrQuot x w z rm))) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  rw_model_private rshiftPow2RoundAddCompat => addShrQuot
  vm_simp [hs, unfoldPrivateRun, addShrQuot_ite_zero, rshiftPow2Round_ite_zero, modPow2Round_ite_zero,
    roundMode_ite_ok _ rm hrm, roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false,
    and_false]

end TvmLean.Spec

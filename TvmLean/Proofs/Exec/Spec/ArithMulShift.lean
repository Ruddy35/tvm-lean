import TvmLean.Proofs.Exec.Spec.ArithRound

/-!
# Specifications: the product shifted right with rounding (`exec_mulshrmod`)

In the format of `Proofs/Exec/Spec/ArithExt.lean`, the operands finite integers (`IntVal.num`): the
instructions of C++ `exec_mulshrmod` (arithops.cpp:520; opcodes `A9Ax` and the quiet `B7A9Ax`,
arithops.cpp:751, 766; `A9Bxyy` the shift a constant, arithops.cpp:753, which has no quiet form),
every rounding mode the decoder makes (`rm`: -1 down, 0 to nearest with ties up, 1 up):

* `MULRSHIFT`, `MULRSHIFTR`, `MULRSHIFTC` (`shrMod true false 1`), `MULMODPOW2`, `MULMODPOW2R`,
  `MULMODPOW2C` (`... 2`), `MULRSHIFTMOD`, `MULRSHIFTRMOD`, `MULRSHIFTCMOD` (`... 3`) and their
  quiet forms, the shift on the stack: `mulShrVar`, `mulModPow2Var`, `mulShrModVar`;
* `MULADDRSHIFTMOD`, `MULADDRSHIFTRMOD`, `MULADDRSHIFTCMOD` and their quiet forms
  (`shrMod true true 3`, from global version 4): `mulAddShrModVar`; `MULADDRSHIFT#MOD`,
  `MULADDRSHIFTR#MOD`, `MULADDRSHIFTC#MOD`: `mulAddShrModConst`.

The quotient is `rshiftPow2Round` and the remainder `modPow2Round` of `x * y` (`+ w`)
(`Spec/ArithRound.lean`: the operations of `Int` for each rounding mode). A shift from the stack
outside `0..256` is range_chk, from global version 13 NaN in the quiet forms (arithops.cpp:542,
554-560); a shift by 0 rounds down (arithops.cpp:548-550); a result that does not fit 257 bits is
int_ov, NaN if quiet; the results are pushed in order. The handler is run by `vm_simp` after its
conditions on the literals of the instruction are decided (`shift_pre`).
-/

namespace TvmLean.Spec

/- The proofs of this module are elaborated one after the other, as in `Spec/ArithExt.lean`. -/
set_option Elab.async false

set_option maxHeartbeats 4000000 in
/-- `MULRSHIFT`, `MULRSHIFTR`, `MULRSHIFTC` (`A9A4`-`A9A6`) and their quiet forms (`B7A9Ax`; C++
`exec_mulshrmod`, arithops.cpp:520, result mode 1): `rshiftPow2Round (x * y) n rm`. -/
@[vm_spec] theorem mulShrVar (st : VmState) (s : Stack) (x y n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shrMod true false 1 rm quiet none))) st =
      if (if quiet then st.globalVersion < 13 ∧ (n < 0 ∨ 256 < n) else n < 0 ∨ 256 < n) then
        (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.int (.num y)) })
      else if n < 0 ∨ 256 < n then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ rshiftPow2Round (x * y) n.toNat rm ∧ rshiftPow2Round (x * y) n.toNat rm < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (rshiftPow2Round (x * y) n.toNat rm))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false,
    quiet_or_and, quiet_or_and']

set_option maxHeartbeats 4000000 in
/-- `MULMODPOW2`, `MULMODPOW2R`, `MULMODPOW2C` (`A9A8`-`A9AA`) and their quiet forms (C++
`exec_mulshrmod`, arithops.cpp:520, result mode 2): `modPow2Round (x * y) n rm`. -/
@[vm_spec] theorem mulModPow2Var (st : VmState) (s : Stack) (x y n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shrMod true false 2 rm quiet none))) st =
      if (if quiet then st.globalVersion < 13 ∧ (n < 0 ∨ 256 < n) else n < 0 ∨ 256 < n) then
        (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.int (.num y)) })
      else if n < 0 ∨ 256 < n then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ modPow2Round (x * y) n.toNat rm ∧ modPow2Round (x * y) n.toNat rm < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (modPow2Round (x * y) n.toNat rm))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false,
    quiet_or_and, quiet_or_and']

set_option maxHeartbeats 4000000 in
/-- `MULRSHIFTMOD`, `MULRSHIFTRMOD`, `MULRSHIFTCMOD` (`A9AC`-`A9AE`) and their quiet forms (C++
`exec_mulshrmod`, arithops.cpp:520, result mode 3): the quotient, then the remainder. A quotient that
does not fit is int_ov with nothing pushed, a remainder that does not fit with the quotient pushed
(NaN for either if quiet). -/
@[vm_spec] theorem mulShrModVar (st : VmState) (s : Stack) (x y n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shrMod true false 3 rm quiet none))) st =
      if (if quiet then st.globalVersion < 13 ∧ (n < 0 ∨ 256 < n) else n < 0 ∨ 256 < n) then
        (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.int (.num y)) })
      else if n < 0 ∨ 256 < n then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ rshiftPow2Round (x * y) n.toNat rm ∧ rshiftPow2Round (x * y) n.toNat rm < 2 ^ 256 then
        if -2 ^ 256 ≤ modPow2Round (x * y) n.toNat rm ∧ modPow2Round (x * y) n.toNat rm < 2 ^ 256 then
          (.ok (), { st with
            stack :=
              (s.push (.int (.num (rshiftPow2Round (x * y) n.toNat rm)))).push
                (.int (.num (modPow2Round (x * y) n.toNat rm))) })
        else if quiet then
          (.ok (), { st with stack := (s.push (.int (.num (rshiftPow2Round (x * y) n.toNat rm)))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num (rshiftPow2Round (x * y) n.toNat rm))) })
      else if quiet then
        if -2 ^ 256 ≤ modPow2Round (x * y) n.toNat rm ∧ modPow2Round (x * y) n.toNat rm < 2 ^ 256 then
          (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num (modPow2Round (x * y) n.toNat rm))) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false,
    quiet_or_and, quiet_or_and']

set_option maxHeartbeats 4000000 in
/-- `MULADDRSHIFTMOD`, `MULADDRSHIFTRMOD`, `MULADDRSHIFTCMOD` (`A9A0`-`A9A2`) and their quiet
forms (C++ `exec_mulshrmod`, arithops.cpp:520, result mode 0, from global version 4,
arithops.cpp:530-536): the quotient and the remainder of `x * y + w`, as in `mulShrModVar`. -/
@[vm_spec] theorem mulAddShrModVar (st : VmState) (s : Stack) (x y w n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = (((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num w))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shrMod true true 3 rm quiet none))) st =
      if st.globalVersion < 4 then (.error .invOpcode, st)
      else if (if quiet then st.globalVersion < 13 ∧ (n < 0 ∨ 256 < n) else n < 0 ∨ 256 < n) then
        (.error .rangeChk, { st with stack := ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num w)) })
      else if n < 0 ∨ 256 < n then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ rshiftPow2Round (x * y + w) n.toNat rm ∧ rshiftPow2Round (x * y + w) n.toNat rm < 2 ^ 256 then
        if -2 ^ 256 ≤ modPow2Round (x * y + w) n.toNat rm ∧ modPow2Round (x * y + w) n.toNat rm < 2 ^ 256 then
          (.ok (), { st with
            stack :=
              (s.push (.int (.num (rshiftPow2Round (x * y + w) n.toNat rm)))).push
                (.int (.num (modPow2Round (x * y + w) n.toNat rm))) })
        else if quiet then
          (.ok (), { st with stack :=
            (s.push (.int (.num (rshiftPow2Round (x * y + w) n.toNat rm)))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num (rshiftPow2Round (x * y + w) n.toNat rm))) })
      else if quiet then
        if -2 ^ 256 ≤ modPow2Round (x * y + w) n.toNat rm ∧ modPow2Round (x * y + w) n.toNat rm < 2 ^ 256 then
          (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num (modPow2Round (x * y + w) n.toNat rm))) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false,
    quiet_or_and, quiet_or_and']

set_option maxHeartbeats 4000000 in
/-- `MULADDRSHIFT#MOD`, `MULADDRSHIFTR#MOD`, `MULADDRSHIFTC#MOD` (`A9B0yy`-`A9B2yy`, the shift
`z = yy + 1`; C++ `exec_mulshrmod`, arithops.cpp:520, mode 2, result mode 0, from global version 4):
the quotient and the remainder of `x * y + w`. -/
@[vm_spec] theorem mulAddShrModConst (st : VmState) (s : Stack) (x y w rm : Int) (z : Nat)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hz : z ≤ 256)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num w))) :
    ExceptT.run (execInstr (.arithExt (.shrMod true true 3 rm false (some z)))) st =
      if st.globalVersion < 4 then (.error .invOpcode, st)
      else if -2 ^ 256 ≤ rshiftPow2Round (x * y + w) z rm ∧ rshiftPow2Round (x * y + w) z rm < 2 ^ 256 then
        if -2 ^ 256 ≤ modPow2Round (x * y + w) z rm ∧ modPow2Round (x * y + w) z rm < 2 ^ 256 then
          (.ok (), { st with
            stack :=
              (s.push (.int (.num (rshiftPow2Round (x * y + w) z rm)))).push
                (.int (.num (modPow2Round (x * y + w) z rm))) })
        else (.error .intOv, { st with stack := s.push (.int (.num (rshiftPow2Round (x * y + w) z rm))) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false, hz,
    show ¬ (z : Int) > 256 by omega]

end TvmLean.Spec

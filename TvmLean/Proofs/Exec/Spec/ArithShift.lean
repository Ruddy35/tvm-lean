import TvmLean.Proofs.Exec.Spec.ArithRound

/-!
# Specifications: the right shifts with rounding, one result (`exec_shrmod`)

In the format of `Proofs/Exec/Spec/ArithExt.lean`, the operands finite integers (`IntVal.num`): the
instructions of C++ `exec_shrmod` (arithops.cpp:337; opcodes `A92x` and the quiet `B7A92x`,
arithops.cpp:747, 762; `A93xyy` the shift a constant, arithops.cpp:748, which has no quiet form)
with one result, every rounding mode the decoder makes (`rm`: -1 down, 0 to nearest with ties up,
1 up):

* `RSHIFTR`, `RSHIFTC` and `RSHIFT` of this encoding (`shrMod false false 1`), `MODPOW2`,
  `MODPOW2R`, `MODPOW2C` (`... 2`) and their quiet forms, the shift on the stack: `shrVar`,
  `modPow2Var`;
* the `#` forms `RSHIFT#`, `MODPOW2#` (each `R`, `C`): `shrConst`, `modPow2Const`.

The forms with two results (`RSHIFTMOD`, `ADDRSHIFTMOD`) are in `Spec/ArithShiftMod.lean`. The
quotient is `rshiftPow2Round` and the remainder `modPow2Round` (`Spec/ArithRound.lean`: the
operations of `Int` for each rounding mode). A shift from the stack outside `0..256` is range_chk
(arithops.cpp:363), from global version 14 NaN in the quiet forms (arithops.cpp:375-383); a result
that does not fit 257 bits is int_ov, NaN if quiet. The handler is run by `vm_simp` after its
conditions on the literals of the instruction are decided (`shift_pre`).
-/

namespace TvmLean.Spec

/- The proofs of this module are elaborated one after the other, as in `Spec/ArithExt.lean`. -/
set_option Elab.async false

/-! ## The shift on the stack -/

set_option maxHeartbeats 4000000 in
/-- `RSHIFTR`, `RSHIFTC`, `RSHIFT` (`A925`, `A926`, `A924`) and their quiet forms (`B7A92x`; C++
`exec_shrmod`, arithops.cpp:337, result mode 1): `rshiftPow2Round x n rm`. A shift outside
`0..256` is range_chk (arithops.cpp:363), from global version 14 NaN in the quiet forms
(arithops.cpp:375-383). -/
@[vm_spec] theorem shrVar (st : VmState) (s : Stack) (x n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shrMod false false 1 rm quiet none))) st =
      if 14 ≤ st.globalVersion then
        if (if quiet then False else n < 0 ∨ 256 < n) then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
        else if n < 0 ∨ 256 < n then
          if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
        else if -2 ^ 256 ≤ rshiftPow2Round x n.toNat rm ∧ rshiftPow2Round x n.toNat rm < 2 ^ 256 then
          (.ok (), { st with stack := s.push (.int (.num (rshiftPow2Round x n.toNat rm))) })
        else if quiet then (.ok (), { st with stack := s.push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if n < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 256 < n.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if -2 ^ 256 ≤ rshiftPow2Round x n.toNat rm ∧ rshiftPow2Round x n.toNat rm < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (rshiftPow2Round x n.toNat rm))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false, quiet_and,
    quiet_and']

set_option maxHeartbeats 4000000 in
/-- `MODPOW2`, `MODPOW2R`, `MODPOW2C` (`A928`-`A92A`) and their quiet forms (C++ `exec_shrmod`,
arithops.cpp:337, result mode 2): `modPow2Round x n rm`; the shift as in `shrVar`. -/
@[vm_spec] theorem modPow2Var (st : VmState) (s : Stack) (x n rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.shrMod false false 2 rm quiet none))) st =
      if 14 ≤ st.globalVersion then
        if (if quiet then False else n < 0 ∨ 256 < n) then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
        else if n < 0 ∨ 256 < n then
          if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
        else if -2 ^ 256 ≤ modPow2Round x n.toNat rm ∧ modPow2Round x n.toNat rm < 2 ^ 256 then
          (.ok (), { st with stack := s.push (.int (.num (modPow2Round x n.toNat rm))) })
        else if quiet then (.ok (), { st with stack := s.push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if n < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 256 < n.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if -2 ^ 256 ≤ modPow2Round x n.toNat rm ∧ modPow2Round x n.toNat rm < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (modPow2Round x n.toNat rm))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false, quiet_and,
    quiet_and']

/-! ## The shift a constant (`#`, `A93xyy`: `z` is `yy + 1`, arithops.cpp:342-345) -/

set_option maxHeartbeats 4000000 in
/-- `RSHIFT#`, `RSHIFTR#`, `RSHIFTC#` (`A934yy`-`A936yy`; C++ `exec_shrmod`, arithops.cpp:337,
mode 2, result mode 1): `rshiftPow2Round x z rm`. -/
@[vm_spec] theorem shrConst (st : VmState) (s : Stack) (x rm : Int) (z : Nat)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.shrMod false false 1 rm false (some z)))) st =
      if -2 ^ 256 ≤ rshiftPow2Round x z rm ∧ rshiftPow2Round x z rm < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (rshiftPow2Round x z rm))) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false]

set_option maxHeartbeats 4000000 in
/-- `MODPOW2#`, `MODPOW2R#`, `MODPOW2C#` (`A938yy`-`A93Ayy`; C++ `exec_shrmod`, arithops.cpp:337,
mode 2, result mode 2): `modPow2Round x z rm`. -/
@[vm_spec] theorem modPow2Const (st : VmState) (s : Stack) (x rm : Int) (z : Nat)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.shrMod false false 2 rm false (some z)))) st =
      if -2 ^ 256 ≤ modPow2Round x z rm ∧ modPow2Round x z rm < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (modPow2Round x z rm))) })
      else (.error .intOv, { st with stack := s }) := by
  shift_pre
  delta_private [shiftOutOfRange]
  vm_simp [hs, unfoldPrivateRun, rshiftPow2Round_ite_zero, modPow2Round_ite_zero, roundMode_ite_ok _ rm hrm,
    roundMode_prop_ok rm hrm, intPow2, Int.add_zero, not_true_eq_false, or_false, and_false]

end TvmLean.Spec

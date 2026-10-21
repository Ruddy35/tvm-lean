import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: integer arithmetic and comparisons

In the format of `Proofs/Exec/Spec/Stack.lean`. The operands are finite integers (`IntVal.num`);
a result that does not fit 257 bits (`-2^256 ≤ r < 2^256`) is int_ov, the operands popped
(non-quiet instructions, C++ `push_int_quiet(..., false)`).
-/

namespace TvmLean.Spec

/-- `ADD` (C++ `exec_add`, arithops.cpp). -/
@[vm_spec] theorem add (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .add) st =
      if -2 ^ 256 ≤ x + y ∧ x + y < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x + y))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `SUB` (C++ `exec_sub`). -/
@[vm_spec] theorem sub (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .sub) st =
      if -2 ^ 256 ≤ x - y ∧ x - y < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x - y))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `INC` (C++ `exec_inc`). -/
@[vm_spec] theorem inc (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .inc) st =
      if -2 ^ 256 ≤ x + 1 ∧ x + 1 < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x + 1))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `DEC` (C++ `exec_dec`). -/
@[vm_spec] theorem dec (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .dec) st =
      if -2 ^ 256 ≤ x - 1 ∧ x - 1 < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x - 1))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `EQUAL` (C++ `exec_cmp` with mode `0x878`): `-1` if `x = y`, else `0`. -/
@[vm_spec] theorem equal (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .equal) st =
      (.ok (), { st with stack := s.push (.int (.num (if x = y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `LESS` (C++ `exec_cmp` with mode `0x887`): `-1` if `x < y`, else `0`. -/
@[vm_spec] theorem less (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .less) st =
      (.ok (), { st with stack := s.push (.int (.num (if x < y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `LEQ` (C++ `exec_cmp` with mode `0x877`): `-1` if `x ≤ y`, else `0`. -/
@[vm_spec] theorem leq (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .leq) st =
      (.ok (), { st with stack := s.push (.int (.num (if x ≤ y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `GREATER` (C++ `exec_cmp` with mode `0x788`): `-1` if `x > y`, else `0`. -/
@[vm_spec] theorem greater (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .greater) st =
      (.ok (), { st with stack := s.push (.int (.num (if x > y then -1 else 0))) }) := by
  vm_simp [hs]

end TvmLean.Spec

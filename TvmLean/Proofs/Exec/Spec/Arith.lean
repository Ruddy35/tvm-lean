import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: integer arithmetic and comparisons

In the format of `Proofs/Exec/Spec/Stack.lean`. The operands are finite integers (`IntVal.num`);
a result that does not fit 257 bits (`-2^256 ≤ r < 2^256`) is int_ov, the operands popped
(non-quiet instructions, C++ `push_int_quiet(..., false)`). `NOT` is computed by the model on the
257 bits of two's complement; `bitsToIntSignedTwos_not` states it as `-n - 1`.
-/

namespace TvmLean

/-- The bits of `m` (below `2^k`) inverted are the bits of `2^k - 1 - m`. -/
theorem natToBits_map_not (m k : Nat) (hm : m < 2 ^ k) :
    (natToBits m k).map (fun b => !b) = natToBits (2 ^ k - 1 - m) k := by
  apply Array.ext
  · simp [natToBits]
  · intro i h1 h2
    simp only [natToBits, Array.size_map, Array.size_ofFn] at h1 h2
    simp only [natToBits, Array.getElem_map, Array.getElem_ofFn]
    have hj : k - 1 - i < k := by omega
    have hv : (2 ^ k - 1 - m) = (~~~ (BitVec.ofNat k m)).toNat := by
      rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
    rw [hv, BitVec.testBit_toNat, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
    simp [hj]

set_option exponentiation.threshold 260 in
/-- The two's complement of `n` on 257 bits (`intToBitsTwos`) for an `n` that fits. -/
theorem intToBitsTwos_257 (n : Int) (h : -2 ^ 256 ≤ n ∧ n < 2 ^ 256) :
    intToBitsTwos n 257 = .ok (natToBits (if 0 ≤ n then n.toNat else 2 ^ 257 - (-n).toNat) 257) := by
  have hh : intPow2 256 = 2 ^ 256 := rfl
  have hm : (1 <<< 257 : Nat) = 2 ^ 257 := by decide
  unfold intToBitsTwos
  simp only [hh, hm, Nat.add_one_sub_one]
  have h1 : ¬ (n < -2 ^ 256 ∨ n ≥ 2 ^ 256) := by omega
  by_cases h2 : 0 ≤ n
  · simp [h2]; rw [if_neg (by omega)]; rfl
  · simp [h2]; rw [if_neg (by omega)]; rfl

set_option exponentiation.threshold 260 in
/-- `NOT` of an integer that fits 257 bits (C++ `exec_not`): `-n - 1`. -/
theorem bitsToIntSignedTwos_not (n : Int) (h : -2 ^ 256 ≤ n ∧ n < 2 ^ 256) :
    bitsToIntSignedTwos ((natToBits (if 0 ≤ n then n.toNat else 2 ^ 257 - (-n).toNat) 257).map (fun b => !b)) =
      -n - 1 := by
  have hlt : (if 0 ≤ n then n.toNat else 2 ^ 257 - (-n).toNat) < 2 ^ 257 := by split <;> omega
  rw [natToBits_map_not _ _ hlt]
  generalize hv : 2 ^ 257 - 1 - (if 0 ≤ n then n.toNat else 2 ^ 257 - (-n).toNat) = v
  have hv' : v < 2 ^ 257 := by omega
  unfold bitsToIntSignedTwos
  simp only [natToBits_size]
  have hb : (natToBits v 257)[0]! = v.testBit 256 := by
    simp [natToBits]
  rw [hb, bitsToNat_natToBits, Nat.mod_eq_of_lt hv', Nat.testBit_eq_decide_div_mod_eq]
  have hs : (1 <<< 257 : Nat) = 2 ^ 257 := by decide
  by_cases h2 : 0 ≤ n
  · rw [if_pos h2] at hv
    have : v / 2 ^ 256 % 2 = 1 := by omega
    simp [this, hs]; omega
  · rw [if_neg h2] at hv
    have : v / 2 ^ 256 % 2 = 0 := by omega
    simp [this]; omega

namespace Spec

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

set_option exponentiation.threshold 260 in
/-- `NOT` (C++ `exec_not`, arithops.cpp) of an integer that fits 257 bits: `-n - 1`. -/
@[vm_spec] theorem not_ (st : VmState) (s : Stack) (n : Int) (h : -2 ^ 256 ≤ n ∧ n < 2 ^ 256)
    (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .not_) st = (.ok (), { st with stack := s.push (.int (.num (-n - 1))) }) := by
  have h1 := intToBitsTwos_257 n h
  have h2 := bitsToIntSignedTwos_not n h
  vm_simp [hs, h1, h2]

end Spec

end TvmLean

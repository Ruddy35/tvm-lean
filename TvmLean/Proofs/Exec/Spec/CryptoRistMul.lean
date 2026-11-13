import TvmLean.Proofs.Exec.Spec.Crypto

/-!
# Specifications: `RIST255_MUL`, `RIST255_QMUL`

`RIST255_MUL` (C++ `exec_ristretto255_mul`, tonops.cpp) on the stack `s x n`: the scalar `n mod l`
(`rist255L`), `rist255_mul_gas_price` charged (out of gas at once), then:

* the scalar not 0 (`Spec.rist255Mul_ne`): from version 14 a point 0 gives 0; else the point must be
  in `0 .. 2^256 - 1` (`exportUInt256BE_num`), and the encoding of the product is pushed
  (`rist255Mul`: `Ristretto255.mul` of the scalar's 32 bytes, little-endian, and the point's), range_chk
  if the library refuses (an invalid point, the identity) or the point is out of range;
* the scalar 0 (`Spec.rist255Mul_zero`): 0 is pushed; from version 14 a point other than 0 that is
  not a valid encoding is range_chk.

`RIST255_QMUL` (`Spec.rist255Qmul_ne`, `Spec.rist255Qmul_zero`): the same cases, the result pushed
with -1, a failure pushes 0. The operands are integers here, so the TVM 14 refusal of NaN does not
apply. The product is the irreducible term `rist255Mul n x` and the check of the point
`Ristretto255.isValid` of its bytes: a run keeps both as terms.

The handler tests the scalar and the point against 0 with `match`es on `.num 0`, which do not reduce
on a symbolic value; the two lemmas of each instruction split on `n % l = 0`, so each applies
where the run decides that (a known scalar; else the handler runs).
-/

namespace TvmLean

/-- The result of `RIST255_MUL` and `RIST255_QMUL` on the scalar `n` (below the order of the group) and
the point `x` (C++ `crypto_scalarmult_ristretto255` of libsodium): the encoding of the product as an
integer, or none if the library refuses (the point is not a valid encoding, or the product is the
identity): `Ristretto255.mul` of the 32 bytes of `n`, little-endian, and the 32 bytes of `x`.
Irreducible: symbolic execution keeps it as a term (unfolded, a step would evaluate the product of
a known scalar by a point it does not know). -/
@[irreducible] def rist255Mul (n x : Nat) : Option Nat :=
  (Ristretto255.mul (natToBytesBEFixed n 32).reverse (natToBytesBEFixed x 32)).map bytesToNatBE

theorem rist255Mul_eq (n x : Nat) :
    rist255Mul n x = (Ristretto255.mul (natToBytesBEFixed n 32).reverse (natToBytesBEFixed x 32)).map bytesToNatBE := by
  unfold rist255Mul; rfl

namespace Spec

set_option maxHeartbeats 4000000

/-- `RIST255_MUL` on the stack `s x n` when `n mod l` is not 0: from version 14 a point 0 gives 0;
else the encoding of the product of the point `x` (32 bytes) by the scalar (32 bytes, little-endian),
range_chk if the library refuses or `x` is not in `0 .. 2^256 - 1`. -/
@[vm_spec] theorem rist255Mul_ne (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) (hn : n % rist255L ≠ 0) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Mul))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255MulGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255MulGasPrice })
      else if 14 ≤ st.globalVersion ∧ x = 0 then
        (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255MulGasPrice })
      else if 0 ≤ x ∧ x.toNat < 2 ^ 256 then
        match TvmLean.rist255Mul (n % rist255L).toNat x.toNat with
        | some r => (.ok (), { st with stack := s.push (.int (.num r)),
                                       gas := st.gas.consume rist255MulGasPrice })
        | none => (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255MulGasPrice })
      else (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255MulGasPrice }) := by
  have hn0 : 0 ≤ n % rist255L := Int.emod_nonneg _ (by rw [rist255L_eq]; decide)
  have hn1 : n % rist255L < rist255L := Int.emod_lt_of_pos _ (by rw [rist255L_eq]; decide)
  vm_simp [hs, VmState.consumeGas, intValMod, exportUInt256BE?, pushUInt256BE]
  generalize n % rist255L = m at hn0 hn1 hn ⊢
  rw [rist255L_eq] at hn1
  rw [exportUInt256BE_num m, if_pos (show 0 ≤ m ∧ m.toNat < 2 ^ 256 by omega), exportUInt256BE_num x]
  rw [TvmLean.rist255Mul_eq]
  -- the library and the point's bytes kept as variables: with the point 0 the kernel would
  -- otherwise unfold `natToBytesBEFixed 0 32` (deep recursion)
  generalize Ristretto255.mul = f
  generalize Ristretto255.isValid = v
  generalize natToBytesBEFixed x.toNat 32 = z
  -- the handler's `match`es on `.num 0` reduce by `simp` with `hn` and `hx`
  by_cases hx : x = 0
  · subst hx
    by_cases hv : 14 ≤ st.globalVersion
    · simp [hn, hv]
    · simp [hn, hv]
      cases f (natToBytesBEFixed m.toNat 32).reverse z <;> vm_simp [Option.map]
  · simp [hn, hx]
    by_cases hc : 0 ≤ x ∧ x < 115792089237316195423570985008687907853269984665640564039457584007913129639936
    · simp only [hc, and_self, if_true]
      cases f (natToBytesBEFixed m.toNat 32).reverse z <;> vm_simp [Option.map]
    · simp only [hc, if_false]
      vm_simp

/-- `RIST255_MUL` on the stack `s x n` when `n mod l` is 0: 0 is pushed; from version 14 a point
other than 0 that is not a valid encoding is range_chk (C++ checks the point on this fast path from
version 14 only). -/
@[vm_spec] theorem rist255Mul_zero (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) (hn : n % rist255L = 0) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Mul))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255MulGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255MulGasPrice })
      else if 14 ≤ st.globalVersion ∧ x ≠ 0 ∧
          ¬((0 ≤ x ∧ x.toNat < 2 ^ 256) ∧ Ristretto255.isValid (natToBytesBEFixed x.toNat 32) = true) then
        (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255MulGasPrice })
      else (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255MulGasPrice }) := by
  vm_simp [hs, VmState.consumeGas, intValMod, exportUInt256BE?, pushUInt256BE, hn]
  rw [exportUInt256BE_num x]
  generalize Ristretto255.mul = f
  generalize Ristretto255.isValid = v
  generalize natToBytesBEFixed x.toNat 32 = z
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [hx]
    by_cases h0 : 0 ≤ x <;> by_cases hL : x.toNat < 2 ^ 256 <;> simp [hx, h0, hL]

/-- `RIST255_QMUL` on the stack `s x n` when `n mod l` is not 0: as `RIST255_MUL`
(`Spec.rist255Mul_ne`), the result pushed with -1; a failure pushes 0. -/
@[vm_spec] theorem rist255Qmul_ne (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) (hn : n % rist255L ≠ 0) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Qmul))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255MulGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255MulGasPrice })
      else if 14 ≤ st.globalVersion ∧ x = 0 then
        (.ok (), { st with stack := (s.push (.int (.num 0))).push (.int (.num (-1))),
                           gas := st.gas.consume rist255MulGasPrice })
      else if 0 ≤ x ∧ x.toNat < 2 ^ 256 then
        match TvmLean.rist255Mul (n % rist255L).toNat x.toNat with
        | some r => (.ok (), { st with stack := (s.push (.int (.num r))).push (.int (.num (-1))),
                                       gas := st.gas.consume rist255MulGasPrice })
        | none => (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255MulGasPrice })
      else (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255MulGasPrice }) := by
  have hn0 : 0 ≤ n % rist255L := Int.emod_nonneg _ (by rw [rist255L_eq]; decide)
  have hn1 : n % rist255L < rist255L := Int.emod_lt_of_pos _ (by rw [rist255L_eq]; decide)
  vm_simp [hs, VmState.consumeGas, intValMod, exportUInt256BE?, pushUInt256BE]
  generalize n % rist255L = m at hn0 hn1 hn ⊢
  rw [rist255L_eq] at hn1
  rw [exportUInt256BE_num m, if_pos (show 0 ≤ m ∧ m.toNat < 2 ^ 256 by omega), exportUInt256BE_num x]
  rw [TvmLean.rist255Mul_eq]
  generalize Ristretto255.mul = f
  generalize Ristretto255.isValid = v
  generalize natToBytesBEFixed x.toNat 32 = z
  by_cases hx : x = 0
  · subst hx
    by_cases hv : 14 ≤ st.globalVersion
    · simp [hn, hv]
    · simp [hn, hv]
      cases f (natToBytesBEFixed m.toNat 32).reverse z <;> vm_simp [Option.map]
  · simp [hn, hx]
    by_cases hc : 0 ≤ x ∧ x < 115792089237316195423570985008687907853269984665640564039457584007913129639936
    · simp only [hc, and_self, if_true]
      cases f (natToBytesBEFixed m.toNat 32).reverse z <;> vm_simp [Option.map]
    · simp only [hc, if_false]
      vm_simp

/-- `RIST255_QMUL` on the stack `s x n` when `n mod l` is 0: 0 and -1 are pushed; from version 14
a point other than 0 that is not a valid encoding gives 0. -/
@[vm_spec] theorem rist255Qmul_zero (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) (hn : n % rist255L = 0) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Qmul))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255MulGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255MulGasPrice })
      else if 14 ≤ st.globalVersion ∧ x ≠ 0 ∧
          ¬((0 ≤ x ∧ x.toNat < 2 ^ 256) ∧ Ristretto255.isValid (natToBytesBEFixed x.toNat 32) = true) then
        (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255MulGasPrice })
      else (.ok (), { st with stack := (s.push (.int (.num 0))).push (.int (.num (-1))),
                              gas := st.gas.consume rist255MulGasPrice }) := by
  vm_simp [hs, VmState.consumeGas, intValMod, exportUInt256BE?, pushUInt256BE, hn]
  rw [exportUInt256BE_num x]
  generalize Ristretto255.mul = f
  generalize Ristretto255.isValid = v
  generalize natToBytesBEFixed x.toNat 32 = z
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [hx]
    by_cases h0 : 0 ≤ x <;> by_cases hL : x.toNat < 2 ^ 256 <;> simp [hx, h0, hL]

end Spec

end TvmLean

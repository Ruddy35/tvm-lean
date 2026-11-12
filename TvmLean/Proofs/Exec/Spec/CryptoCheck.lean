import TvmLean.Proofs.Exec.Spec.Crypto

/-!
# Specifications: `BLS_VERIFY`, the ristretto255 operations on encodings, `P256_CHKSIGNU`

In the format of `Proofs/Exec/Spec/Crypto.lean`: an integer is read as the 32 bytes of an encoding
(`exportUInt256BE_num`: range_chk unless it is in `0 .. 2^256 - 1`), the results are the model's
functions of those bytes (`Ristretto255.isValid`, `add`, `sub`, `fromHash`, `P256.verify`), kept as
terms; the gas of an operation (C++ tonops.cpp) is charged where the handler charges it (out of gas
at once):

* `RIST255_VALIDATE` (C++ `exec_ristretto255_validate`): range_chk unless the integer encodes a
  point; `RIST255_QVALIDATE`: -1 or 0;
* `RIST255_ADD`, `RIST255_SUB` (C++ `exec_ristretto255_add`, `exec_ristretto255_sub`): the encoding of
  the sum (difference), range_chk if the library refuses; `RIST255_QADD`, `RIST255_QSUB`: it and
  -1, or 0 (also for an integer that is not an encoding);
* `RIST255_FROMHASH` (C++ `exec_ristretto255_from_hash`): the encoding of the point of the 64 bytes of
  two integers;
* `P256_CHKSIGNU` (C++ `exec_p256_chksign` of a hash): the check of the 64 bytes of the signature and
  the 33 bytes of the key against the 32 bytes of the hash, -1 or 0.* `BLS_VERIFY` (C++ `exec_bls_verify`): the gas charged, then the 96 bytes of the signature, the
  bytes of the message (a whole number of them, `sliceToFullBytes_eq`), the 48 bytes of the key;
  `Bls12381.verify`, -1 or 0.
-/

namespace TvmLean.Spec

set_option maxHeartbeats 4000000

/-- `RIST255_VALIDATE` on the stack `s x`. -/
@[vm_spec] theorem rist255Validate (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Validate))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255ValidateGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255ValidateGasPrice })
      else if 0 ≤ x ∧ x.toNat < 2 ^ 256 then
        if Ristretto255.isValid (natToBytesBEFixed x.toNat 32) then
          (.ok (), { st with stack := s, gas := st.gas.consume rist255ValidateGasPrice })
        else (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255ValidateGasPrice })
      else (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255ValidateGasPrice }) := by
  by_cases hx : 0 ≤ x ∧ x.toNat < 2 ^ 256 <;> vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hx]

/-- `RIST255_QVALIDATE` on the stack `s x`. -/
@[vm_spec] theorem rist255Qvalidate (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Qvalidate))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255ValidateGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255ValidateGasPrice })
      else if 0 ≤ x ∧ x.toNat < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (if Ristretto255.isValid (natToBytesBEFixed x.toNat 32) then -1 else 0))),
                           gas := st.gas.consume rist255ValidateGasPrice })
      else (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255ValidateGasPrice }) := by
  by_cases hx : 0 ≤ x ∧ x.toNat < 2 ^ 256 <;>
    vm_simp [hs, VmState.consumeGas, exportUInt256BE?, exportUInt256BE_num, hx]

/-- `RIST255_ADD` on the stack `s x y`. -/
@[vm_spec] theorem rist255Add (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Add))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255AddGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255AddGasPrice })
      else if 0 ≤ x ∧ x.toNat < 2 ^ 256 then
        if 0 ≤ y ∧ y.toNat < 2 ^ 256 then
          match Ristretto255.add (natToBytesBEFixed x.toNat 32) (natToBytesBEFixed y.toNat 32) with
          | some r => (.ok (), { st with stack := s.push (.int (.num (bytesToNatBE r : Nat))),
                                         gas := st.gas.consume rist255AddGasPrice })
          | none => (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255AddGasPrice })
        else (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255AddGasPrice })
      else (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255AddGasPrice }) := by
  by_cases hx : 0 ≤ x ∧ x.toNat < 2 ^ 256
  · by_cases hy : 0 ≤ y ∧ y.toNat < 2 ^ 256
    · cases h : Ristretto255.add (natToBytesBEFixed x.toNat 32) (natToBytesBEFixed y.toNat 32) <;>
        vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hx, hy, h, pushUInt256BE]
    · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hx, hy]
  · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hx]

/-- `RIST255_QADD` on the stack `s x y`. -/
@[vm_spec] theorem rist255Qadd (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Qadd))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255AddGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255AddGasPrice })
      else if 0 ≤ x ∧ x.toNat < 2 ^ 256 then
        if 0 ≤ y ∧ y.toNat < 2 ^ 256 then
          match Ristretto255.add (natToBytesBEFixed x.toNat 32) (natToBytesBEFixed y.toNat 32) with
          | some r => (.ok (), { st with stack := (s.push (.int (.num (bytesToNatBE r : Nat)))).push (.int (.num (-1))),
                                         gas := st.gas.consume rist255AddGasPrice })
          | none => (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255AddGasPrice })
        else (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255AddGasPrice })
      else (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255AddGasPrice }) := by
  by_cases hx : 0 ≤ x ∧ x.toNat < 2 ^ 256
  · by_cases hy : 0 ≤ y ∧ y.toNat < 2 ^ 256
    · cases h : Ristretto255.add (natToBytesBEFixed x.toNat 32) (natToBytesBEFixed y.toNat 32) <;>
        vm_simp [hs, VmState.consumeGas, exportUInt256BE?, exportUInt256BE_num, hx, hy, h, pushUInt256BE]
    · vm_simp [hs, VmState.consumeGas, exportUInt256BE?, exportUInt256BE_num, hx, hy]
  · vm_simp [hs, VmState.consumeGas, exportUInt256BE?, exportUInt256BE_num, hx]

/-- `RIST255_SUB` on the stack `s x y`. -/
@[vm_spec] theorem rist255Sub (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Sub))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255AddGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255AddGasPrice })
      else if 0 ≤ x ∧ x.toNat < 2 ^ 256 then
        if 0 ≤ y ∧ y.toNat < 2 ^ 256 then
          match Ristretto255.sub (natToBytesBEFixed x.toNat 32) (natToBytesBEFixed y.toNat 32) with
          | some r => (.ok (), { st with stack := s.push (.int (.num (bytesToNatBE r : Nat))),
                                         gas := st.gas.consume rist255AddGasPrice })
          | none => (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255AddGasPrice })
        else (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255AddGasPrice })
      else (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255AddGasPrice }) := by
  by_cases hx : 0 ≤ x ∧ x.toNat < 2 ^ 256
  · by_cases hy : 0 ≤ y ∧ y.toNat < 2 ^ 256
    · cases h : Ristretto255.sub (natToBytesBEFixed x.toNat 32) (natToBytesBEFixed y.toNat 32) <;>
        vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hx, hy, h, pushUInt256BE]
    · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hx, hy]
  · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hx]

/-- `RIST255_QSUB` on the stack `s x y`. -/
@[vm_spec] theorem rist255Qsub (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255Qsub))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255AddGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255AddGasPrice })
      else if 0 ≤ x ∧ x.toNat < 2 ^ 256 then
        if 0 ≤ y ∧ y.toNat < 2 ^ 256 then
          match Ristretto255.sub (natToBytesBEFixed x.toNat 32) (natToBytesBEFixed y.toNat 32) with
          | some r => (.ok (), { st with stack := (s.push (.int (.num (bytesToNatBE r : Nat)))).push (.int (.num (-1))),
                                         gas := st.gas.consume rist255AddGasPrice })
          | none => (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255AddGasPrice })
        else (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255AddGasPrice })
      else (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255AddGasPrice }) := by
  by_cases hx : 0 ≤ x ∧ x.toNat < 2 ^ 256
  · by_cases hy : 0 ≤ y ∧ y.toNat < 2 ^ 256
    · cases h : Ristretto255.sub (natToBytesBEFixed x.toNat 32) (natToBytesBEFixed y.toNat 32) <;>
        vm_simp [hs, VmState.consumeGas, exportUInt256BE?, exportUInt256BE_num, hx, hy, h, pushUInt256BE]
    · vm_simp [hs, VmState.consumeGas, exportUInt256BE?, exportUInt256BE_num, hx, hy]
  · vm_simp [hs, VmState.consumeGas, exportUInt256BE?, exportUInt256BE_num, hx]

/-- `RIST255_FROMHASH` on the stack `s x1 x2`. -/
@[vm_spec] theorem rist255FromHash (st : VmState) (s : Stack) (x1 x2 : Int)
    (hs : st.stack = (s.push (.int (.num x1))).push (.int (.num x2))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255FromHash))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255FromHashGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255FromHashGasPrice })
      else if 0 ≤ x1 ∧ x1.toNat < 2 ^ 256 then
        if 0 ≤ x2 ∧ x2.toNat < 2 ^ 256 then
          (.ok (), { st with stack := s.push (.int (.num (bytesToNatBE
                       (Ristretto255.fromHash (natToBytesBEFixed x1.toNat 32 ++ natToBytesBEFixed x2.toNat 32)) : Nat))),
                             gas := st.gas.consume rist255FromHashGasPrice })
        else (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255FromHashGasPrice })
      else (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255FromHashGasPrice }) := by
  by_cases h1 : 0 ≤ x1 ∧ x1.toNat < 2 ^ 256
  · by_cases h2 : 0 ≤ x2 ∧ x2.toNat < 2 ^ 256
    · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, h1, h2, pushUInt256BE]
    · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, h1, h2]
  · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, h1]

/-- `P256_CHKSIGNU` on the stack `s h sig key`. -/
@[vm_spec] theorem p256ChkSignU (st : VmState) (s : Stack) (h : Int) (sig key : Slice)
    (hs : st.stack = ((s.push (.int (.num h))).push (.slice sig)).push (.slice key)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .p256ChkSignU))) st =
      if 0 ≤ h ∧ h.toNat < 2 ^ 256 then
        if sig.haveBits 512 then
          if key.haveBits 264 then
            if ({ st with stack := s, gas := st.gas.consume p256ChksgnGasPrice } : VmState).gasExhaustedNow then
              (.error .outOfGas, { st with stack := s, gas := st.gas.consume p256ChksgnGasPrice })
            else
              (.ok (), { st with stack := s.push (.int (.num (if P256.verify (natToBytesBEFixed h.toNat 32)
                             (bitStringToBytesBE (key.readBits 264)) (bitStringToBytesBE (sig.readBits 512)) then -1 else 0))),
                                 gas := st.gas.consume p256ChksgnGasPrice })
          else (.error .cellUnd, { st with stack := s })
        else (.error .cellUnd, { st with stack := s })
      else (.error .rangeChk, { st with stack := s }) := by
  by_cases h1 : 0 ≤ h ∧ h.toNat < 2 ^ 256
  · by_cases h2 : sig.haveBits 512 = true
    · by_cases h3 : key.haveBits 264 = true <;>
        vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, prefetchBytesCellUnd_eq, h1, h2, h3]
    · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, prefetchBytesCellUnd_eq, h1, h2]
  · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, h1]

/-- The bytes of a slice of whole bytes (`sliceToFullBytes`, of
`BLS_VERIFY`'s message): cell_und unless its bits are a whole number of bytes. -/
theorem sliceToFullBytes_eq (sl : Slice) : sliceToFullBytes sl =
    if sl.bitsRemaining % 8 = 0 then
      if sl.haveBits (sl.bitsRemaining / 8 * 8) then .ok (bitStringToBytesBE (sl.readBits (sl.bitsRemaining / 8 * 8)))
      else .error .cellUnd
    else .error .cellUnd := by
  unfold sliceToFullBytes
  rw [prefetchBytesCellUnd_eq]
  by_cases h : sl.bitsRemaining % 8 = 0
  · simp only [h, bne_self_eq_false, Bool.false_eq_true, if_false, if_true]; rfl
  · have h' : (sl.bitsRemaining % 8 != 0) = true := by simp [h]
    simp only [h', h, if_true, if_false]; rfl

/-- `BLS_VERIFY` on the stack `s pub msg sig`: the gas charged, then the 96 bytes of the signature,
the bytes of the message (a whole number), the 48 bytes of the key; -1 or 0. -/
@[vm_spec] theorem blsVerify (st : VmState) (s : Stack) (pub msg sig : Slice)
    (hs : st.stack = ((s.push (.slice pub)).push (.slice msg)).push (.slice sig)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsVerify))) st =
      if ({ st with gas := st.gas.consume blsVerifyGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsVerifyGasPrice })
      else if sig.haveBits 768 then
        if msg.bitsRemaining % 8 = 0 then
          if msg.haveBits (msg.bitsRemaining / 8 * 8) then
            if pub.haveBits 384 then
              (.ok (), { st with stack := s.push (.int (.num (if Bls12381.verify (bitStringToBytesBE (pub.readBits 384))
                           (bitStringToBytesBE (msg.readBits (msg.bitsRemaining / 8 * 8)))
                           (bitStringToBytesBE (sig.readBits 768)) then -1 else 0))),
                                 gas := st.gas.consume blsVerifyGasPrice })
            else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsVerifyGasPrice })
          else (.error .cellUnd, { st with stack := s.push (.slice pub), gas := st.gas.consume blsVerifyGasPrice })
        else (.error .cellUnd, { st with stack := s.push (.slice pub), gas := st.gas.consume blsVerifyGasPrice })
      else (.error .cellUnd, { st with stack := (s.push (.slice pub)).push (.slice msg),
                                       gas := st.gas.consume blsVerifyGasPrice }) := by
  by_cases h1 : sig.haveBits 768 = true
  · by_cases h2 : msg.bitsRemaining % 8 = 0
    · by_cases h3 : msg.haveBits (msg.bitsRemaining / 8 * 8) = true
      · by_cases h4 : pub.haveBits 384 = true <;>
          vm_simp [hs, VmState.consumeGas, prefetchBytesCellUnd_eq, sliceToFullBytes_eq, h1, h2, h3, h4]
      · vm_simp [hs, VmState.consumeGas, prefetchBytesCellUnd_eq, sliceToFullBytes_eq, h1, h2, h3]
    · vm_simp [hs, VmState.consumeGas, prefetchBytesCellUnd_eq, sliceToFullBytes_eq, h1, h2]
  · vm_simp [hs, VmState.consumeGas, prefetchBytesCellUnd_eq, h1]

end TvmLean.Spec

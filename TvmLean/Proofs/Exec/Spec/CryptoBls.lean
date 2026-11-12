import TvmLean.Proofs.Exec.Spec.Crypto

/-!
# Specifications: `HASHBU`, `RIST255_PUSHL`, and the BLS12-381 operations on one or two points

In the format of `Proofs/Exec/Spec/Crypto.lean`: nothing is computed, the results are the model's
functions of the bytes read (`Bls12381.g1Add`, ..., kept as terms; the bytes of a point the first
48 (G1) or 96 (G2) bytes of a slice, `prefetchBytesCellUnd_eq`, cell_und if it is shorter). The
gas of an operation (C++ bls.cpp, tonops.cpp) is charged before its points are read (out of gas at
once); a point the library refuses is unknown (C++ `VmError{Excno::unknown}`).

* `HASHBU` (C++ `exec_builder_hash`, cellops.cpp): the hash of the builder finished (not charged;
  cell_ov above the maximal depth), `cellHash`;
* `RIST255_PUSHL`, `BLS_PUSHR`: the orders `l` and `r`; `BLS_G1_ZERO`, `BLS_G2_ZERO`: the encodings
  of zero;
* `BLS_G1_ISZERO`, `BLS_G2_ISZERO` (not charged), `BLS_G1_INGROUP`, `BLS_G2_INGROUP`: -1 or 0;
* `BLS_G1_NEG`, `BLS_G2_NEG`, `BLS_MAP_TO_G1`, `BLS_MAP_TO_G2`: a point of a point (of a field
  element);
* `BLS_G1_ADD`, `BLS_G1_SUB`, `BLS_G2_ADD`, `BLS_G2_SUB` (stk_und below two values), `BLS_G1_MUL`,
  `BLS_G2_MUL` (a point and an integer, int_ov for NaN).
-/

namespace TvmLean.Spec

set_option maxHeartbeats 4000000

/-- `HASHBU` on the stack `s b`. -/
@[vm_spec] theorem hashbu (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellExt .hashbu)) st =
      if Cell.refsDepthOk b.refs then
        if cellHash b.finalize < 2 ^ 256 then
          (.ok (), { st with stack := s.push (.int (.num (cellHash b.finalize))) })
        else (.error .intOv, { st with stack := s })
      else (.error .cellOv, { st with stack := s }) := by
  simp only [cellHash_eq]
  vm_simp [hs, VM.checkNewCellDepth]
  generalize bytesToNatBE b.finalize.hashBytes = x
  split
  · by_cases hx : x < 2 ^ 256
    · rw [if_pos (by omega), if_pos hx]
    · rw [if_neg (by omega), if_neg hx]
  · rfl

/-- `RIST255_PUSHL`: the order `l` of ristretto255. -/
@[vm_spec] theorem rist255PushL (st : VmState) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255PushL))) st =
      (.ok (), { st with stack := st.stack.push (.int (.num rist255L)) }) := by
  vm_simp

/-- `BLS_PUSHR`: the order `r` of the BLS12-381 groups. -/
@[vm_spec] theorem blsPushR (st : VmState) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsPushR))) st =
      (.ok (), { st with stack := st.stack.push (.int (.num blsR)) }) := by
  vm_simp

/-- `BLS_G1_ZERO`: the encoding of zero of G1. -/
@[vm_spec] theorem blsG1Zero (st : VmState) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG1Zero))) st =
      (.ok (), { st with stack := st.stack.push (.slice (sliceOfByteArray (ByteArray.mk Bls12381.g1ZeroBytes))) }) := by
  vm_simp

/-- `BLS_G1_ISZERO` on the stack `s a`. -/
@[vm_spec] theorem blsG1IsZero (st : VmState) (s : Stack) (a : Slice) (hs : st.stack = s.push (.slice a)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG1IsZero))) st =
      if a.haveBits 384 then
        (.ok (), { st with stack := s.push (.int (.num
          (if Bls12381.g1IsZero (bitStringToBytesBE (a.readBits 384)) then -1 else 0))) })
      else (.error .cellUnd, { st with stack := s }) := by
  by_cases ha : a.haveBits 384 = true <;> vm_simp [hs, ha, prefetchBytesCellUnd_eq]

/-- `BLS_G1_INGROUP` on the stack `s a`. -/
@[vm_spec] theorem blsG1InGroup (st : VmState) (s : Stack) (a : Slice) (hs : st.stack = s.push (.slice a)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG1InGroup))) st =
      if ({ st with gas := st.gas.consume blsG1InGroupGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG1InGroupGasPrice })
      else if a.haveBits 384 then
        (.ok (), { st with stack := s.push (.int (.num
          (if Bls12381.g1InGroup (bitStringToBytesBE (a.readBits 384)) then -1 else 0))),
                           gas := st.gas.consume blsG1InGroupGasPrice })
      else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG1InGroupGasPrice }) := by
  by_cases ha : a.haveBits 384 = true <;> vm_simp [hs, ha, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_G1_NEG` on the stack `s a`. -/
@[vm_spec] theorem blsG1Neg (st : VmState) (s : Stack) (a : Slice) (hs : st.stack = s.push (.slice a)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG1Neg))) st =
      if ({ st with gas := st.gas.consume blsG1NegGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG1NegGasPrice })
      else if a.haveBits 384 then
        match Bls12381.g1Neg (bitStringToBytesBE (a.readBits 384)) with
        | some out => (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk out))),
                                         gas := st.gas.consume blsG1NegGasPrice })
        | none => (.error .unknown, { st with stack := s, gas := st.gas.consume blsG1NegGasPrice })
      else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG1NegGasPrice }) := by
  by_cases ha : a.haveBits 384 = true
  · cases h : Bls12381.g1Neg (bitStringToBytesBE (a.readBits 384)) <;>
      vm_simp [hs, ha, h, prefetchBytesCellUnd_eq, VmState.consumeGas]
  · vm_simp [hs, ha, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_MAP_TO_G1` on the stack `s a`. -/
@[vm_spec] theorem blsMapToG1 (st : VmState) (s : Stack) (a : Slice) (hs : st.stack = s.push (.slice a)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsMapToG1))) st =
      if ({ st with gas := st.gas.consume blsMapToG1GasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsMapToG1GasPrice })
      else if a.haveBits 384 then
        (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk
          (Bls12381.mapToG1Bytes (bitStringToBytesBE (a.readBits 384)))))),
                           gas := st.gas.consume blsMapToG1GasPrice })
      else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsMapToG1GasPrice }) := by
  by_cases ha : a.haveBits 384 = true <;> vm_simp [hs, ha, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_G1_ADD` on the stack `s a b`. -/
@[vm_spec] theorem blsG1Add (st : VmState) (s : Stack) (a b : Slice)
    (hs : st.stack = (s.push (.slice a)).push (.slice b)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG1Add))) st =
      if ({ st with gas := st.gas.consume blsG1AddSubGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG1AddSubGasPrice })
      else if b.haveBits 384 then
        if a.haveBits 384 then
          match Bls12381.g1Add (bitStringToBytesBE (a.readBits 384)) (bitStringToBytesBE (b.readBits 384)) with
          | some out => (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk out))),
                                           gas := st.gas.consume blsG1AddSubGasPrice })
          | none => (.error .unknown, { st with stack := s, gas := st.gas.consume blsG1AddSubGasPrice })
        else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG1AddSubGasPrice })
      else (.error .cellUnd, { st with stack := s.push (.slice a), gas := st.gas.consume blsG1AddSubGasPrice }) := by
  by_cases hb : b.haveBits 384 = true
  · by_cases ha : a.haveBits 384 = true
    · cases h : Bls12381.g1Add (bitStringToBytesBE (a.readBits 384)) (bitStringToBytesBE (b.readBits 384)) <;>
        vm_simp [hs, ha, hb, h, prefetchBytesCellUnd_eq, VmState.consumeGas]
    · vm_simp [hs, ha, hb, prefetchBytesCellUnd_eq, VmState.consumeGas]
  · vm_simp [hs, hb, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_G1_SUB` on the stack `s a b`. -/
@[vm_spec] theorem blsG1Sub (st : VmState) (s : Stack) (a b : Slice)
    (hs : st.stack = (s.push (.slice a)).push (.slice b)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG1Sub))) st =
      if ({ st with gas := st.gas.consume blsG1AddSubGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG1AddSubGasPrice })
      else if b.haveBits 384 then
        if a.haveBits 384 then
          match Bls12381.g1Sub (bitStringToBytesBE (a.readBits 384)) (bitStringToBytesBE (b.readBits 384)) with
          | some out => (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk out))),
                                           gas := st.gas.consume blsG1AddSubGasPrice })
          | none => (.error .unknown, { st with stack := s, gas := st.gas.consume blsG1AddSubGasPrice })
        else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG1AddSubGasPrice })
      else (.error .cellUnd, { st with stack := s.push (.slice a), gas := st.gas.consume blsG1AddSubGasPrice }) := by
  by_cases hb : b.haveBits 384 = true
  · by_cases ha : a.haveBits 384 = true
    · cases h : Bls12381.g1Sub (bitStringToBytesBE (a.readBits 384)) (bitStringToBytesBE (b.readBits 384)) <;>
        vm_simp [hs, ha, hb, h, prefetchBytesCellUnd_eq, VmState.consumeGas]
    · vm_simp [hs, ha, hb, prefetchBytesCellUnd_eq, VmState.consumeGas]
  · vm_simp [hs, hb, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_G1_MUL` on the stack `s p x`. -/
@[vm_spec] theorem blsG1Mul (st : VmState) (s : Stack) (p : Slice) (x : Int)
    (hs : st.stack = (s.push (.slice p)).push (.int (.num x))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG1Mul))) st =
      if ({ st with gas := st.gas.consume blsG1MulGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG1MulGasPrice })
      else if p.haveBits 384 then
        match Bls12381.g1MulInt (bitStringToBytesBE (p.readBits 384)) x with
        | some out => (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk out))),
                                         gas := st.gas.consume blsG1MulGasPrice })
        | none => (.error .unknown, { st with stack := s, gas := st.gas.consume blsG1MulGasPrice })
      else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG1MulGasPrice }) := by
  by_cases hp : p.haveBits 384 = true
  · cases h : Bls12381.g1MulInt (bitStringToBytesBE (p.readBits 384)) x <;>
      vm_simp [hs, hp, h, prefetchBytesCellUnd_eq, VmState.consumeGas]
  · vm_simp [hs, hp, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_G2_ZERO`: the encoding of zero of G2. -/
@[vm_spec] theorem blsG2Zero (st : VmState) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG2Zero))) st =
      (.ok (), { st with stack := st.stack.push (.slice (sliceOfByteArray (ByteArray.mk Bls12381.g2ZeroBytes))) }) := by
  vm_simp

/-- `BLS_G2_ISZERO` on the stack `s a`. -/
@[vm_spec] theorem blsG2IsZero (st : VmState) (s : Stack) (a : Slice) (hs : st.stack = s.push (.slice a)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG2IsZero))) st =
      if a.haveBits 768 then
        (.ok (), { st with stack := s.push (.int (.num
          (if Bls12381.g2IsZero (bitStringToBytesBE (a.readBits 768)) then -1 else 0))) })
      else (.error .cellUnd, { st with stack := s }) := by
  by_cases ha : a.haveBits 768 = true <;> vm_simp [hs, ha, prefetchBytesCellUnd_eq]

/-- `BLS_G2_INGROUP` on the stack `s a`. -/
@[vm_spec] theorem blsG2InGroup (st : VmState) (s : Stack) (a : Slice) (hs : st.stack = s.push (.slice a)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG2InGroup))) st =
      if ({ st with gas := st.gas.consume blsG2InGroupGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG2InGroupGasPrice })
      else if a.haveBits 768 then
        (.ok (), { st with stack := s.push (.int (.num
          (if Bls12381.g2InGroup (bitStringToBytesBE (a.readBits 768)) then -1 else 0))),
                           gas := st.gas.consume blsG2InGroupGasPrice })
      else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG2InGroupGasPrice }) := by
  by_cases ha : a.haveBits 768 = true <;> vm_simp [hs, ha, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_G2_NEG` on the stack `s a`. -/
@[vm_spec] theorem blsG2Neg (st : VmState) (s : Stack) (a : Slice) (hs : st.stack = s.push (.slice a)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG2Neg))) st =
      if ({ st with gas := st.gas.consume blsG2NegGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG2NegGasPrice })
      else if a.haveBits 768 then
        match Bls12381.g2Neg (bitStringToBytesBE (a.readBits 768)) with
        | some out => (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk out))),
                                         gas := st.gas.consume blsG2NegGasPrice })
        | none => (.error .unknown, { st with stack := s, gas := st.gas.consume blsG2NegGasPrice })
      else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG2NegGasPrice }) := by
  by_cases ha : a.haveBits 768 = true
  · cases h : Bls12381.g2Neg (bitStringToBytesBE (a.readBits 768)) <;>
      vm_simp [hs, ha, h, prefetchBytesCellUnd_eq, VmState.consumeGas]
  · vm_simp [hs, ha, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_MAP_TO_G2` on the stack `s a`. -/
@[vm_spec] theorem blsMapToG2 (st : VmState) (s : Stack) (a : Slice) (hs : st.stack = s.push (.slice a)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsMapToG2))) st =
      if ({ st with gas := st.gas.consume blsMapToG2GasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsMapToG2GasPrice })
      else if a.haveBits 768 then
        (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk
          (Bls12381.mapToG2Bytes (bitStringToBytesBE (a.readBits 768)))))),
                           gas := st.gas.consume blsMapToG2GasPrice })
      else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsMapToG2GasPrice }) := by
  by_cases ha : a.haveBits 768 = true <;> vm_simp [hs, ha, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_G2_ADD` on the stack `s a b`. -/
@[vm_spec] theorem blsG2Add (st : VmState) (s : Stack) (a b : Slice)
    (hs : st.stack = (s.push (.slice a)).push (.slice b)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG2Add))) st =
      if ({ st with gas := st.gas.consume blsG2AddSubGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG2AddSubGasPrice })
      else if b.haveBits 768 then
        if a.haveBits 768 then
          match Bls12381.g2Add (bitStringToBytesBE (a.readBits 768)) (bitStringToBytesBE (b.readBits 768)) with
          | some out => (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk out))),
                                           gas := st.gas.consume blsG2AddSubGasPrice })
          | none => (.error .unknown, { st with stack := s, gas := st.gas.consume blsG2AddSubGasPrice })
        else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG2AddSubGasPrice })
      else (.error .cellUnd, { st with stack := s.push (.slice a), gas := st.gas.consume blsG2AddSubGasPrice }) := by
  by_cases hb : b.haveBits 768 = true
  · by_cases ha : a.haveBits 768 = true
    · cases h : Bls12381.g2Add (bitStringToBytesBE (a.readBits 768)) (bitStringToBytesBE (b.readBits 768)) <;>
        vm_simp [hs, ha, hb, h, prefetchBytesCellUnd_eq, VmState.consumeGas]
    · vm_simp [hs, ha, hb, prefetchBytesCellUnd_eq, VmState.consumeGas]
  · vm_simp [hs, hb, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_G2_SUB` on the stack `s a b`. -/
@[vm_spec] theorem blsG2Sub (st : VmState) (s : Stack) (a b : Slice)
    (hs : st.stack = (s.push (.slice a)).push (.slice b)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG2Sub))) st =
      if ({ st with gas := st.gas.consume blsG2AddSubGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG2AddSubGasPrice })
      else if b.haveBits 768 then
        if a.haveBits 768 then
          match Bls12381.g2Sub (bitStringToBytesBE (a.readBits 768)) (bitStringToBytesBE (b.readBits 768)) with
          | some out => (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk out))),
                                           gas := st.gas.consume blsG2AddSubGasPrice })
          | none => (.error .unknown, { st with stack := s, gas := st.gas.consume blsG2AddSubGasPrice })
        else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG2AddSubGasPrice })
      else (.error .cellUnd, { st with stack := s.push (.slice a), gas := st.gas.consume blsG2AddSubGasPrice }) := by
  by_cases hb : b.haveBits 768 = true
  · by_cases ha : a.haveBits 768 = true
    · cases h : Bls12381.g2Sub (bitStringToBytesBE (a.readBits 768)) (bitStringToBytesBE (b.readBits 768)) <;>
        vm_simp [hs, ha, hb, h, prefetchBytesCellUnd_eq, VmState.consumeGas]
    · vm_simp [hs, ha, hb, prefetchBytesCellUnd_eq, VmState.consumeGas]
  · vm_simp [hs, hb, prefetchBytesCellUnd_eq, VmState.consumeGas]

/-- `BLS_G2_MUL` on the stack `s p x`. -/
@[vm_spec] theorem blsG2Mul (st : VmState) (s : Stack) (p : Slice) (x : Int)
    (hs : st.stack = (s.push (.slice p)).push (.int (.num x))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .blsG2Mul))) st =
      if ({ st with gas := st.gas.consume blsG2MulGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with gas := st.gas.consume blsG2MulGasPrice })
      else if p.haveBits 768 then
        match Bls12381.g2MulInt (bitStringToBytesBE (p.readBits 768)) x with
        | some out => (.ok (), { st with stack := s.push (.slice (sliceOfByteArray (ByteArray.mk out))),
                                         gas := st.gas.consume blsG2MulGasPrice })
        | none => (.error .unknown, { st with stack := s, gas := st.gas.consume blsG2MulGasPrice })
      else (.error .cellUnd, { st with stack := s, gas := st.gas.consume blsG2MulGasPrice }) := by
  by_cases hp : p.haveBits 768 = true
  · cases h : Bls12381.g2MulInt (bitStringToBytesBE (p.readBits 768)) x <;>
      vm_simp [hs, hp, h, prefetchBytesCellUnd_eq, VmState.consumeGas]
  · vm_simp [hs, hp, prefetchBytesCellUnd_eq, VmState.consumeGas]

end TvmLean.Spec

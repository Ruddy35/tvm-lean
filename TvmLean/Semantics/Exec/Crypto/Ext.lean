import TvmLean.Semantics.Exec.Common

namespace TvmLean

def intValMod (x : IntVal) (m : Int) : IntVal :=
  match x with
  | .nan => .nan
  | .num n => .num (n % m)

def exportUInt256BE? (x : IntVal) : Option (Array UInt8) :=
  match exportUInt256BE x with
  | .ok bs => some bs
  | .error _ => none

def sliceToFullBytes (s : Slice) : Except Excno (Array UInt8) := do
  if s.bitsRemaining % 8 != 0 then
    throw .cellUnd
  let bytes : Nat := s.bitsRemaining / 8
  s.prefetchBytesCellUnd bytes

def sliceOfByteArray (ba : ByteArray) : Slice :=
  Id.run do
    let mut bits : BitString := #[]
    for i in [0:ba.size] do
      bits := bits ++ natToBits (ba.get! i).toNat 8
    Slice.ofCell (Cell.mkOrdinary bits #[])

def pushUInt256BE (bs : Array UInt8) : VM Unit :=
  VM.push (.int (.num (Int.ofNat (bytesToNatBE bs))))

def popNatInRange (min max : Nat) : VM Nat := do
  let v ← VM.popInt
  match v with
  | .nan => throw .rangeChk
  | .num n =>
      if n < 0 then
        throw .rangeChk
      let u := n.toNat
      if u < min ∨ u > max then
        throw .rangeChk
      return u

def blsMultiexpL (n : Nat) : Nat :=
  -- `2^(l+1) ≤ n` implies `l < n`, so bounding the counter by `n` does not change the result.
  countWhile n (fun l => decide ((1 <<< (l + 1)) ≤ n)) 4

def blsCalculateMultiexpGas (n : Nat) (base coef1 coef2 : Int) : Int :=
  let l : Nat := blsMultiexpL n
  base + (Int.ofNat n * coef1) + ((Int.ofNat n * coef2) / Int.ofNat l)

def rist255L : Int :=
  (Int.ofNat (1 <<< 252)) + 27742317777372353535851937790883648493

def blsR : Int :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

set_option maxHeartbeats 1000000 in
def execInstrCryptoExt (_host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cryptoOp (.ext op) =>
      match op with
      | .ecrecover =>
          VM.checkUnderflow 4  -- C++ `stack.check_underflow(4)` before the pops
          let s ← VM.popInt
          let r ← VM.popInt
          let v ← VM.popNatUpTo 255
          let hash ← VM.popInt

          let rBytes ←
            match exportUInt256BE r with
            | .ok bs => pure bs
            | .error e => throw e
          let sBytes ←
            match exportUInt256BE s with
            | .ok bs => pure bs
            | .error e => throw e
          let hashBytes ←
            match exportUInt256BE hash with
            | .ok bs => pure bs
            | .error e => throw e

          -- TVM 14 accepts Ethereum legacy recovery ids v = 27/28 (mapped to 0/1)
          let v : Nat := if ((← get).globalVersion ≥ 14) && (v == 27 || v == 28) then v - 27 else v
          VM.consumeGas ecrecoverGasPrice

          -- C++ `td::secp256k1::ecrecover`: the key serialized uncompressed, `h = 4`
          match Secp256k1.ecrecover (bytesToNatBE hashBytes) (bytesToNatBE rBytes) (bytesToNatBE sBytes) v with
          | none => VM.pushSmallInt 0
          | some (x, y) =>
              VM.pushSmallInt 4
              VM.push (.int (.num (Int.ofNat x)))
              VM.push (.int (.num (Int.ofNat y)))
              VM.pushSmallInt (-1)

      | .secp256k1XonlyPubkeyTweakAdd =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let tweak ← VM.popInt
          let key ← VM.popInt
          let keyBytes ←
            match exportUInt256BE key with
            | .ok bs => pure bs
            | .error e => throw e
          let tweakBytes ←
            match exportUInt256BE tweak with
            | .ok bs => pure bs
            | .error e => throw e

          VM.consumeGas secp256k1XonlyPubkeyTweakAddGasPrice

          -- C++ `td::secp256k1::xonly_pubkey_tweak_add`: the key serialized uncompressed, `h = 4`
          match Secp256k1.xonlyPubkeyTweakAdd (bytesToNatBE keyBytes) (bytesToNatBE tweakBytes) with
          | none => VM.pushSmallInt 0
          | some (x, y) =>
              VM.pushSmallInt 4
              VM.push (.int (.num (Int.ofNat x)))
              VM.push (.int (.num (Int.ofNat y)))
              VM.pushSmallInt (-1)

      | .p256ChkSignU =>
          VM.checkUnderflow 3  -- C++ `stack.check_underflow(3)` before the pops
          let keySlice ← VM.popSlice
          let sigSlice ← VM.popSlice
          let hash ← VM.popInt

          let dataBytes ←
            match exportUInt256BE hash with
            | .ok bs => pure bs
            | .error e => throw e
          let sigBytes ←
            match sigSlice.prefetchBytesCellUnd 64 with
            | .ok bs => pure bs
            | .error e => throw e
          let keyBytes ←
            match keySlice.prefetchBytesCellUnd 33 with
            | .ok bs => pure bs
            | .error e => throw e

          VM.consumeGas p256ChksgnGasPrice
          VM.pushSmallInt (if P256.verify dataBytes keyBytes sigBytes then (-1) else 0)

      | .p256ChkSignS =>
          VM.checkUnderflow 3  -- C++ `stack.check_underflow(3)` before the pops
          let keySlice ← VM.popSlice
          let sigSlice ← VM.popSlice
          let dataSlice ← VM.popSlice
          if dataSlice.bitsRemaining % 8 != 0 then
            throw .cellUnd
          let dataLen : Nat := dataSlice.bitsRemaining / 8
          if dataLen > 128 then
            throw .rangeChk

          let dataBytes ←
            match dataSlice.prefetchBytesCellUnd dataLen with
            | .ok bs => pure bs
            | .error e => throw e
          let sigBytes ←
            match sigSlice.prefetchBytesCellUnd 64 with
            | .ok bs => pure bs
            | .error e => throw e
          let keyBytes ←
            match keySlice.prefetchBytesCellUnd 33 with
            | .ok bs => pure bs
            | .error e => throw e

          VM.consumeGas p256ChksgnGasPrice
          VM.pushSmallInt (if P256.verify dataBytes keyBytes sigBytes then (-1) else 0)

      | .rist255FromHash =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let x2 ← VM.popInt
          let x1 ← VM.popInt
          VM.consumeGas rist255FromHashGasPrice
          let x1Bytes ←
            match exportUInt256BE x1 with
            | .ok bs => pure bs
            | .error e => throw e
          let x2Bytes ←
            match exportUInt256BE x2 with
            | .ok bs => pure bs
            | .error e => throw e
          pushUInt256BE (Ristretto255.fromHash (x1Bytes ++ x2Bytes))

      | .rist255Validate =>
          let x ← VM.popInt
          VM.consumeGas rist255ValidateGasPrice
          let xb ←
            match exportUInt256BE x with
            | .ok bs => pure bs
            | .error e => throw e
          if !Ristretto255.isValid xb then
            throw .rangeChk

      | .rist255Qvalidate =>
          let x ← VM.popInt
          VM.consumeGas rist255ValidateGasPrice
          let ok :=
            match exportUInt256BE? x with
            | none => false
            | some xb => Ristretto255.isValid xb
          VM.pushSmallInt (if ok then (-1) else 0)

      | .rist255Add =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let y ← VM.popInt
          let x ← VM.popInt
          VM.consumeGas rist255AddGasPrice
          let xb ←
            match exportUInt256BE x with
            | .ok bs => pure bs
            | .error e => throw e
          let yb ←
            match exportUInt256BE y with
            | .ok bs => pure bs
            | .error e => throw e
          match Ristretto255.add xb yb with
          | none => throw .rangeChk
          | some r => pushUInt256BE r

      | .rist255Sub =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let y ← VM.popInt
          let x ← VM.popInt
          VM.consumeGas rist255AddGasPrice
          let xb ←
            match exportUInt256BE x with
            | .ok bs => pure bs
            | .error e => throw e
          let yb ←
            match exportUInt256BE y with
            | .ok bs => pure bs
            | .error e => throw e
          match Ristretto255.sub xb yb with
          | none => throw .rangeChk
          | some r => pushUInt256BE r

      | .rist255Qadd =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let y ← VM.popInt
          let x ← VM.popInt
          VM.consumeGas rist255AddGasPrice
          match exportUInt256BE? x, exportUInt256BE? y with
          | some xb, some yb =>
              match Ristretto255.add xb yb with
              | none => VM.pushSmallInt 0
              | some r =>
                  pushUInt256BE r
                  VM.pushSmallInt (-1)
          | _, _ =>
              VM.pushSmallInt 0

      | .rist255Qsub =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let y ← VM.popInt
          let x ← VM.popInt
          VM.consumeGas rist255AddGasPrice
          match exportUInt256BE? x, exportUInt256BE? y with
          | some xb, some yb =>
              match Ristretto255.sub xb yb with
              | none => VM.pushSmallInt 0
              | some r =>
                  pushUInt256BE r
                  VM.pushSmallInt (-1)
          | _, _ =>
              VM.pushSmallInt 0

      | .rist255Mul =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let n0 ← VM.popInt
          let x ← VM.popInt
          let n := intValMod n0 rist255L
          VM.consumeGas rist255MulGasPrice
          -- C++ exec_ristretto255_mul, including the TVM 14 changes (NaN operands rejected,
          -- `x = 0` gives 0, the point is validated on the `n % l = 0` fast path).
          let v14 : Bool := (← get).globalVersion ≥ 14
          let anyNan : Bool := match n, x with | .num _, .num _ => false | _, _ => true
          let nZero : Bool := match n with | .num 0 => true | _ => false
          let xZero : Bool := match x with | .num 0 => true | _ => false
          if v14 && anyNan then
            throw .rangeChk
          else if nZero || (v14 && xZero) then
            let invalidPoint : Bool :=
              !xZero && (match exportUInt256BE? x with
                | some xb => !Ristretto255.isValid xb
                | none => true)
            if v14 && invalidPoint then
              throw .rangeChk
            else
              VM.pushSmallInt 0
          else
            match exportUInt256BE? x, exportUInt256BE? n with
            | some xb, some nbBe =>
                let nbLe := nbBe.reverse
                match Ristretto255.mul nbLe xb with
                | none => throw .rangeChk
                | some r => pushUInt256BE r
            | _, _ =>
                throw .rangeChk

      | .rist255Qmul =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let n0 ← VM.popInt
          let x ← VM.popInt
          let n := intValMod n0 rist255L
          VM.consumeGas rist255MulGasPrice
          -- C++ exec_ristretto255_mul, including the TVM 14 changes (NaN operands rejected,
          -- `x = 0` gives 0, the point is validated on the `n % l = 0` fast path).
          let v14 : Bool := (← get).globalVersion ≥ 14
          let anyNan : Bool := match n, x with | .num _, .num _ => false | _, _ => true
          let nZero : Bool := match n with | .num 0 => true | _ => false
          let xZero : Bool := match x with | .num 0 => true | _ => false
          if v14 && anyNan then
            VM.pushSmallInt 0
          else if nZero || (v14 && xZero) then
            let invalidPoint : Bool :=
              !xZero && (match exportUInt256BE? x with
                | some xb => !Ristretto255.isValid xb
                | none => true)
            if v14 && invalidPoint then
              VM.pushSmallInt 0
            else
              VM.pushSmallInt 0
              VM.pushSmallInt (-1)
          else
            match exportUInt256BE? x, exportUInt256BE? n with
            | some xb, some nbBe =>
                let nbLe := nbBe.reverse
                match Ristretto255.mul nbLe xb with
                | none => VM.pushSmallInt 0
                | some r =>
                    pushUInt256BE r
                    VM.pushSmallInt (-1)
            | _, _ =>
                VM.pushSmallInt 0

      | .rist255MulBase =>
          let n0 ← VM.popInt
          let n := intValMod n0 rist255L
          VM.consumeGas rist255MulBaseGasPrice
          -- TVM 14: `n % l = 0` gives 0 directly (C++ exec_ristretto255_mul_base)
          if ((← get).globalVersion ≥ 14) && (match n with | .num 0 => true | _ => false) then
            VM.pushSmallInt 0
          else
            let nbBe ←
              match exportUInt256BE n with
              | .ok bs => pure bs
              | .error e => throw e
            -- `crypto_scalarmult_ristretto255_base` fails for the identity after writing its
            -- encoding (zeros): an error from version 14, the zeros before (C++ checks `rb`
            -- against its initial 0xff bytes)
            let (r, ok) := Ristretto255.mulBase nbBe.reverse
            if !ok && (← get).globalVersion ≥ 14 then
              throw .rangeChk
            pushUInt256BE r

      | .rist255QmulBase =>
          let n0 ← VM.popInt
          let n := intValMod n0 rist255L
          VM.consumeGas rist255MulBaseGasPrice
          -- TVM 14: `n % l = 0` gives 0 directly (C++ exec_ristretto255_mul_base)
          if ((← get).globalVersion ≥ 14) && (match n with | .num 0 => true | _ => false) then
            VM.pushSmallInt 0
            VM.pushSmallInt (-1)
          else
            match exportUInt256BE? n with
            | none =>
                VM.pushSmallInt 0
            | some nbBe =>
                let (r, ok) := Ristretto255.mulBase nbBe.reverse
                if !ok && (← get).globalVersion ≥ 14 then
                  VM.pushSmallInt 0
                else
                  pushUInt256BE r
                  VM.pushSmallInt (-1)

      | .rist255PushL =>
          VM.push (.int (.num rist255L))

      | .blsVerify =>
          let st0 ← get
          if st0.stack.size < 3 then
            throw .stkUnd
          VM.consumeGas blsVerifyGasPrice
          let sigBytes ←
            do
              let sigSlice ← VM.popSlice
              match sigSlice.prefetchBytesCellUnd 96 with
              | .ok bs => pure bs
              | .error e => throw e
          let msgBytes ←
            do
              let msgSlice ← VM.popSlice
              match sliceToFullBytes msgSlice with
              | .ok bs => pure bs
              | .error e => throw e
          let pubBytes ←
            do
              let pubSlice ← VM.popSlice
              match pubSlice.prefetchBytesCellUnd 48 with
              | .ok bs => pure bs
              | .error e => throw e

          let ok := Bls12381.verify pubBytes msgBytes sigBytes
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsAggregate =>
          let st0 ← get
          let maxN : Nat := st0.stack.size - 1
          let n ← popNatInRange 1 maxN
          VM.consumeGas (blsAggregateBaseGasPrice + Int.ofNat n * blsAggregateElementGasPrice)

          let mut sigs : Array (Array UInt8) := Array.replicate n #[]
          for j in [0:n] do
            let idx : Nat := n - 1 - j
            let s ← VM.popSlice
            let bs ←
              match s.prefetchBytesCellUnd 96 with
              | .ok bs => pure bs
              | .error e => throw e
            sigs := sigs.set! idx bs

          match Bls12381.aggregate sigs with
          | some out => VM.push (.slice (sliceOfByteArray (ByteArray.mk out)))
          | none => throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}

      | .blsFastAggregateVerify =>
          let st0 ← get
          if st0.stack.size < 3 then
            throw .stkUnd
          let sigSlice ← VM.popSlice
          let msgSlice ← VM.popSlice
          let stBeforeN ← get
          let maxN : Nat := stBeforeN.stack.size - 1
          let n ← VM.popNatUpTo maxN
          VM.consumeGas
            (blsFastAggregateVerifyBaseGasPrice + Int.ofNat n * blsFastAggregateVerifyElementGasPrice)

          let mut pubs : Array (Array UInt8) := Array.replicate n #[]
          for j in [0:n] do
            let idx : Nat := n - 1 - j
            let s ← VM.popSlice
            let bs ←
              match s.prefetchBytesCellUnd 48 with
              | .ok bs => pure bs
              | .error e => throw e
            pubs := pubs.set! idx bs

          let msgBytes ←
            match sliceToFullBytes msgSlice with
            | .ok bs => pure bs
            | .error e => throw e
          let sigBytes ←
            match sigSlice.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let ok := Bls12381.fastAggregateVerify pubs msgBytes sigBytes
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsAggregateVerify =>
          let st0 ← get
          if st0.stack.size < 2 then
            throw .stkUnd
          let sigSlice ← VM.popSlice
          let stBeforeN ← get
          let maxN : Nat := (stBeforeN.stack.size - 1) / 2
          let n ← VM.popNatUpTo maxN
          VM.consumeGas
            (blsAggregateVerifyBaseGasPrice + Int.ofNat n * blsAggregateVerifyElementGasPrice)

          let mut pubs : Array (Array UInt8) := Array.replicate n #[]
          let mut msgs : Array (Array UInt8) := Array.replicate n #[]
          for j in [0:n] do
            let idx : Nat := n - 1 - j
            let msgSlice ← VM.popSlice
            let msgBytes ←
              match sliceToFullBytes msgSlice with
              | .ok bs => pure bs
              | .error e => throw e
            let pubSlice ← VM.popSlice
            let pubBytes ←
              match pubSlice.prefetchBytesCellUnd 48 with
              | .ok bs => pure bs
              | .error e => throw e
            pubs := pubs.set! idx pubBytes
            msgs := msgs.set! idx msgBytes

          let sigBytes ←
            match sigSlice.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e

          let ok := Bls12381.aggregateVerify pubs msgs sigBytes
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsG1Add | .blsG1Sub | .blsG2Add | .blsG2Sub =>
          let size : Nat := if op matches .blsG1Add | .blsG1Sub then 48 else 96
          let st0 ← get
          if st0.stack.size < 2 then
            throw .stkUnd
          VM.consumeGas (if size = 48 then blsG1AddSubGasPrice else blsG2AddSubGasPrice)
          let b ← VM.popSlice
          let bb ←
            match b.prefetchBytesCellUnd size with
            | .ok bs => pure bs
            | .error e => throw e
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd size with
            | .ok bs => pure bs
            | .error e => throw e
          let out :=
            match op with
            | .blsG1Add => Bls12381.g1Add ab bb
            | .blsG1Sub => Bls12381.g1Sub ab bb
            | .blsG2Add => Bls12381.g2Add ab bb
            | _ => Bls12381.g2Sub ab bb
          match out with
          | some out => VM.push (.slice (sliceOfByteArray (ByteArray.mk out)))
          | none => throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}

      | .blsG1Neg | .blsG2Neg =>
          let size : Nat := if op matches .blsG1Neg then 48 else 96
          VM.consumeGas (if size = 48 then blsG1NegGasPrice else blsG2NegGasPrice)
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd size with
            | .ok bs => pure bs
            | .error e => throw e
          match (if size = 48 then Bls12381.g1Neg ab else Bls12381.g2Neg ab) with
          | some out => VM.push (.slice (sliceOfByteArray (ByteArray.mk out)))
          | none => throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}

      | .blsG1Mul | .blsG2Mul =>
          let size : Nat := if op matches .blsG1Mul then 48 else 96
          let st0 ← get
          if st0.stack.size < 2 then
            throw .stkUnd
          VM.consumeGas (if size = 48 then blsG1MulGasPrice else blsG2MulGasPrice)
          let x ← VM.popIntFinite
          let pSlice ← VM.popSlice
          let pb ←
            match pSlice.prefetchBytesCellUnd size with
            | .ok bs => pure bs
            | .error e => throw e
          -- `generic_mul`: the zero point for x = 0 without reading the point, else x mod r
          match (if size = 48 then Bls12381.g1MulInt pb x else Bls12381.g2MulInt pb x) with
          | some out => VM.push (.slice (sliceOfByteArray (ByteArray.mk out)))
          | none => throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}

      | .blsG1MultiExp | .blsG2MultiExp =>
          let size : Nat := if op matches .blsG1MultiExp then 48 else 96
          let stBeforeN ← get
          let maxN : Nat := (stBeforeN.stack.size - 1) / 2
          let n ← VM.popNatUpTo maxN
          VM.consumeGas
            (if size = 48 then
              blsCalculateMultiexpGas n blsG1MultiExpBaseGasPrice blsG1MultiExpCoef1GasPrice blsG1MultiExpCoef2GasPrice
            else
              blsCalculateMultiexpGas n blsG2MultiExpBaseGasPrice blsG2MultiExpCoef1GasPrice blsG2MultiExpCoef2GasPrice)

          let mut ps : Array (Array UInt8) := Array.replicate n #[]
          let mut xs : Array Int := Array.replicate n 0
          for j in [0:n] do
            let idx : Nat := n - 1 - j
            let x ← VM.popIntFinite
            let pSlice ← VM.popSlice
            let pb ←
              match pSlice.prefetchBytesCellUnd size with
              | .ok bs => pure bs
              | .error e => throw e
            ps := ps.set! idx pb
            xs := xs.set! idx x

          match (if size = 48 then Bls12381.g1MultiExp ps xs else Bls12381.g2MultiExp ps xs) with
          | some out => VM.push (.slice (sliceOfByteArray (ByteArray.mk out)))
          | none => throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}

      | .blsG1Zero =>
          VM.push (.slice (sliceOfByteArray (ByteArray.mk Bls12381.g1ZeroBytes)))

      | .blsG2Zero =>
          VM.push (.slice (sliceOfByteArray (ByteArray.mk Bls12381.g2ZeroBytes)))

      | .blsMapToG1 | .blsMapToG2 =>
          let size : Nat := if op matches .blsMapToG1 then 48 else 96
          VM.consumeGas (if size = 48 then blsMapToG1GasPrice else blsMapToG2GasPrice)
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd size with
            | .ok bs => pure bs
            | .error e => throw e
          let out := if size = 48 then Bls12381.mapToG1Bytes ab else Bls12381.mapToG2Bytes ab
          VM.push (.slice (sliceOfByteArray (ByteArray.mk out)))

      | .blsG1InGroup | .blsG2InGroup =>
          let size : Nat := if op matches .blsG1InGroup then 48 else 96
          VM.consumeGas (if size = 48 then blsG1InGroupGasPrice else blsG2InGroupGasPrice)
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd size with
            | .ok bs => pure bs
            | .error e => throw e
          let ok := if size = 48 then Bls12381.g1InGroup ab else Bls12381.g2InGroup ab
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsG1IsZero | .blsG2IsZero =>
          let size : Nat := if op matches .blsG1IsZero then 48 else 96
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd size with
            | .ok bs => pure bs
            | .error e => throw e
          let ok := if size = 48 then Bls12381.g1IsZero ab else Bls12381.g2IsZero ab
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsPairing =>
          let stBeforeN ← get
          let maxN : Nat := (stBeforeN.stack.size - 1) / 2
          let n ← VM.popNatUpTo maxN
          VM.consumeGas (blsPairingBaseGasPrice + Int.ofNat n * blsPairingElementGasPrice)
          let mut p1s : Array (Array UInt8) := Array.replicate n #[]
          let mut p2s : Array (Array UInt8) := Array.replicate n #[]
          for j in [0:n] do
            let idx : Nat := n - 1 - j
            let p2Slice ← VM.popSlice
            let p2Bytes ←
              match p2Slice.prefetchBytesCellUnd 96 with
              | .ok bs => pure bs
              | .error e => throw e
            let p1Slice ← VM.popSlice
            let p1Bytes ←
              match p1Slice.prefetchBytesCellUnd 48 with
              | .ok bs => pure bs
              | .error e => throw e
            p1s := p1s.set! idx p1Bytes
            p2s := p2s.set! idx p2Bytes
          match Bls12381.pairing p1s p2s with
          | some ok => VM.pushSmallInt (if ok then (-1) else 0)
          | none => throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}

      | .blsPushR =>
          VM.push (.int (.num blsR))
  | _ => next

end TvmLean

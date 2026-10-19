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

def pushUInt256FromByteArrayBE (ba : ByteArray) : VM Unit := do
  VM.push (.int (.num (Int.ofNat (byteArrayToNatBE ba))))

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
def execInstrCryptoExt (host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
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
          let sig : Array UInt8 := rBytes ++ sBytes ++ #[UInt8.ofNat v]
          VM.consumeGas ecrecoverGasPrice

          let publicKey : ByteArray := host.secp256k1Ecrecover (ByteArray.mk hashBytes) (ByteArray.mk sig)
          if publicKey.size == 0 then
            VM.pushSmallInt 0
          else
            if publicKey.size != 65 then
              VM.unimplementedInstr { name := Instr.pretty i } "crypto ext backend path is not fully implemented"
            let h : UInt8 := publicKey.get! 0
            let x1 := publicKey.extract 1 33
            let x2 := publicKey.extract 33 65
            VM.pushSmallInt (Int.ofNat h.toNat)
            pushUInt256FromByteArrayBE x1
            pushUInt256FromByteArrayBE x2
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

          let publicKey : ByteArray :=
            host.secp256k1XonlyPubkeyTweakAdd (ByteArray.mk keyBytes) (ByteArray.mk tweakBytes)
          if publicKey.size == 0 then
            VM.pushSmallInt 0
          else
            if publicKey.size != 65 then
              VM.unimplementedInstr { name := Instr.pretty i } "crypto ext backend path is not fully implemented"
            let h : UInt8 := publicKey.get! 0
            let x1 := publicKey.extract 1 33
            let x2 := publicKey.extract 33 65
            VM.pushSmallInt (Int.ofNat h.toNat)
            pushUInt256FromByteArrayBE x1
            pushUInt256FromByteArrayBE x2
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
          let ok := host.p256Verify (ByteArray.mk dataBytes) (ByteArray.mk keyBytes) (ByteArray.mk sigBytes)
          VM.pushSmallInt (if ok then (-1) else 0)

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
          let ok := host.p256Verify (ByteArray.mk dataBytes) (ByteArray.mk keyBytes) (ByteArray.mk sigBytes)
          VM.pushSmallInt (if ok then (-1) else 0)

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
          let r := host.rist255FromHash (ByteArray.mk x1Bytes) (ByteArray.mk x2Bytes)
          if r.size != 32 then
            VM.unimplementedInstr { name := Instr.pretty i } "crypto ext backend path is not fully implemented"
          pushUInt256FromByteArrayBE r

      | .rist255Validate =>
          let x ← VM.popInt
          VM.consumeGas rist255ValidateGasPrice
          let xb ←
            match exportUInt256BE x with
            | .ok bs => pure bs
            | .error e => throw e
          if !host.rist255IsValidPoint (ByteArray.mk xb) then
            throw .rangeChk

      | .rist255Qvalidate =>
          let x ← VM.popInt
          VM.consumeGas rist255ValidateGasPrice
          let ok :=
            match exportUInt256BE? x with
            | none => false
            | some xb => host.rist255IsValidPoint (ByteArray.mk xb)
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
          let r := host.rist255AddBytes (ByteArray.mk xb) (ByteArray.mk yb)
          if r.size != 32 then
            throw .rangeChk
          pushUInt256FromByteArrayBE r

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
          let r := host.rist255SubBytes (ByteArray.mk xb) (ByteArray.mk yb)
          if r.size != 32 then
            throw .rangeChk
          pushUInt256FromByteArrayBE r

      | .rist255Qadd =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let y ← VM.popInt
          let x ← VM.popInt
          VM.consumeGas rist255AddGasPrice
          match exportUInt256BE? x, exportUInt256BE? y with
          | some xb, some yb =>
              let r := host.rist255AddBytes (ByteArray.mk xb) (ByteArray.mk yb)
              if r.size == 32 then
                pushUInt256FromByteArrayBE r
                VM.pushSmallInt (-1)
              else
                VM.pushSmallInt 0
          | _, _ =>
              VM.pushSmallInt 0

      | .rist255Qsub =>
          VM.checkUnderflow 2  -- C++ `stack.check_underflow(2)` before the pops
          let y ← VM.popInt
          let x ← VM.popInt
          VM.consumeGas rist255AddGasPrice
          match exportUInt256BE? x, exportUInt256BE? y with
          | some xb, some yb =>
              let r := host.rist255SubBytes (ByteArray.mk xb) (ByteArray.mk yb)
              if r.size == 32 then
                pushUInt256FromByteArrayBE r
                VM.pushSmallInt (-1)
              else
                VM.pushSmallInt 0
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
                | some xb => !host.rist255IsValidPoint (ByteArray.mk xb)
                | none => true)
            if v14 && invalidPoint then
              throw .rangeChk
            else
              VM.pushSmallInt 0
          else
            match exportUInt256BE? x, exportUInt256BE? n with
            | some xb, some nbBe =>
                let nbLe := nbBe.reverse
                let r := host.rist255MulBytes (ByteArray.mk nbLe) (ByteArray.mk xb)
                if r.size == 32 then
                    pushUInt256FromByteArrayBE r
                else
                  throw .rangeChk
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
                | some xb => !host.rist255IsValidPoint (ByteArray.mk xb)
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
                let r := host.rist255MulBytes (ByteArray.mk nbLe) (ByteArray.mk xb)
                if r.size == 32 then
                    pushUInt256FromByteArrayBE r
                    VM.pushSmallInt (-1)
                else
                  VM.pushSmallInt 0
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
            let nbLe := nbBe.reverse
            let r := host.rist255MulBaseBytes (ByteArray.mk nbLe)
            if r.size != 32 then
              throw .rangeChk
            pushUInt256FromByteArrayBE r

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
                let nbLe := nbBe.reverse
                let r := host.rist255MulBaseBytes (ByteArray.mk nbLe)
                if r.size == 32 then
                  pushUInt256FromByteArrayBE r
                  VM.pushSmallInt (-1)
                else
                  VM.pushSmallInt 0

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

          let ok := host.blsVerify (ByteArray.mk pubBytes) (ByteArray.mk msgBytes) (ByteArray.mk sigBytes)
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsAggregate =>
          let st0 ← get
          let maxN : Nat := st0.stack.size - 1
          let n ← popNatInRange 1 maxN
          VM.consumeGas (blsAggregateBaseGasPrice + Int.ofNat n * blsAggregateElementGasPrice)

          let mut sigs : Array ByteArray := Array.replicate n (ByteArray.mk #[])
          for j in [0:n] do
            let idx : Nat := n - 1 - j
            let s ← VM.popSlice
            let bs ←
              match s.prefetchBytesCellUnd 96 with
              | .ok bs => pure bs
              | .error e => throw e
            sigs := sigs.set! idx (ByteArray.mk bs)

          let out := host.blsAggregate sigs
          if out.size != 96 then
            throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
          VM.push (.slice (sliceOfByteArray out))

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

          let mut pubs : Array ByteArray := Array.replicate n (ByteArray.mk #[])
          for j in [0:n] do
            let idx : Nat := n - 1 - j
            let s ← VM.popSlice
            let bs ←
              match s.prefetchBytesCellUnd 48 with
              | .ok bs => pure bs
              | .error e => throw e
            pubs := pubs.set! idx (ByteArray.mk bs)

          let msgBytes ←
            match sliceToFullBytes msgSlice with
            | .ok bs => pure bs
            | .error e => throw e
          let sigBytes ←
            match sigSlice.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let ok := host.blsFastAggregateVerify pubs (ByteArray.mk msgBytes) (ByteArray.mk sigBytes)
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

          let mut pubs : Array ByteArray := Array.replicate n (ByteArray.mk #[])
          let mut msgs : Array ByteArray := Array.replicate n (ByteArray.mk #[])
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
            pubs := pubs.set! idx (ByteArray.mk pubBytes)
            msgs := msgs.set! idx (ByteArray.mk msgBytes)

          let sigBytes ←
            match sigSlice.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e

          let ok := host.blsAggregateVerify pubs msgs (ByteArray.mk sigBytes)
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsG1Add =>
          let st0 ← get
          if st0.stack.size < 2 then
            throw .stkUnd
          VM.consumeGas blsG1AddSubGasPrice
          let b ← VM.popSlice
          let bb ←
            match b.prefetchBytesCellUnd 48 with
            | .ok bs => pure bs
            | .error e => throw e
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 48 with
            | .ok bs => pure bs
            | .error e => throw e
          let out := host.blsG1AddBytes (ByteArray.mk ab) (ByteArray.mk bb)
          if out.size != 48 then
            throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
          VM.push (.slice (sliceOfByteArray out))

      | .blsG1Sub =>
          let st0 ← get
          if st0.stack.size < 2 then
            throw .stkUnd
          VM.consumeGas blsG1AddSubGasPrice
          let b ← VM.popSlice
          let bb ←
            match b.prefetchBytesCellUnd 48 with
            | .ok bs => pure bs
            | .error e => throw e
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 48 with
            | .ok bs => pure bs
            | .error e => throw e
          let out := host.blsG1SubBytes (ByteArray.mk ab) (ByteArray.mk bb)
          if out.size != 48 then
            throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
          VM.push (.slice (sliceOfByteArray out))

      | .blsG1Neg =>
          VM.consumeGas blsG1NegGasPrice
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 48 with
            | .ok bs => pure bs
            | .error e => throw e
          let out := host.blsG1NegBytes (ByteArray.mk ab)
          if out.size != 48 then
            throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
          VM.push (.slice (sliceOfByteArray out))

      | .blsG1Mul =>
          let st0 ← get
          if st0.stack.size < 2 then
            throw .stkUnd
          VM.consumeGas blsG1MulGasPrice
          let x ← VM.popIntFinite
          let pSlice ← VM.popSlice
          let pb ←
            match pSlice.prefetchBytesCellUnd 48 with
            | .ok bs => pure bs
            | .error e => throw e
          if x == 0 then
            let out := host.blsG1ZeroBytes ()
            if out.size != 48 then
              throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
            VM.push (.slice (sliceOfByteArray out))
          else
            let xMod : Int := x % blsR
            let xb ←
              match exportUInt256BE (.num xMod) with
              | .ok bs => pure bs
              | .error e => throw e
            let out := host.blsG1MulBytes (ByteArray.mk pb) (ByteArray.mk xb)
            if out.size != 48 then
              throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
            VM.push (.slice (sliceOfByteArray out))

      | .blsG1MultiExp =>
          let stBeforeN ← get
          let maxN : Nat := (stBeforeN.stack.size - 1) / 2
          let n ← VM.popNatUpTo maxN
          VM.consumeGas
            (blsCalculateMultiexpGas n blsG1MultiExpBaseGasPrice blsG1MultiExpCoef1GasPrice blsG1MultiExpCoef2GasPrice)

          let mut ps : Array ByteArray := Array.replicate n (ByteArray.mk #[])
          let mut xs : Array Int := Array.replicate n 0
          for j in [0:n] do
            let idx : Nat := n - 1 - j
            let x ← VM.popIntFinite
            let pSlice ← VM.popSlice
            let pb ←
              match pSlice.prefetchBytesCellUnd 48 with
              | .ok bs => pure bs
              | .error e => throw e
            ps := ps.set! idx (ByteArray.mk pb)
            xs := xs.set! idx x

          if n == 0 then
            let out := host.blsG1ZeroBytes ()
            if out.size != 48 then
              throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
            VM.push (.slice (sliceOfByteArray out))
          else if n == 1 then
            let x := xs[0]!
            let p := ps[0]!
            if x == 0 then
              let out := host.blsG1ZeroBytes ()
              if out.size != 48 then
                throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
              VM.push (.slice (sliceOfByteArray out))
            else
              let xMod : Int := x % blsR
              let xb ←
                match exportUInt256BE (.num xMod) with
                | .ok bs => pure bs
                | .error e => throw e
              let out := host.blsG1MulBytes p (ByteArray.mk xb)
              if out.size != 48 then
                throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
              VM.push (.slice (sliceOfByteArray out))
          else
            let mut scalars : Array ByteArray := Array.replicate n (ByteArray.mk #[])
            for k in [0:n] do
              let xMod : Int := xs[k]! % blsR
              let xbBe ←
                match exportUInt256BE (.num xMod) with
                | .ok bs => pure bs
                | .error e => throw e
              scalars := scalars.set! k (ByteArray.mk xbBe.reverse)
            let out := host.blsG1MultiExpBytes ps scalars
            if out.size != 48 then
              throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
            VM.push (.slice (sliceOfByteArray out))

      | .blsG1Zero =>
          let out := host.blsG1ZeroBytes ()
          if out.size != 48 then
            VM.unimplementedInstr { name := Instr.pretty i } "crypto ext backend path is not fully implemented"
          VM.push (.slice (sliceOfByteArray out))

      | .blsMapToG1 =>
          VM.consumeGas blsMapToG1GasPrice
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 48 with
            | .ok bs => pure bs
            | .error e => throw e
          let out := host.blsMapToG1Bytes (ByteArray.mk ab)
          if out.size != 48 then
            VM.unimplementedInstr { name := Instr.pretty i } "crypto ext backend path is not fully implemented"
          VM.push (.slice (sliceOfByteArray out))

      | .blsG1InGroup =>
          VM.consumeGas blsG1InGroupGasPrice
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 48 with
            | .ok bs => pure bs
            | .error e => throw e
          let ok := host.blsG1InGroup (ByteArray.mk ab)
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsG1IsZero =>
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 48 with
            | .ok bs => pure bs
            | .error e => throw e
          let ok := host.blsG1IsZero (ByteArray.mk ab)
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsG2Add =>
          let st0 ← get
          if st0.stack.size < 2 then
            throw .stkUnd
          VM.consumeGas blsG2AddSubGasPrice
          let b ← VM.popSlice
          let bb ←
            match b.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let out := host.blsG2AddBytes (ByteArray.mk ab) (ByteArray.mk bb)
          if out.size != 96 then
            throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
          VM.push (.slice (sliceOfByteArray out))

      | .blsG2Sub =>
          let st0 ← get
          if st0.stack.size < 2 then
            throw .stkUnd
          VM.consumeGas blsG2AddSubGasPrice
          let b ← VM.popSlice
          let bb ←
            match b.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let out := host.blsG2SubBytes (ByteArray.mk ab) (ByteArray.mk bb)
          if out.size != 96 then
            throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
          VM.push (.slice (sliceOfByteArray out))

      | .blsG2Neg =>
          VM.consumeGas blsG2NegGasPrice
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let out := host.blsG2NegBytes (ByteArray.mk ab)
          if out.size != 96 then
            throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
          VM.push (.slice (sliceOfByteArray out))

      | .blsG2Mul =>
          let st0 ← get
          if st0.stack.size < 2 then
            throw .stkUnd
          VM.consumeGas blsG2MulGasPrice
          let x ← VM.popIntFinite
          let pSlice ← VM.popSlice
          let pb ←
            match pSlice.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          if x == 0 then
            let out := host.blsG2ZeroBytes ()
            if out.size != 96 then
              throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
            VM.push (.slice (sliceOfByteArray out))
          else
            let xMod : Int := x % blsR
            let xb ←
              match exportUInt256BE (.num xMod) with
              | .ok bs => pure bs
              | .error e => throw e
            let out := host.blsG2MulBytes (ByteArray.mk pb) (ByteArray.mk xb)
            if out.size != 96 then
              throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
            VM.push (.slice (sliceOfByteArray out))

      | .blsG2MultiExp =>
          let stBeforeN ← get
          let maxN : Nat := (stBeforeN.stack.size - 1) / 2
          let n ← VM.popNatUpTo maxN
          VM.consumeGas
            (blsCalculateMultiexpGas n blsG2MultiExpBaseGasPrice blsG2MultiExpCoef1GasPrice blsG2MultiExpCoef2GasPrice)

          let mut ps : Array ByteArray := Array.replicate n (ByteArray.mk #[])
          let mut xs : Array Int := Array.replicate n 0
          for j in [0:n] do
            let idx : Nat := n - 1 - j
            let x ← VM.popIntFinite
            let pSlice ← VM.popSlice
            let pb ←
              match pSlice.prefetchBytesCellUnd 96 with
              | .ok bs => pure bs
              | .error e => throw e
            ps := ps.set! idx (ByteArray.mk pb)
            xs := xs.set! idx x

          if n == 0 then
            let out := host.blsG2ZeroBytes ()
            if out.size != 96 then
              throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
            VM.push (.slice (sliceOfByteArray out))
          else if n == 1 then
            let x := xs[0]!
            let p := ps[0]!
            if x == 0 then
              let out := host.blsG2ZeroBytes ()
              if out.size != 96 then
                throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
              VM.push (.slice (sliceOfByteArray out))
            else
              let xMod : Int := x % blsR
              let xb ←
                match exportUInt256BE (.num xMod) with
                | .ok bs => pure bs
                | .error e => throw e
              let out := host.blsG2MulBytes p (ByteArray.mk xb)
              if out.size != 96 then
                throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
              VM.push (.slice (sliceOfByteArray out))
          else
            let mut scalars : Array ByteArray := Array.replicate n (ByteArray.mk #[])
            for k in [0:n] do
              let xMod : Int := xs[k]! % blsR
              let xbBe ←
                match exportUInt256BE (.num xMod) with
                | .ok bs => pure bs
                | .error e => throw e
              scalars := scalars.set! k (ByteArray.mk xbBe.reverse)
            let out := host.blsG2MultiExpBytes ps scalars
            if out.size != 96 then
              throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}
            VM.push (.slice (sliceOfByteArray out))

      | .blsG2Zero =>
          let out := host.blsG2ZeroBytes ()
          if out.size != 96 then
            VM.unimplementedInstr { name := Instr.pretty i } "crypto ext backend path is not fully implemented"
          VM.push (.slice (sliceOfByteArray out))

      | .blsMapToG2 =>
          VM.consumeGas blsMapToG2GasPrice
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let out := host.blsMapToG2Bytes (ByteArray.mk ab)
          if out.size != 96 then
            VM.unimplementedInstr { name := Instr.pretty i } "crypto ext backend path is not fully implemented"
          VM.push (.slice (sliceOfByteArray out))

      | .blsG2InGroup =>
          VM.consumeGas blsG2InGroupGasPrice
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let ok := host.blsG2InGroup (ByteArray.mk ab)
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsG2IsZero =>
          let a ← VM.popSlice
          let ab ←
            match a.prefetchBytesCellUnd 96 with
            | .ok bs => pure bs
            | .error e => throw e
          let ok := host.blsG2IsZero (ByteArray.mk ab)
          VM.pushSmallInt (if ok then (-1) else 0)

      | .blsPairing =>
          let stBeforeN ← get
          let maxN : Nat := (stBeforeN.stack.size - 1) / 2
          let n ← VM.popNatUpTo maxN
          VM.consumeGas (blsPairingBaseGasPrice + Int.ofNat n * blsPairingElementGasPrice)
          let mut p1s : Array ByteArray := Array.replicate n (ByteArray.mk #[])
          let mut p2s : Array ByteArray := Array.replicate n (ByteArray.mk #[])
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
            p1s := p1s.set! idx (ByteArray.mk p1Bytes)
            p2s := p2s.set! idx (ByteArray.mk p2Bytes)
          let rc : UInt8 := host.blsPairing p1s p2s
          if rc == 0 then
            VM.pushSmallInt 0
          else if rc == 1 then
            VM.pushSmallInt (-1)
          else
            throw .unknown  -- blst error: C++ bls.cpp throws VmError{Excno::unknown}

      | .blsPushR =>
          VM.push (.int (.num blsR))
  | _ => next

end TvmLean

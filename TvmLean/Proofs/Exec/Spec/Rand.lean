import TvmLean.Proofs.Exec.Spec.HashExt

/-!
# Specifications: `RANDU256`, `RAND`, `SETRAND`, `ADDRAND`

The random numbers of the VM (C++ `generate_randu256`, `exec_randu256`, `exec_rand_int`,
`exec_set_rand`, tonops.cpp) hash the seed `c7[0][6]`: SHA-512 for a new seed and a number, SHA-256
of the seed and an integer for `ADDRAND`. The handlers of the model (`VM.generateRandu256`,
TvmLean/Semantics/VM/Ops/State.lean; TvmLean/Semantics/Exec/TonEnv/Rand.lean, Randu256.lean,
SetRand.lean) are written here again with the digests `HashExt.digest 1` and `HashExt.digest 0`
(irreducible: no run computes a hash of its input, whose terms are otherwise unfolded as far as they
go), the same programs (both sides unfolded, the digests the same by `Rand.digest_sha512` and
`HashExt.digest_sha256`):

* `Rand.gen`: `VM.generateRandu256`; `Rand.randu256Prog`, `Rand.randProg`, `Rand.setRandProg mix`;
* `Spec.randu256`, `Spec.rand`, `Spec.setRand` (`vm_spec`): the instructions run as these programs.
-/

namespace TvmLean

namespace Rand

/-- `VM.generateRandu256` (C++ `generate_randu256`, tonops.cpp:537-566), the SHA-512 of the seed
`HashExt.digest 1`. -/
def gen : VM Int := do
  let st ← get
  match st.regs.c7[0]? with
  | none =>
      throw .rangeChk
  | some (Value.tuple params) =>
      if 255 < params.size then
        throw .typeChk
      match params[6]? with
      | none =>
          throw .rangeChk
      | some (Value.int (.num seed)) =>
          if decide (seed < 0 ∨ seed ≥ intPow2 256) then
            throw .rangeChk
          let seedBytes := natToBytesBEFixed seed.toNat 32
          let digest := (HashExt.digest 1 seedBytes).data
          let newSeedNat := bytesToNatBE (digest.extract 0 32)
          let randNat := bytesToNatBE (digest.extract 32 64)
          let newSeed : Int := Int.ofNat newSeedNat
          let rand : Int := Int.ofNat randNat

          let (params', tpay) := tupleExtendSetIndex params 6 (Value.int (.num newSeed))
          let outerSize := st.regs.c7.size
          let c7' := st.regs.c7.set! 0 (Value.tuple params')
          let mut st' := { st with regs := { st.regs with c7 := c7' } }
          if tpay > 0 then
            st' := st'.consumeTupleGas tpay
          st' := st'.consumeTupleGas outerSize
          set st'
          return rand
      | some (Value.int .nan) =>
          throw .rangeChk
      | some _ =>
          throw .typeChk
  | some _ =>
      throw .typeChk

/-- `RANDU256` (C++ `exec_randu256`): a random 256-bit number. -/
def randu256Prog : VM Unit := do
  let y ← gen
  VM.pushIntQuiet (.num y) false

/-- `RAND` (C++ `exec_rand_int`): `x * y >> 256` for the `x` popped and a random `y`. -/
def randProg : VM Unit := do
  let x ← VM.popIntFinite
  let y ← gen
  let z := floorDivPow2 (x * y) 256
  VM.pushIntQuiet (.num z) false

/-- `SETRAND` (`mix` false) and `ADDRAND` (`mix` true) (C++ `exec_set_rand`, tonops.cpp): the seed
set to the `x` popped, or to the SHA-256 (`HashExt.digest 0`) of the seed and `x`. -/
def setRandProg (mix : Bool) : VM Unit := do
  let x ← VM.popIntFinite
  if decide (x < 0 ∨ x ≥ intPow2 256) then
    throw .rangeChk
  let st ← get
  match st.regs.c7[0]? with
  | none => throw .rangeChk
  | some (Value.tuple params) =>
      if decide (255 < params.size) then
        throw .typeChk
      let newSeed : Int ←
        if mix then
          match params[6]? with
          | none => throw .rangeChk
          | some (Value.int (.num seed)) =>
              if decide (seed < 0 ∨ seed ≥ intPow2 256) then
                throw .rangeChk
              let seedBytes := natToBytesBEFixed seed.toNat 32
              let xBytes := natToBytesBEFixed x.toNat 32
              let digest := (HashExt.digest 0 (seedBytes ++ xBytes)).data
              pure (Int.ofNat (bytesToNatBE digest))
          | some (Value.int .nan) => throw .rangeChk
          | some _ => throw .typeChk
        else
          pure x
      let (params', tpay) := tupleExtendSetIndex params 6 (.int (.num newSeed))
      let outerSize := st.regs.c7.size
      let c7' := st.regs.c7.set! 0 (.tuple params')
      set { st with regs := { st.regs with c7 := c7' } }
      if tpay > 0 then
        VM.consumeGas (Int.ofNat tpay * tupleEntryGasPrice)
      VM.consumeGas (Int.ofNat outerSize * tupleEntryGasPrice)
  | some _ => throw .typeChk

/-- SHA-512 as `HashExt.digest 1`. -/
theorem digest_sha512 (bs : Array UInt8) : HashExt.digest 1 bs = ByteArray.mk (sha512Digest bs) := by
  with_unfolding_all rfl

end Rand

namespace Spec

set_option maxHeartbeats 1000000 in
/-- `RANDU256` runs as `Rand.randu256Prog`. -/
@[vm_spec] theorem randu256 (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .randu256)) st = ExceptT.run Rand.randu256Prog st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, Rand.randu256Prog, Rand.gen, VM.generateRandu256, Rand.digest_sha512,
    VM.run_bind, VM.run_get, VM.bindRes_ok]
  try rfl

set_option maxHeartbeats 1000000 in
/-- `RAND` runs as `Rand.randProg`. -/
@[vm_spec] theorem rand (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .rand)) st = ExceptT.run Rand.randProg st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, Rand.randProg, Rand.gen, VM.generateRandu256, Rand.digest_sha512,
    VM.run_bind, VM.run_get, VM.bindRes_ok]
  try rfl

set_option maxHeartbeats 1000000 in
/-- `SETRAND` and `ADDRAND` run as `Rand.setRandProg`. -/
@[vm_spec] theorem setRand (st : VmState) (mix : Bool) :
    ExceptT.run (execInstr (.tonEnvOp (.setRand mix))) st = ExceptT.run (Rand.setRandProg mix) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, Rand.setRandProg, HashExt.digest_sha256, VM.run_bind,
    VM.run_get, VM.bindRes_ok]
  try rfl

end Spec

end TvmLean

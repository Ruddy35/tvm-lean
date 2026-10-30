import TvmLean.Proofs.Exec.Eval
import TvmLean.Proofs.Tx.Shape

/-!
# Specifications: `HASHEXT` with an immediate hash

`HASHEXT{A}{R} h` (C++ `exec_hash_ext`, tonops.cpp) hashes the bits of the `cnt` slices and builders
under the count with the hash `h` (0 SHA-256, 1 SHA-512, 2 BLAKE2b-512, 3 Keccak-256, 4 Keccak-512) and
pushes the digest (an integer, or a tuple of integers of 32-byte chunks, or stored in a builder with
`A`). The model's handler (TvmLean/Semantics/Exec/Crypto/HashExt.lean) also reads the hash from the
stack (`h = 255`); a run on it with an immediate hash unfolds that branch too and every case of the
digest. Here, for an immediate hash, the handler is `HashExt.prog h` (by `rfl`): the same program
without the branch of the hash from the stack, the digest a term (`HashExt.digest`, irreducible, so
that no run computes a hash of its input), the loop over its bytes of `HASHEXTA` the bits of the
digest (`HashExt.outBitsLoop`, `HashExt.bits`). SHA-256 gives 32 bytes (`HashExt.digest_size_sha256`).
-/

namespace TvmLean

namespace HashExt

/-- The digest `HASHEXT` pushes for the hash `h` of the bytes `bs` (C++ `vm::Hasher`). -/
@[irreducible] def digest (h : Nat) (bs : Array UInt8) : ByteArray :=
  match h with
  | 0 => ByteArray.mk (sha256Digest bs)
  | 1 => ByteArray.mk (sha512Digest bs)
  | 2 => Blake2b.blake2b512 (ByteArray.mk bs)
  | 3 => Keccak.keccak256 (ByteArray.mk bs)
  | _ => Keccak.keccak512 (ByteArray.mk bs)

/-- The bits of the digest `d`, a byte after another (what `HASHEXTA` stores). -/
def bits (d : ByteArray) : BitString :=
  (List.range' 0 d.size).foldl (fun r j => r ++ natToBits (d.get! j).toNat 8) #[]

/-- The loop of the handler over the bytes of the digest (`HASHEXTA`). -/
def outBitsLoop (digest : ByteArray) : VM BitString :=
  forIn [0:digest.size] (#[] : BitString) fun j r => do
    pure PUnit.unit
    pure (ForInStep.yield (r ++ natToBits (digest.get! j).toNat 8))

/-- The loop over the bytes of the digest is `bits`. -/
@[vm_run] theorem run_outBitsLoop (d : ByteArray) (st : VmState) :
    ExceptT.run (outBitsLoop d) st = (.ok (bits d), st) := by
  unfold outBitsLoop bits
  simp only [pure_bind, Std.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, VM.run_pure,
    Std.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]

set_option maxHeartbeats 1000000 in
/-- The handler of `HASHEXT h` with the hash `h` an immediate (not 255: from the stack), as the model
writes it (TvmLean/Semantics/Exec/Crypto/HashExt.lean, C++ `exec_hash_ext`, tonops.cpp), the digest
`HashExt.digest`. -/
def prog (h : Nat) (append rev : Bool) : VM Unit := do
  let gv : Nat := (← get).globalVersion
  let stBeforeCnt ← get
  let depth : Nat := stBeforeCnt.stack.size
  let maxCntInt : Int := Int.ofNat depth - 1 - (if append ∧ gv ≥ 9 then 1 else 0)
  let cntVal ← VM.popInt
  let cnt : Nat ←
    match cntVal with
    | .nan => throw .rangeChk
    | .num n =>
        if decide (n < 0 ∨ n > maxCntInt) then
          throw .rangeChk
        else
          pure n.toNat
  let bytesPerGasUnit ←
    match h with
    | 0 => pure 33
    | 1 => pure 16
    | 2 => pure 19
    | 3 => pure 11
    | 4 => pure 6
    | _ => throw .rangeChk
  let st0 ← get
  let stack0 := st0.stack
  let mut totalBits : Nat := 0
  let mut gasConsumed : Int := 0
  let mut acc : BitByteAcc := {}
  for i in [0:cnt] do
    let idx : Nat := if rev then i else (cnt - 1 - i)
    let entry : Value := stack0[stack0.size - 1 - idx]!
    let (bits, size) ←
      match entry with
      | .slice s => pure (s.readBits s.bitsRemaining, s.bitsRemaining)
      | .builder b => pure (b.bits, b.bits.size)
      | _ =>
          modify fun st => { st with stack := st.stack.take (st.stack.size - cnt) }
          throw .typeChk
    totalBits := totalBits + size
    let gasTotal : Int :=
      (Int.ofNat (i + 1) * hashExtEntryGasPrice) +
        Int.ofNat (((totalBits / 8) / bytesPerGasUnit))
    VM.consumeGas (gasTotal - gasConsumed)
    gasConsumed := gasTotal
    acc := acc.appendBits bits
  modify fun st => { st with stack := st.stack.take (st.stack.size - cnt) }
  let inputBytes ←
    match acc.finish with
    | .ok bs => pure bs
    | .error e => throw e
  let digest : ByteArray := HashExt.digest h inputBytes
  if append then
    let b ← VM.popBuilder
    if !b.canExtendBy (digest.size * 8) then
      throw .cellOv
    let outBits ← outBitsLoop digest
    VM.push (.builder (b.storeBits outBits))
  else
    if digest.size ≤ 32 then
      let n := byteArrayToNatBE digest
      VM.pushIntQuiet (.num (Int.ofNat n)) false
    else
      VM.push (.tuple (hashExtChunks digest ((digest.size - 0 + 31) / 32) 0 #[]))

theorem digest_sha256 (bs : Array UInt8) : digest 0 bs = ByteArray.mk (sha256Digest bs) := by
  with_unfolding_all rfl

/-- SHA-256 gives 32 bytes (`sha256Digest_size`). -/
@[vm_run] theorem digest_size_sha256 (bs : Array UInt8) : (digest 0 bs).size = 32 := by
  rw [digest_sha256]
  exact sha256Digest_size bs

end HashExt

/-- The dispatch of `execInstr` to the handler of `HASHEXT`. -/
theorem execInstr_hashExt (h : Nat) (a r : Bool) (st : VmState) :
    ExceptT.run (execInstr (.cryptoOp (.hashExt h a r))) st =
      ExceptT.run (execInstrCryptoHashExt (.cryptoOp (.hashExt h a r)) (pure ())) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok]

namespace Spec

/-- `HASHEXT{A}{R} 0` (SHA-256): `HashExt.prog 0`. -/
@[vm_spec] theorem hashExt_sha256 (st : VmState) (a r : Bool) :
    ExceptT.run (execInstr (.cryptoOp (.hashExt 0 a r))) st = ExceptT.run (HashExt.prog 0 a r) st := by
  rw [execInstr_hashExt]
  with_unfolding_all rfl

/-- `HASHEXT{A}{R} 1` (SHA-512): `HashExt.prog 1`. -/
@[vm_spec] theorem hashExt_sha512 (st : VmState) (a r : Bool) :
    ExceptT.run (execInstr (.cryptoOp (.hashExt 1 a r))) st = ExceptT.run (HashExt.prog 1 a r) st := by
  rw [execInstr_hashExt]
  with_unfolding_all rfl

/-- `HASHEXT{A}{R} 2` (BLAKE2b-512): `HashExt.prog 2`. -/
@[vm_spec] theorem hashExt_blake2b (st : VmState) (a r : Bool) :
    ExceptT.run (execInstr (.cryptoOp (.hashExt 2 a r))) st = ExceptT.run (HashExt.prog 2 a r) st := by
  rw [execInstr_hashExt]
  with_unfolding_all rfl

/-- `HASHEXT{A}{R} 3` (Keccak-256): `HashExt.prog 3`. -/
@[vm_spec] theorem hashExt_keccak256 (st : VmState) (a r : Bool) :
    ExceptT.run (execInstr (.cryptoOp (.hashExt 3 a r))) st = ExceptT.run (HashExt.prog 3 a r) st := by
  rw [execInstr_hashExt]
  with_unfolding_all rfl

/-- `HASHEXT{A}{R} 4` (Keccak-512): `HashExt.prog 4`. -/
@[vm_spec] theorem hashExt_keccak512 (st : VmState) (a r : Bool) :
    ExceptT.run (execInstr (.cryptoOp (.hashExt 4 a r))) st = ExceptT.run (HashExt.prog 4 a r) st := by
  rw [execInstr_hashExt]
  with_unfolding_all rfl

end Spec

end TvmLean

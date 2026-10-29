import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: hashes and signatures

In the format of `Proofs/Exec/Spec/Stack.lean`. Nothing is computed: the hash of a cell is the
term `cellHash c` (the representation hash of `c` as an integer, `Cell.hashBytes`), and the result
of `CHKSIGNU` the term `chkSignU gv hash key sig` (`Ed25519.verify` of the model on the arguments as
bytes). Both are irreducible, so that no unification evaluates them; a statement about a contract
keeps them as they are (e.g. "the signature verified": `chkSignU ... = true`).

The representation hash has 32 bytes, so `cellHash c < 2^256`; the model checks it (`HASHSU`
pushes it with `push_int_quiet`, int_ov if it did not fit), and the specifications keep that check
as a case.

`CHKSIGNS` and `P256_CHKSIGNS` check a signature of the bytes of a slice: their results are the terms
`chkSignS gv data key sig` and `p256ChkSignS data key sig` (`Ed25519.verify`, `P256.verify` of the
model on the bits as bytes), irreducible as well; the bytes of the data slice are read by
`prefetchBytesCellUnd_eq`. `RIST255_MULBASE` and `RIST255_QMULBASE` push the term
`rist255MulBase x` (`Ristretto255.mulBase` of the model), the encoding of a point kept as a term in
their proofs.
-/

namespace TvmLean

/-- The representation hash of `c` as an unsigned integer (C++ `get_hash().as_bitslice()` read as
a 256-bit unsigned integer). Irreducible: symbolic execution never evaluates it. -/
@[irreducible] def cellHash (c : Cell) : Nat := bytesToNatBE (Cell.hashBytes c)

theorem cellHash_eq (c : Cell) : cellHash c = bytesToNatBE (Cell.hashBytes c) := by
  unfold cellHash; rfl

/-- The result of `CHKSIGNU` on the hash `h`, the 512 signature bits `sig` and the key `k` at
global version `gv` (C++ `exec_ed25519_check_signature`): the verification of OpenSSL
(`Ed25519.verify`) of the signature of the 32 bytes of `h` with the 32 bytes of `k`; from version
14 the zero key and the identity encoding (`00..00`, `01 00..00`) are refused first. Irreducible:
symbolic execution keeps it as a term. -/
@[irreducible] def chkSignU (gv : Nat) (h k : Nat) (sig : BitString) : Bool :=
  let keyBytes := natToBytesBEFixed k 32
  let weakKey : Bool := (gv ≥ 14) && (keyBytes[0]! == 0 || keyBytes[0]! == 1) &&
    (List.range 31).all (fun j => keyBytes[j + 1]! == 0)
  !weakKey && Ed25519.verify (natToBytesBEFixed h 32) keyBytes (bitStringToBytesBE sig)

/-- Before version 14 `CHKSIGNU` is `Ed25519.verify`. -/
theorem chkSignU_of_lt (gv : Nat) (h k : Nat) (sig : BitString) (hv : gv < 14) :
    chkSignU gv h k sig = Ed25519.verify (natToBytesBEFixed h 32) (natToBytesBEFixed k 32) (bitStringToBytesBE sig) := by
  unfold chkSignU
  have : ¬ gv ≥ 14 := by omega
  simp [this]

/-- `CHKSIGNU` succeeds only if `Ed25519.verify` does. -/
theorem verify_of_chkSignU {gv : Nat} {h k : Nat} {sig : BitString} (hc : chkSignU gv h k sig = true) :
    Ed25519.verify (natToBytesBEFixed h 32) (natToBytesBEFixed k 32) (bitStringToBytesBE sig) = true := by
  unfold chkSignU at hc
  simp only [Bool.and_eq_true] at hc
  exact hc.2

/-- The result of `CHKSIGNS` on the data bits `data` (a whole number of bytes), the key `k` and the
512 signature bits `sig` at global version `gv` (C++ `exec_ed25519_check_signature` with
`from_slice`): as `chkSignU`, the verification of OpenSSL (`Ed25519.verify`) of the signature of the
bytes of `data` with the 32 bytes of `k`, the zero key and the identity encoding refused first from
version 14. Irreducible: symbolic execution keeps it as a term. -/
@[irreducible] def chkSignS (gv : Nat) (data : BitString) (k : Nat) (sig : BitString) : Bool :=
  let keyBytes := natToBytesBEFixed k 32
  let weakKey : Bool := (gv ≥ 14) && (keyBytes[0]! == 0 || keyBytes[0]! == 1) &&
    (List.range 31).all (fun j => keyBytes[j + 1]! == 0)
  !weakKey && Ed25519.verify (bitStringToBytesBE data) keyBytes (bitStringToBytesBE sig)

/-- The result of `P256_CHKSIGNS` on the data bits `data` (a whole number of bytes), the 264 bits of
the key `key` and the 512 signature bits `sig` (C++ `exec_p256_chksign` with `from_slice`): the
verification of the model (`P256.verify`) on them as bytes. Irreducible: symbolic execution keeps
it as a term. -/
@[irreducible] def p256ChkSignS (data key sig : BitString) : Bool :=
  P256.verify (bitStringToBytesBE data) (bitStringToBytesBE key) (bitStringToBytesBE sig)

/-- The result of `RIST255_MULBASE` and `RIST255_QMULBASE` on the scalar `x` (below the order of the
group; C++ `crypto_scalarmult_ristretto255_base` of libsodium): the encoding of `x` times the base
point as an integer, and whether it is not the identity (`Ristretto255.mulBase` of the 32 bytes of
`x`, little-endian). Irreducible: symbolic execution keeps it as a term. -/
@[irreducible] def rist255MulBase (x : Nat) : Nat × Bool :=
  (bytesToNatBE (Ristretto255.mulBase (natToBytesBEFixed x 32).reverse).1,
   (Ristretto255.mulBase (natToBytesBEFixed x 32).reverse).2)

/-- The order `l` of the ristretto255 group (`RIST255_PUSHL`). -/
theorem rist255L_eq :
    rist255L = 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
  unfold rist255L; rfl

/-- The first `n` bytes of a slice (C++ `prefetch_bytes`): cell_und if it has fewer bits. -/
theorem prefetchBytesCellUnd_eq (d : Slice) (n : Nat) : d.prefetchBytesCellUnd n =
    if d.haveBits (n * 8) then .ok (bitStringToBytesBE (d.readBits (n * 8))) else .error .cellUnd := by
  unfold Slice.prefetchBytesCellUnd
  cases h : d.haveBits (n * 8) <;> simp [h] <;> rfl

/-- A 256-bit unsigned integer as 32 bytes (C++ `export_bits` of `exec_ed25519_check_signature`). -/
theorem exportUInt256BE_num (x : Int) : exportUInt256BE (.num x) =
    if 0 ≤ x ∧ x.toNat < 2 ^ 256 then .ok (natToBytesBEFixed x.toNat 32) else .error .rangeChk := by
  have hl : uint256Limit = 2 ^ 256 := by unfold uint256Limit; rfl
  by_cases h1 : x < 0
  · rw [if_neg (by omega)]
    simp only [exportUInt256BE, h1, if_true]
    rfl
  · by_cases h2 : 2 ^ 256 ≤ x
    · rw [if_neg (by omega)]
      have h3 : x.toNat ≥ uint256Limit := by rw [hl]; omega
      simp only [exportUInt256BE, h1, h3, if_true, if_false]
      rfl
    · rw [if_pos (by omega)]
      have h3 : ¬ x.toNat ≥ uint256Limit := by rw [hl]; omega
      simp only [exportUInt256BE, h1, h3, if_false]
      rfl

/-- The 64 bytes of a signature (C++ `prefetch_bytes`). -/
theorem prefetchBytesCellUnd_64 (sig : Slice) : sig.prefetchBytesCellUnd 64 =
    if sig.haveBits 512 then .ok (bitStringToBytesBE (sig.readBits 512)) else .error .cellUnd := by
  unfold Slice.prefetchBytesCellUnd
  cases h : sig.haveBits 512 <;> simp [h] <;> rfl

/-- The count of signature checks (C++ `register_chksgn_call`, vm.h:434-443) as cases of the
state: from version 4 one more check, free (counted as free gas) for the first
`chksgnFreeCount`, then charged `chksgnGasPrice`. (Used by `vm_step`, not by `vm_simp`.) -/
theorem VmState.registerChkSgnCall_eq (st : VmState) :
    st.registerChkSgnCall =
      if 4 ≤ st.globalVersion then
        if st.chksgnCounter + 1 ≤ chksgnFreeCount then
          { st with chksgnCounter := st.chksgnCounter + 1, freeGasConsumed := st.freeGasConsumed + chksgnGasPrice }
        else { st with chksgnCounter := st.chksgnCounter + 1, gas := st.gas.consume chksgnGasPrice }
      else st := by
  unfold VmState.registerChkSgnCall
  by_cases h1 : 4 ≤ st.globalVersion
  · have h1' : ¬ st.globalVersion < 4 := by omega
    by_cases h2 : st.chksgnCounter + 1 ≤ chksgnFreeCount
    · have h2' : ¬ st.chksgnCounter + 1 > chksgnFreeCount := by omega
      simp [h1, h1', h2, h2']
    · have h2' : st.chksgnCounter + 1 > chksgnFreeCount := by omega
      simp [h1, h1', h2, h2', VmState.consumeGas]
  · have h1' : st.globalVersion < 4 := by omega
    simp [h1, h1']

/-- A pair whose second component is a case is the case of pairs (a result whose state is a case,
`VmState.registerChkSgnCall_eq`). -/
theorem VM.pair_ite {α β : Type} (a : α) (c : Prop) [Decidable c] (x y : β) :
    (a, if c then x else y) = if c then (a, x) else (a, y) := by
  split <;> rfl

namespace Spec

/-- `HASHSU` (C++ `exec_compute_hash` for a slice, cryptoops.cpp): the slice is made a cell
(`cell_create_gas_price` charged; cell_ov if its references are too deep) and its hash pushed. -/
@[vm_spec] theorem hashSU (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cryptoOp .hashSU)) st =
      if Cell.refsDepthOk sl.toCellRemaining.refs then
        if cellHash sl.toCellRemaining < 2 ^ 256 then
          (.ok (), { st with stack := s.push (.int (.num (cellHash sl.toCellRemaining))),
                             gas := st.gas.consume cellCreateGasPrice })
        else (.error .intOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice })
      else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice }) := by
  simp only [cellHash_eq]
  vm_simp [hs, VM.checkNewCellDepth, VmState.consumeGas]
  generalize bytesToNatBE sl.toCellRemaining.hashBytes = x
  split
  · by_cases hx : x < 2 ^ 256
    · rw [if_pos (by omega), if_pos hx]
    · rw [if_neg (by omega), if_neg hx]
  · rfl

/-- `HASHCU` (C++ `exec_compute_hash` for a cell): the hash of the cell is pushed. -/
@[vm_spec] theorem hashCU (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr (.cryptoOp .hashCU)) st =
      if cellHash c < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (cellHash c))) })
      else (.error .intOv, { st with stack := s }) := by
  simp only [cellHash_eq]
  vm_simp [hs]
  generalize bytesToNatBE c.hashBytes = x
  by_cases hx : x < 2 ^ 256
  · rw [if_pos (by omega), if_pos hx]
  · rw [if_neg (by omega), if_neg hx]

/-- `CHKSIGNU` (C++ `exec_ed25519_check_signature`, cryptoops.cpp) on the stack `s h sig k`: the
key, the signature and the hash are popped; the hash and the key must be 256-bit unsigned
integers (range_chk) and the signature have 512 bits (cell_und); the check is counted
(`registerChkSgnCall`: free for the first ten from version 4) and its result
(`chkSignU`, `-1` or `0`) pushed. -/
@[vm_spec] theorem chkSignU (st : VmState) (s : Stack) (h : Int) (sig : Slice) (k : Int)
    (hs : st.stack = ((s.push (.int (.num h))).push (.slice sig)).push (.int (.num k))) :
    ExceptT.run (execInstr (.cryptoOp .chkSignU)) st =
      if 0 ≤ h ∧ h.toNat < 2 ^ 256 then
        if sig.haveBits 512 then
          if 0 ≤ k ∧ k.toNat < 2 ^ 256 then
            (.ok (), { st with
              stack := s.push (.int (.num (if TvmLean.chkSignU st.globalVersion h.toNat k.toNat (sig.readBits 512)
                                              then -1 else 0))) }.registerChkSgnCall)
          else (.error .rangeChk, { st with stack := s })
        else (.error .cellUnd, { st with stack := s })
      else (.error .rangeChk, { st with stack := s }) := by
  vm_simp [hs]
  rw [exportUInt256BE_num h, exportUInt256BE_num k, prefetchBytesCellUnd_64]
  by_cases c1 : 0 ≤ h ∧ h.toNat < 2 ^ 256
  · simp only [if_pos c1]
    by_cases c2 : sig.haveBits 512 = true
    · simp only [if_pos c2]
      by_cases c3 : 0 ≤ k ∧ k.toNat < 2 ^ 256
      · simp only [if_pos c3, TvmLean.chkSignU]
        vm_simp
        simp only [VmState.registerChkSgnCall]
        by_cases g1 : st.globalVersion < 4
        · simp [g1]
        · by_cases g2 : st.chksgnCounter + 1 > chksgnFreeCount <;> simp [g1, g2, VmState.consumeGas]
      · simp only [if_neg c3]; vm_simp
    · simp only [if_neg c2]; vm_simp
  · simp only [if_neg c1]; vm_simp


set_option maxHeartbeats 4000000 in
/-- `CHKSIGNS` (C++ `exec_ed25519_check_signature` with `from_slice`, tonops.cpp) on the stack
`s d sig k`: the key, the signature and the data are popped; the data must be a whole number of
bytes (cell_und), at most 128 (range_chk; a slice has at most 127), the signature have 512 bits
(cell_und) and the key be a 256-bit unsigned integer (range_chk); the check is counted
(`registerChkSgnCall`) and its result (`chkSignS`, `-1` or `0`) pushed. -/
@[vm_spec] theorem chkSignS (st : VmState) (s : Stack) (d sig : Slice) (k : Int)
    (hs : st.stack = ((s.push (.slice d)).push (.slice sig)).push (.int (.num k))) :
    ExceptT.run (execInstr (.cryptoOp .chkSignS)) st =
      if d.bitsRemaining % 8 ≠ 0 then (.error .cellUnd, { st with stack := s })
      else if d.bitsRemaining / 8 > 128 then (.error .rangeChk, { st with stack := s })
      else if d.haveBits (d.bitsRemaining / 8 * 8) then
        if sig.haveBits 512 then
          if 0 ≤ k ∧ k.toNat < 2 ^ 256 then
            (.ok (), { st with
              stack := s.push (.int (.num (if TvmLean.chkSignS st.globalVersion
                (d.readBits (d.bitsRemaining / 8 * 8)) k.toNat (sig.readBits 512) then -1 else 0))) }.registerChkSgnCall)
          else (.error .rangeChk, { st with stack := s })
        else (.error .cellUnd, { st with stack := s })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]
  rw [exportUInt256BE_num k, prefetchBytesCellUnd_64, prefetchBytesCellUnd_eq]
  by_cases c0 : d.bitsRemaining % 8 = 0
  · simp only [c0, if_true]
    by_cases c1 : d.bitsRemaining / 8 > 128
    · simp only [if_pos c1]
    · simp only [if_neg c1]
      by_cases c2 : d.haveBits (d.bitsRemaining / 8 * 8) = true
      · simp only [if_pos c2]
        by_cases c3 : sig.haveBits 512 = true
        · simp only [if_pos c3]
          by_cases c4 : 0 ≤ k ∧ k.toNat < 2 ^ 256
          · simp only [if_pos c4, TvmLean.chkSignS]
            vm_simp
            simp only [VmState.registerChkSgnCall]
            by_cases g1 : st.globalVersion < 4
            · simp [g1]
            · by_cases g2 : st.chksgnCounter + 1 > chksgnFreeCount <;> simp [g1, g2, VmState.consumeGas]
          · simp only [if_neg c4]; vm_simp
        · simp only [if_neg c3]; vm_simp
      · simp only [if_neg c2]; vm_simp
  · simp only [c0]; vm_simp

set_option maxHeartbeats 4000000 in
/-- `P256_CHKSIGNS` (C++ `exec_p256_chksign` with `from_slice`, tonops.cpp) on the stack
`s d sig key`: the key, the signature and the data slices are popped; the data must be a whole
number of bytes (cell_und), at most 128 (range_chk), the signature have 512 bits and the key 264
(cell_und); `p256_chksgn_gas_price` is charged (out of gas at once from version 4) and the result
(`p256ChkSignS`, `-1` or `0`) pushed. -/
@[vm_spec] theorem p256ChkSignS (st : VmState) (s : Stack) (d sig key : Slice)
    (hs : st.stack = ((s.push (.slice d)).push (.slice sig)).push (.slice key)) :
    ExceptT.run (execInstr (.cryptoOp (.ext .p256ChkSignS))) st =
      if d.bitsRemaining % 8 ≠ 0 then (.error .cellUnd, { st with stack := s })
      else if d.bitsRemaining / 8 > 128 then (.error .rangeChk, { st with stack := s })
      else if d.haveBits (d.bitsRemaining / 8 * 8) then
        if sig.haveBits 512 then
          if key.haveBits 264 then
            if ({ st with stack := s, gas := st.gas.consume p256ChksgnGasPrice } : VmState).gasExhaustedNow then
              (.error .outOfGas, { st with stack := s, gas := st.gas.consume p256ChksgnGasPrice })
            else
              (.ok (), { st with
                stack := s.push (.int (.num (if TvmLean.p256ChkSignS (d.readBits (d.bitsRemaining / 8 * 8))
                  (key.readBits 264) (sig.readBits 512) then -1 else 0)))
                gas := st.gas.consume p256ChksgnGasPrice })
          else (.error .cellUnd, { st with stack := s })
        else (.error .cellUnd, { st with stack := s })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]
  rw [prefetchBytesCellUnd_eq d, prefetchBytesCellUnd_eq sig, prefetchBytesCellUnd_eq key]
  by_cases c0 : d.bitsRemaining % 8 = 0
  · simp only [c0, bne_self_eq_false, Bool.false_eq_true, if_false, if_true]
    by_cases c1 : d.bitsRemaining / 8 > 128
    · simp only [if_pos c1]
    · simp only [if_neg c1]
      by_cases c2 : d.haveBits (d.bitsRemaining / 8 * 8) = true
      · simp only [if_pos c2]
        by_cases c3 : sig.haveBits 512 = true
        · simp only [Nat.reduceMul, if_pos c3]
          by_cases c4 : key.haveBits 264 = true
          · -- the definition unfolded everywhere, also in the instance of the `if` (`rw`, not `simp`)
            simp only [if_pos c4]
            rw [TvmLean.p256ChkSignS]
            vm_simp [VmState.consumeGas]
          · simp only [if_neg c4]; vm_simp
        · simp only [Nat.reduceMul, if_neg c3]; vm_simp
      · simp only [if_neg c2]; vm_simp
  · have c0' : (d.bitsRemaining % 8 != 0) = true := by simp [c0]
    simp only [c0', c0, if_true]; vm_simp

section Ristretto

-- the encoding of a point is kept as a term (unfolded, the run of a step evaluates the scalar
-- multiplication of the base point)
attribute [local irreducible] TvmLean.Ristretto255.encode

set_option maxHeartbeats 4000000 in
/-- `RIST255_MULBASE` (C++ `exec_ristretto255_mul_base`, tonops.cpp) on the stack `s n`: the scalar
`n mod l` (`rist255L`); `rist255_mulbase_gas_price` charged (out of gas at once from version 4);
from version 14 a scalar 0 gives 0, and the identity is range_chk; else the encoding of the product
(`rist255MulBase`) is pushed. -/
@[vm_spec] theorem rist255MulBase (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255MulBase))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255MulBaseGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255MulBaseGasPrice })
      else if 14 ≤ st.globalVersion ∧ n % rist255L = 0 then
        (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255MulBaseGasPrice })
      else if (TvmLean.rist255MulBase (n % rist255L).toNat).2 = false ∧ 14 ≤ st.globalVersion then
        (.error .rangeChk, { st with stack := s, gas := st.gas.consume rist255MulBaseGasPrice })
      else
        (.ok (), { st with stack := s.push (.int (.num (TvmLean.rist255MulBase (n % rist255L).toNat).1)),
                           gas := st.gas.consume rist255MulBaseGasPrice }) := by
  have hx0 : 0 ≤ n % rist255L := Int.emod_nonneg _ (by rw [rist255L_eq]; decide)
  have hx1 : n % rist255L < rist255L := Int.emod_lt_of_pos _ (by rw [rist255L_eq]; decide)
  vm_simp [hs, VmState.consumeGas, intValMod]
  generalize n % rist255L = x at hx0 hx1 ⊢
  rw [rist255L_eq] at hx1
  rw [exportUInt256BE_num x, if_pos (show 0 ≤ x ∧ x.toNat < 2 ^ 256 by omega)]
  rw [TvmLean.rist255MulBase]
  -- the multiplication a variable, so that no closed fact of it is decided (with `x = 0`)
  generalize Ristretto255.mulBase = f
  rcases (by omega : x = 0 ∨ 0 < x) with rfl | hpos
  · vm_simp
  · have hz : ¬ x = 0 := by omega
    simp [hz]
    vm_simp

set_option maxHeartbeats 4000000 in
/-- `RIST255_QMULBASE` (C++ `exec_ristretto255_mul_base`, quiet) on the stack `s n`: as
`RIST255_MULBASE`, the product pushed with `-1`; from version 14 a scalar 0 gives `0 -1`, and the
identity gives `0`. -/
@[vm_spec] theorem rist255QmulBase (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .rist255QmulBase))) st =
      if ({ st with stack := s, gas := st.gas.consume rist255MulBaseGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume rist255MulBaseGasPrice })
      else if 14 ≤ st.globalVersion ∧ n % rist255L = 0 then
        (.ok (), { st with stack := (s.push (.int (.num 0))).push (.int (.num (-1))),
                           gas := st.gas.consume rist255MulBaseGasPrice })
      else if (TvmLean.rist255MulBase (n % rist255L).toNat).2 = false ∧ 14 ≤ st.globalVersion then
        (.ok (), { st with stack := s.push (.int (.num 0)), gas := st.gas.consume rist255MulBaseGasPrice })
      else
        (.ok (), { st with
          stack := (s.push (.int (.num (TvmLean.rist255MulBase (n % rist255L).toNat).1))).push (.int (.num (-1))),
          gas := st.gas.consume rist255MulBaseGasPrice }) := by
  have hx0 : 0 ≤ n % rist255L := Int.emod_nonneg _ (by rw [rist255L_eq]; decide)
  have hx1 : n % rist255L < rist255L := Int.emod_lt_of_pos _ (by rw [rist255L_eq]; decide)
  vm_simp [hs, VmState.consumeGas, intValMod, exportUInt256BE?]
  generalize n % rist255L = x at hx0 hx1 ⊢
  rw [rist255L_eq] at hx1
  rw [exportUInt256BE_num x, if_pos (show 0 ≤ x ∧ x.toNat < 2 ^ 256 by omega)]
  rw [TvmLean.rist255MulBase]
  generalize Ristretto255.mulBase = f
  rcases (by omega : x = 0 ∨ 0 < x) with rfl | hpos
  · vm_simp
  · have hz : ¬ x = 0 := by omega
    simp [hz]
    vm_simp

end Ristretto

end Spec

end TvmLean

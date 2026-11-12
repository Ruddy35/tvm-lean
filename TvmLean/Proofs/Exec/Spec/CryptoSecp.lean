import TvmLean.Proofs.Exec.Spec.Crypto

/-!
# Specifications: `ECRECOVER`, `SECP256K1_XONLY_PUBKEY_TWEAK_ADD`

In the format of `Proofs/Exec/Spec/Crypto.lean`: the integers read as 32 bytes each
(`exportUInt256BE_num`, range_chk unless in `0 .. 2^256 - 1`), the gas charged (out of gas at once),
then the model's function of secp256k1 (`Secp256k1.ecrecover`, `Secp256k1.xonlyPubkeyTweakAdd`) kept
as a term; its result pushed as `Spec.secpPush` (0, or 4, the two coordinates and -1):

* `ECRECOVER` (C++ `exec_ecrecover`, tonops.cpp) on the stack `s h v r s'`: `v` in `0..255`
  (range_chk); from version 14 the recovery ids 27 and 28 are 0 and 1 (`Spec.ecrecoverId`);
* `SECP256K1_XONLY_PUBKEY_TWEAK_ADD` (C++ `exec_secp256k1_xonly_pubkey_tweak_add`) on the stack
  `s k t`.
-/

namespace TvmLean.Spec

set_option maxHeartbeats 4000000

/-- The recovery id `ECRECOVER` passes on: from version 14 the ids 27 and 28 of Ethereum are 0 and 1. -/
def ecrecoverId (gv v : Nat) : Nat := if 14 ≤ gv ∧ (v = 27 ∨ v = 28) then v - 27 else v

/-- The stack after `ECRECOVER` or `SECP256K1_XONLY_PUBKEY_TWEAK_ADD`: 0 if the library fails, else 4
(an uncompressed key), the two coordinates and -1. -/
def secpPush (s : Stack) : Option (Nat × Nat) → Stack
  | none => s.push (.int (.num 0))
  | some (x, y) => (((s.push (.int (.num 4))).push (.int (.num x))).push (.int (.num y))).push (.int (.num (-1)))

/-- `ECRECOVER` on the stack `s h v r s'`. -/
@[vm_spec] theorem ecrecover (st : VmState) (s : Stack) (h v r sg : Int)
    (hs : st.stack = (((s.push (.int (.num h))).push (.int (.num v))).push (.int (.num r))).push (.int (.num sg))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .ecrecover))) st =
      if v < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num h)) })
      else if 255 < v.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num h)) })
      else if 0 ≤ r ∧ r.toNat < 2 ^ 256 then
        if 0 ≤ sg ∧ sg.toNat < 2 ^ 256 then
          if 0 ≤ h ∧ h.toNat < 2 ^ 256 then
            if ({ st with stack := s, gas := st.gas.consume ecrecoverGasPrice } : VmState).gasExhaustedNow then
              (.error .outOfGas, { st with stack := s, gas := st.gas.consume ecrecoverGasPrice })
            else
              (.ok (), { st with stack := secpPush s (Secp256k1.ecrecover (bytesToNatBE (natToBytesBEFixed h.toNat 32))
                                   (bytesToNatBE (natToBytesBEFixed r.toNat 32)) (bytesToNatBE (natToBytesBEFixed sg.toNat 32))
                                   (ecrecoverId st.globalVersion v.toNat)),
                                 gas := st.gas.consume ecrecoverGasPrice })
          else (.error .rangeChk, { st with stack := s })
        else (.error .rangeChk, { st with stack := s })
      else (.error .rangeChk, { st with stack := s }) := by
  by_cases hv0 : v < 0
  · vm_simp [hs, hv0]
  · by_cases hv1 : 255 < v.toNat
    · vm_simp [hs, hv0, hv1]
    · by_cases hr : 0 ≤ r ∧ r.toNat < 2 ^ 256
      · by_cases hsg : 0 ≤ sg ∧ sg.toNat < 2 ^ 256
        · by_cases hh : 0 ≤ h ∧ h.toNat < 2 ^ 256
          · simp only [ecrecoverId]
            cases hres : Secp256k1.ecrecover (bytesToNatBE (natToBytesBEFixed h.toNat 32))
                (bytesToNatBE (natToBytesBEFixed r.toNat 32)) (bytesToNatBE (natToBytesBEFixed sg.toNat 32))
                (if 14 ≤ st.globalVersion ∧ (v.toNat = 27 ∨ v.toNat = 28) then v.toNat - 27 else v.toNat) with
            | none => vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hv0, hv1, hr, hsg, hh, hres, secpPush]
            | some p =>
              obtain ⟨x, y⟩ := p
              vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hv0, hv1, hr, hsg, hh, hres, secpPush]
          · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hv0, hv1, hr, hsg, hh]
        · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hv0, hv1, hr, hsg]
      · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hv0, hv1, hr]

/-- `SECP256K1_XONLY_PUBKEY_TWEAK_ADD` on the stack `s k t`. -/
@[vm_spec] theorem secp256k1XonlyPubkeyTweakAdd (st : VmState) (s : Stack) (k t : Int)
    (hs : st.stack = (s.push (.int (.num k))).push (.int (.num t))) :
    ExceptT.run (execInstr (.cryptoOp (.ext .secp256k1XonlyPubkeyTweakAdd))) st =
      if 0 ≤ k ∧ k.toNat < 2 ^ 256 then
        if 0 ≤ t ∧ t.toNat < 2 ^ 256 then
          if ({ st with stack := s, gas := st.gas.consume secp256k1XonlyPubkeyTweakAddGasPrice } : VmState).gasExhaustedNow then
            (.error .outOfGas, { st with stack := s, gas := st.gas.consume secp256k1XonlyPubkeyTweakAddGasPrice })
          else
            (.ok (), { st with stack := secpPush s (Secp256k1.xonlyPubkeyTweakAdd (bytesToNatBE (natToBytesBEFixed k.toNat 32))
                                 (bytesToNatBE (natToBytesBEFixed t.toNat 32))),
                               gas := st.gas.consume secp256k1XonlyPubkeyTweakAddGasPrice })
        else (.error .rangeChk, { st with stack := s })
      else (.error .rangeChk, { st with stack := s }) := by
  by_cases hk : 0 ≤ k ∧ k.toNat < 2 ^ 256
  · by_cases ht : 0 ≤ t ∧ t.toNat < 2 ^ 256
    · cases hres : Secp256k1.xonlyPubkeyTweakAdd (bytesToNatBE (natToBytesBEFixed k.toNat 32))
          (bytesToNatBE (natToBytesBEFixed t.toNat 32)) with
      | none => vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hk, ht, hres, secpPush]
      | some p =>
        obtain ⟨x, y⟩ := p
        vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hk, ht, hres, secpPush]
    · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hk, ht]
  · vm_simp [hs, VmState.consumeGas, exportUInt256BE_num, hk]

end TvmLean.Spec

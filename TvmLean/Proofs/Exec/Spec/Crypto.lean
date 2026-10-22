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


end Spec

end TvmLean

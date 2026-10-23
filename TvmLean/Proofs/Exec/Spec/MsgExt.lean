import TvmLean.Proofs.Exec.Spec.Msg

/-!
# Specifications: `RAWRESERVE` in every global version

`Spec.rawReserve` (`TvmLean/Proofs/Exec/Spec/Msg.lean`) holds from version 4, where the mode may be
up to 31. A mode up to 15 is in range in every version (C++ `exec_reserve_raw`, tonops.cpp:2370:
`stack.pop_smallint_range(global_version >= 4 ? 31 : 15)`), so `RAWRESERVE` with such a mode has
the same result whatever the version (`Spec.rawReserve_le15`): a contract that reserves with a
mode below 16 runs the same way in every version.
-/

namespace TvmLean

namespace Spec

set_option maxHeartbeats 1000000 in
/-- `RAWRESERVE` (C++ `exec_reserve_raw`, tonops.cpp) in any version, on the stack `s x f` with the
mode `f` in `0..15`: the amount `x` must be non-negative (range_chk), of fewer than 16 bytes
(cell_ov); the action `OutAction.reserve f x c5` becomes `c5`. -/
@[vm_spec] theorem rawReserve_le15 (st : VmState) (s : Stack) (x f : Int) (hf : 0 ≤ f ∧ f ≤ 15)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num f))) :
    ExceptT.run (execInstr (.tonEnvOp .rawReserve)) st =
      if 0 ≤ x then
        if (natLenBits x.toNat + 7) / 8 < 16 then
          if Cell.refsDepthOk #[st.regs.c5] then
            (.ok (), { st with stack := s, gas := st.gas.consume cellCreateGasPrice,
                               regs := { st.regs with c5 := OutAction.reserve f.toNat x.toNat st.regs.c5 } })
          else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice })
        else (.error .cellOv, { st with stack := s })
      else (.error .rangeChk, { st with stack := s }) := by
  have h1 : ¬ f < 0 := by omega
  have h2 : ¬ f.toNat > 15 := by omega
  have h2' : ¬ f.toNat > 31 := by omega
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    have h3 : ¬ x < 0 := by omega
    by_cases hl : (natLenBits x.toNat + 7) / 8 < 16
    · rw [if_pos hl]
      have h4 : ¬ (natLenBits x.toNat + 7) / 8 ≥ 16 := by omega
      have h5 : ¬ (natToBits 0x36e6b809 32 ++ natToBits f.toNat 8 ++
          (natToBits ((natLenBits x.toNat + 7) / 8) 4 ++ natToBits x.toNat ((natLenBits x.toNat + 7) / 8 * 8)) ++
            #[false]).size > 1023 := by
        simp only [Array.size_append, natToBits_size, List.size_toArray, List.length_cons, List.length_nil]
        omega
      by_cases hv : st.globalVersion ≥ 4
      · vm_simp [hs, hv, h1, h2, h2', h3, h4]
        simp only [VmState.consumeGas]
        split <;> rfl
      · vm_simp [hs, hv, h1, h2, h2', h3, h4]
        simp only [VmState.consumeGas]
        split <;> rfl
    · rw [if_neg hl]
      have h4 : (natLenBits x.toNat + 7) / 8 ≥ 16 := by omega
      by_cases hv : st.globalVersion ≥ 4
      · vm_simp [hs, hv, h1, h2, h2', h3, h4]
      · vm_simp [hs, hv, h1, h2, h2', h3, h4]
  · rw [if_neg hx]
    have h3 : x < 0 := by omega
    by_cases hv : st.globalVersion ≥ 4
    · vm_simp [hs, hv, h1, h2, h2', h3]
    · vm_simp [hs, hv, h1, h2, h2', h3]

end Spec

end TvmLean

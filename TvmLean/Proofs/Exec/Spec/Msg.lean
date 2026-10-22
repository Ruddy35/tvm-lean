import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: output actions

In the format of `Proofs/Exec/Spec/Stack.lean`. `SENDRAWMSG`, `SETCODE` and `RAWRESERVE` add an
action to the list in `c5` (C++ `install_output_action`): a new cell whose first reference is the old `c5`
(`OutAction.sendMsg`, `OutAction.setCode`, `OutAction.reserve`), its creation charged
(`cell_create_gas_price`, checked at the end of the step) and cell_ov if it would be too deep.
-/

namespace TvmLean

/-- The cell of the action `action_send_msg#0ec3c86d mode:(## 8) out_msg:^(MessageRelaxed X)` added
to the list `prev`. -/
def OutAction.sendMsg (mode : Nat) (prev msg : Cell) : Cell :=
  Cell.mkOrdinary (natToBits 0x0ec3c86d 32 ++ natToBits mode 8) #[prev, msg]

/-- The cell of the action `action_set_code#ad4de08e new_code:^Cell` added to the list `prev`. -/
def OutAction.setCode (prev code : Cell) : Cell :=
  Cell.mkOrdinary (natToBits 0xad4de08e 32) #[prev, code]

/-- The cell of the action `action_reserve_currency#36e6b809 mode:(## 8) currency:CurrencyCollection`
(the amount as `Grams`, no extra currencies) added to the list `prev`. -/
def OutAction.reserve (mode x : Nat) (prev : Cell) : Cell :=
  let lenBytes := (natLenBits x + 7) / 8
  Cell.mkOrdinary (natToBits 0x36e6b809 32 ++ natToBits mode 8 ++
    (natToBits lenBytes 4 ++ natToBits x (lenBytes * 8)) ++ #[false]) #[prev]

namespace Spec

/-- `SENDRAWMSG` (C++ `exec_send_raw_message`, tonops.cpp) on the stack `s msg mode`: the mode must
be in `0..255` (range_chk), the action `OutAction.sendMsg mode c5 msg` becomes `c5`. -/
@[vm_spec] theorem sendRawMsg (st : VmState) (s : Stack) (msg : Cell) (mode : Int)
    (hs : st.stack = (s.push (.cell msg)).push (.int (.num mode))) :
    ExceptT.run (execInstr (.tonEnvOp .sendRawMsg)) st =
      if 0 ≤ mode ∧ mode ≤ 255 then
        if Cell.refsDepthOk #[st.regs.c5, msg] then
          (.ok (), { st with stack := s, gas := st.gas.consume cellCreateGasPrice,
                             regs := { st.regs with c5 := OutAction.sendMsg mode.toNat st.regs.c5 msg } })
        else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice })
      else (.error .rangeChk, { st with stack := s.push (.cell msg) }) := by
  by_cases hm : 0 ≤ mode ∧ mode ≤ 255
  · have h1 : ¬ mode < 0 := by omega
    have h2 : ¬ mode.toNat > 255 := by omega
    rw [if_pos hm]
    vm_simp [hs, h1, h2, VM.checkNewCellDepth, VmState.consumeGas, OutAction.sendMsg]
  · rw [if_neg hm]
    by_cases h1 : mode < 0
    · vm_simp [hs, h1]
    · have h2 : mode.toNat > 255 := by omega
      vm_simp [hs, h1, h2]

/-- `SETCODE` (C++ `exec_set_code`): the action `OutAction.setCode c5 code` becomes `c5`. -/
@[vm_spec] theorem setCode (st : VmState) (s : Stack) (code : Cell) (hs : st.stack = s.push (.cell code)) :
    ExceptT.run (execInstr (.tonEnvOp .setCode)) st =
      if Cell.refsDepthOk #[st.regs.c5, code] then
        (.ok (), { st with stack := s, gas := st.gas.consume cellCreateGasPrice,
                           regs := { st.regs with c5 := OutAction.setCode st.regs.c5 code } })
      else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice }) := by
  vm_simp [hs, VM.checkNewCellDepth, VmState.consumeGas, OutAction.setCode]

set_option maxHeartbeats 1000000 in
/-- `RAWRESERVE` (C++ `exec_reserve_raw`, tonops.cpp) from version 4 on the stack `s x f`: the
mode `f` must be in `0..31` and the amount `x` non-negative (range_chk), of fewer than 16 bytes
(cell_ov); the action `OutAction.reserve f x c5` becomes `c5`. -/
@[vm_spec] theorem rawReserve (st : VmState) (s : Stack) (x f : Int) (hv : 4 ≤ st.globalVersion)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num f))) :
    ExceptT.run (execInstr (.tonEnvOp .rawReserve)) st =
      if 0 ≤ f ∧ f ≤ 31 then
        if 0 ≤ x then
          if (natLenBits x.toNat + 7) / 8 < 16 then
            if Cell.refsDepthOk #[st.regs.c5] then
              (.ok (), { st with stack := s, gas := st.gas.consume cellCreateGasPrice,
                                 regs := { st.regs with c5 := OutAction.reserve f.toNat x.toNat st.regs.c5 } })
            else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice })
          else (.error .cellOv, { st with stack := s })
        else (.error .rangeChk, { st with stack := s })
      else (.error .rangeChk, { st with stack := s.push (.int (.num x)) }) := by
  have hv' : st.globalVersion ≥ 4 := hv
  by_cases hf : 0 ≤ f ∧ f ≤ 31
  · rw [if_pos hf]
    have h1 : ¬ f < 0 := by omega
    have h2 : ¬ f.toNat > 31 := by omega
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
        vm_simp [hs, hv', h1, h2, h3, h4]
        simp only [VmState.consumeGas]
        split <;> rfl
      · rw [if_neg hl]
        have h4 : (natLenBits x.toNat + 7) / 8 ≥ 16 := by omega
        vm_simp [hs, hv', h1, h2, h3, h4]
    · rw [if_neg hx]
      have h3 : x < 0 := by omega
      vm_simp [hs, hv', h1, h2, h3]
  · rw [if_neg hf]
    by_cases h1 : f < 0
    · vm_simp [hs, hv', h1]
    · have h2 : f.toNat > 31 := by omega
      vm_simp [hs, hv', h1, h2]

end Spec

end TvmLean

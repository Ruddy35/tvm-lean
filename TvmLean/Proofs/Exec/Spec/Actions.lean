import TvmLean.Proofs.Exec.Spec.Msg

/-!
# Specifications: the library actions and `RAWRESERVEX`

In the format of `Proofs/Exec/Spec/Msg.lean`: `SETLIBCODE`, `CHANGELIB` and `RAWRESERVEX` add an
action to the list in `c5` (C++ `install_output_action`, tonops.cpp), a new cell whose first
reference is the old `c5`, its creation charged (`cell_create_gas_price`, checked at the end of the
step) and cell_ov if it would be too deep. The cells are written as the model's handlers build
them (`TvmLean/Semantics/Exec/Msg/`):

* `OutAction.setLibCode mode prev code`: `action_change_library#26fa1dd4 mode:(## 7)
  libref:LibRef` with `libref_ref$1 library:^Cell` (`SETLIBCODE`, C++ `exec_set_lib_code`: the byte
  `mode * 2 + 1`, the code as the second reference);
* `OutAction.changeLib mode prev hash`: the same action with `libref_hash$0 lib_hash:bits256`
  (`CHANGELIB`, C++ `exec_change_lib`: the byte `mode * 2`, then the 256 bits of the hash);
* `RAWRESERVEX` (C++ `exec_reserve_raw`, mode 1) with no extra currencies (`null`) builds the cell of
  `RAWRESERVE` (`OutAction.reserve`); with a dictionary `y` of extra currencies,
  `OutAction.reserveExtra mode x prev y`: the `Maybe ^Cell` bit set, `y` the second reference.

The mode of `SETLIBCODE` and `CHANGELIB` is up to 2 before version 4 and in `{0, 1, 2, 16, 17, 18}`
from version 4 (`pop_smallint_range(31)`, then range_chk if `(mode & ~16) > 2`, tonops.cpp:2408-2413
and 2432-2437); the mode of `RAWRESERVEX` is up to 15 before version 4 and up to 31 from version 4
(tonops.cpp:2370). Each instruction has a specification for the modes valid in every version and one
for the modes valid from version 4.
-/

namespace TvmLean

/-- The cell of the action `action_change_library#26fa1dd4 mode:(## 7) libref:(libref_ref$1
library:^Cell)` (`SETLIBCODE`) added to the list `prev`. -/
def OutAction.setLibCode (mode : Nat) (prev code : Cell) : Cell :=
  Cell.mkOrdinary (natToBits 0x26fa1dd4 32 ++ natToBits (mode * 2 + 1) 8) #[prev, code]

/-- The cell of the action `action_change_library#26fa1dd4 mode:(## 7) libref:(libref_hash$0
lib_hash:bits256)` (`CHANGELIB`) added to the list `prev`. -/
def OutAction.changeLib (mode : Nat) (prev : Cell) (hash : Nat) : Cell :=
  Cell.mkOrdinary (natToBits 0x26fa1dd4 32 ++ natToBits (mode * 2) 8 ++ natToBits hash 256) #[prev]

/-- The cell of the action `action_reserve_currency#36e6b809 mode:(## 8) currency:CurrencyCollection`
with the amount `x` as `Grams` and the dictionary of extra currencies `extra` (`RAWRESERVEX` with a
cell) added to the list `prev`. -/
def OutAction.reserveExtra (mode x : Nat) (prev extra : Cell) : Cell :=
  let lenBytes := (natLenBits x + 7) / 8
  Cell.mkOrdinary (natToBits 0x36e6b809 32 ++ natToBits mode 8 ++
    (natToBits lenBytes 4 ++ natToBits x (lenBytes * 8)) ++ #[true]) #[prev, extra]

namespace Spec

/-- `vm_simp` without contextual rewriting: in the handler of `RAWRESERVEX` the conditions of its
`if`s, as rewrite rules, rewrite each other without end. -/
syntax (name := vmSimpFlat) "vm_simp_flat" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| vm_simp_flat $[[$args,*]]?) => do
    let args := args.getD ⟨#[]⟩
    `(tactic| set_option maxRecDepth 100000 in simp (config := { contextual := false, maxSteps := 2000000 })
        (disch := vm_disch) only [TvmLean.Exec.reduceExecInstrRun,
        TvmLean.Exec.unfoldModelRun, vm_run, Array.size_push,
        Array.pop_push, Array.size_pop, if_pos, if_neg, dif_pos, dif_neg, if_true, if_false, dite_true,
        dite_false, Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false, ne_eq,
        Nat.add_sub_cancel, Nat.sub_self, Nat.add_one_sub_one, Nat.sub_zero, and_true, true_and,
        decide_eq_true_eq, decide_eq_false_iff_not, decide_not, Bool.not_not, Bool.not_true,
        Bool.not_false, Decidable.not_not, Bool.not_eq_true', Bool.not_eq_false', beq_iff_eq,
        Int.ofNat_eq_coe, Int.toNat_natCast, Bool.and_eq_true, Bool.or_eq_true, Bool.eq_false_iff, ite_not,
        ge_iff_le, gt_iff_lt, reduceIte, reduceDIte, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow,
        Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, Nat.reduceBEq,
        Nat.reduceBNe, Int.reduceAdd, Int.reduceSub, Int.reduceMul, Int.reduceNeg, Int.reducePow, Int.reduceLT,
        Int.reduceLE, Int.reduceGT, Int.reduceGE, Int.reduceEq, Int.reduceNe, Int.reduceNatCast,
        Int.reduceNatCast', Int.reduceOfNat, Int.reduceToNat, $args,*])

theorem and15_le_of_le {m : Nat} (h : m ≤ 2) : ¬ (m &&& 15) > 2 :=
  Nat.not_lt.mpr (Nat.le_trans Nat.and_le_left h)

set_option maxHeartbeats 1000000 in
/-- `SETLIBCODE` (C++ `exec_set_lib_code`) in any version, on the stack `s code mode` with the mode
in `0..2`: the action `OutAction.setLibCode mode c5 code` becomes `c5`. -/
@[vm_spec] theorem setLibCode (st : VmState) (s : Stack) (code : Cell) (mode : Int) (hm : 0 ≤ mode ∧ mode ≤ 2)
    (hs : st.stack = (s.push (.cell code)).push (.int (.num mode))) :
    ExceptT.run (execInstr (.tonEnvOp .setLibCode)) st =
      if Cell.refsDepthOk #[st.regs.c5, code] then
        (.ok (), { st with stack := s, gas := st.gas.consume cellCreateGasPrice,
                           regs := { st.regs with c5 := OutAction.setLibCode mode.toNat st.regs.c5 code } })
      else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice }) := by
  have h1 : ¬ mode < 0 := by omega
  have h2 : ¬ mode.toNat > 31 := by omega
  have h2' : ¬ mode.toNat > 2 := by omega
  have h3 := and15_le_of_le (m := mode.toNat) (by omega)
  by_cases hv : st.globalVersion ≥ 4
  · vm_simp [hs, hv, h1, h2, h2', h3, VM.checkNewCellDepth, VmState.consumeGas, OutAction.setLibCode]
  · vm_simp [hs, hv, h1, h2, h2', VM.checkNewCellDepth, VmState.consumeGas, OutAction.setLibCode]

set_option maxHeartbeats 1000000 in
/-- `SETLIBCODE` from version 4, on the stack `s code mode` with a mode valid there (`0..31`, its
bits but 16 at most 2): the action `OutAction.setLibCode mode c5 code` becomes `c5`. -/
@[vm_spec] theorem setLibCode_v4 (st : VmState) (s : Stack) (code : Cell) (mode : Int) (hv : 4 ≤ st.globalVersion)
    (hm : 0 ≤ mode ∧ mode ≤ 31 ∧ ¬ (mode.toNat &&& 15) > 2)
    (hs : st.stack = (s.push (.cell code)).push (.int (.num mode))) :
    ExceptT.run (execInstr (.tonEnvOp .setLibCode)) st =
      if Cell.refsDepthOk #[st.regs.c5, code] then
        (.ok (), { st with stack := s, gas := st.gas.consume cellCreateGasPrice,
                           regs := { st.regs with c5 := OutAction.setLibCode mode.toNat st.regs.c5 code } })
      else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice }) := by
  have hv' : st.globalVersion ≥ 4 := hv
  have h1 : ¬ mode < 0 := by omega
  have h2 : ¬ mode.toNat > 31 := by omega
  have h3 := hm.2.2
  vm_simp [hs, hv', h1, h2, h3, VM.checkNewCellDepth, VmState.consumeGas, OutAction.setLibCode]

set_option maxHeartbeats 1000000 in
/-- `CHANGELIB` (C++ `exec_change_lib`) in any version, on the stack `s h mode` with the mode in
`0..2`: the hash `h` must be a 256-bit unsigned integer (range_chk); the action
`OutAction.changeLib mode c5 h` becomes `c5`. -/
@[vm_spec] theorem changeLib (st : VmState) (s : Stack) (h mode : Int) (hm : 0 ≤ mode ∧ mode ≤ 2)
    (hs : st.stack = (s.push (.int (.num h))).push (.int (.num mode))) :
    ExceptT.run (execInstr (.tonEnvOp .changeLib)) st =
      if 0 ≤ h ∧ h < 2 ^ 256 then
        if Cell.refsDepthOk #[st.regs.c5] then
          (.ok (), { st with stack := s, gas := st.gas.consume cellCreateGasPrice,
                             regs := { st.regs with c5 := OutAction.changeLib mode.toNat st.regs.c5 h.toNat } })
        else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice })
      else (.error .rangeChk, { st with stack := s }) := by
  have h1 : ¬ mode < 0 := by omega
  have h2 : ¬ mode.toNat > 31 := by omega
  have h2' : ¬ mode.toNat > 2 := by omega
  have h3 := and15_le_of_le (m := mode.toNat) (by omega)
  by_cases hh : 0 ≤ h ∧ h < 2 ^ 256
  · have h4 : ¬ (h < 0 ∨ h ≥ 2 ^ 256) := by omega
    rw [if_pos hh]
    by_cases hv : st.globalVersion ≥ 4
    · vm_simp [hs, hv, h1, h2, h2', h3, h4, VM.checkNewCellDepth, VmState.consumeGas, OutAction.changeLib]
    · vm_simp [hs, hv, h1, h2, h2', h4, VM.checkNewCellDepth, VmState.consumeGas, OutAction.changeLib]
  · have h4 : h < 0 ∨ h ≥ 2 ^ 256 := by omega
    rw [if_neg hh]
    by_cases hv : st.globalVersion ≥ 4
    · vm_simp [hs, hv, h1, h2, h2', h3, h4]
    · vm_simp [hs, hv, h1, h2, h2', h4]

set_option maxHeartbeats 1000000 in
/-- `CHANGELIB` from version 4, on the stack `s h mode` with a mode valid there. -/
@[vm_spec] theorem changeLib_v4 (st : VmState) (s : Stack) (h mode : Int) (hv : 4 ≤ st.globalVersion)
    (hm : 0 ≤ mode ∧ mode ≤ 31 ∧ ¬ (mode.toNat &&& 15) > 2)
    (hs : st.stack = (s.push (.int (.num h))).push (.int (.num mode))) :
    ExceptT.run (execInstr (.tonEnvOp .changeLib)) st =
      if 0 ≤ h ∧ h < 2 ^ 256 then
        if Cell.refsDepthOk #[st.regs.c5] then
          (.ok (), { st with stack := s, gas := st.gas.consume cellCreateGasPrice,
                             regs := { st.regs with c5 := OutAction.changeLib mode.toNat st.regs.c5 h.toNat } })
        else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice })
      else (.error .rangeChk, { st with stack := s }) := by
  have hv' : st.globalVersion ≥ 4 := hv
  have h1 : ¬ mode < 0 := by omega
  have h2 : ¬ mode.toNat > 31 := by omega
  have h3 := hm.2.2
  by_cases hh : 0 ≤ h ∧ h < 2 ^ 256
  · have h4 : ¬ (h < 0 ∨ h ≥ 2 ^ 256) := by omega
    rw [if_pos hh]
    vm_simp [hs, hv', h1, h2, h3, h4, VM.checkNewCellDepth, VmState.consumeGas, OutAction.changeLib]
  · have h4 : h < 0 ∨ h ≥ 2 ^ 256 := by omega
    rw [if_neg hh]
    vm_simp [hs, hv', h1, h2, h3, h4]

/-- The bits of a reserve action: at most 165, within a cell. -/
theorem reserveBits_size_le (f x : Nat) (b : Bool) (hl : (natLenBits x + 7) / 8 < 16) (hf : f < 256) :
    ¬ (natToBits 0x36e6b809 32 ++ natToBits f 8 ++
        (natToBits ((natLenBits x + 7) / 8) 4 ++ natToBits x ((natLenBits x + 7) / 8 * 8)) ++ #[b]).size > 1023 := by
  have _ := hf
  simp only [Array.size_append, natToBits_size, List.size_toArray, List.length_cons, List.length_nil]
  omega

set_option maxHeartbeats 2000000 in
/-- `RAWRESERVEX` (C++ `exec_reserve_raw`, mode 1) in any version, on the stack `s x y f` with the
mode `f` in `0..15` and no extra currencies (`y` null): the amount `x` must be non-negative
(range_chk), of fewer than 16 bytes (cell_ov); the action of `RAWRESERVE`, `OutAction.reserve f x c5`,
becomes `c5`. -/
@[vm_spec] theorem rawReserveX_null (st : VmState) (s : Stack) (x f : Int) (hf : 0 ≤ f ∧ f ≤ 15)
    (hs : st.stack = ((s.push (.int (.num x))).push .null).push (.int (.num f))) :
    ExceptT.run (execInstr (.tonEnvOp .rawReserveX)) st =
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
      have h5 := reserveBits_size_le f.toNat x.toNat (none : Option Cell).isSome hl (by omega)
      by_cases hv : st.globalVersion ≥ 4
      · vm_simp_flat [hs, hv, h1, h2, h2', h3, h4, h5, VM.popMaybeCell, VM.checkNewCellDepth]
        simp only [VmState.consumeGas]
        split <;> rfl
      · vm_simp_flat [hs, hv, h1, h2, h2', h3, h4, h5, VM.popMaybeCell, VM.checkNewCellDepth]
        simp only [VmState.consumeGas]
        split <;> rfl
    · rw [if_neg hl]
      have h4 : (natLenBits x.toNat + 7) / 8 ≥ 16 := by omega
      by_cases hv : st.globalVersion ≥ 4
      · vm_simp_flat [hs, hv, h1, h2, h2', h3, h4, VM.popMaybeCell]
      · vm_simp_flat [hs, hv, h1, h2, h2', h3, h4, VM.popMaybeCell]
  · rw [if_neg hx]
    have h3 : x < 0 := by omega
    by_cases hv : st.globalVersion ≥ 4
    · vm_simp_flat [hs, hv, h1, h2, h2', h3, VM.popMaybeCell]
    · vm_simp_flat [hs, hv, h1, h2, h2', h3, VM.popMaybeCell]

set_option maxHeartbeats 2000000 in
/-- `RAWRESERVEX` in any version, on the stack `s x y f` with the mode `f` in `0..15` and the
dictionary `y` of extra currencies (a cell): the action `OutAction.reserveExtra f x c5 y` becomes
`c5`. -/
@[vm_spec] theorem rawReserveX_cell (st : VmState) (s : Stack) (x f : Int) (y : Cell) (hf : 0 ≤ f ∧ f ≤ 15)
    (hs : st.stack = ((s.push (.int (.num x))).push (.cell y)).push (.int (.num f))) :
    ExceptT.run (execInstr (.tonEnvOp .rawReserveX)) st =
      if 0 ≤ x then
        if (natLenBits x.toNat + 7) / 8 < 16 then
          if Cell.refsDepthOk #[st.regs.c5, y] then
            (.ok (), { st with stack := s, gas := st.gas.consume cellCreateGasPrice,
                               regs := { st.regs with c5 := OutAction.reserveExtra f.toNat x.toNat st.regs.c5 y } })
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
      have h5 := reserveBits_size_le f.toNat x.toNat (some y).isSome hl (by omega)
      by_cases hv : st.globalVersion ≥ 4
      · vm_simp_flat [hs, hv, h1, h2, h2', h3, h4, h5, VM.popMaybeCell, VM.checkNewCellDepth]
        simp only [VmState.consumeGas]
        split <;> rfl
      · vm_simp_flat [hs, hv, h1, h2, h2', h3, h4, h5, VM.popMaybeCell, VM.checkNewCellDepth]
        simp only [VmState.consumeGas]
        split <;> rfl
    · rw [if_neg hl]
      have h4 : (natLenBits x.toNat + 7) / 8 ≥ 16 := by omega
      by_cases hv : st.globalVersion ≥ 4
      · vm_simp_flat [hs, hv, h1, h2, h2', h3, h4, VM.popMaybeCell]
      · vm_simp_flat [hs, hv, h1, h2, h2', h3, h4, VM.popMaybeCell]
  · rw [if_neg hx]
    have h3 : x < 0 := by omega
    by_cases hv : st.globalVersion ≥ 4
    · vm_simp_flat [hs, hv, h1, h2, h2', h3, VM.popMaybeCell]
    · vm_simp_flat [hs, hv, h1, h2, h2', h3, VM.popMaybeCell]

end Spec

end TvmLean

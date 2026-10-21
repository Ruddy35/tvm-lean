import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: cells, slices, builders

In the format of `Proofs/Exec/Spec/Stack.lean`. The cells loaded are ordinary (`c.special =
false`: a library cell would load its library's root, another exotic cell is cell_und); loading
one charges `VmState.registerCellLoad` (100 gas, 25 for a cell loaded before).
-/

namespace TvmLean

/-- An ordinary cell loads as itself: no library is followed (C++ `load_cell_slice_impl`). -/
@[vm_run] theorem VM.libraryResolveLoads_ordinary (libs : Array Cell) (gv : Nat) (c : Cell)
    (refused : Array BitString) (hc : c.special = false) :
    libraryResolveLoads libs gv c refused = (#[], .ok c) := by
  simp [libraryResolveLoads, libraryChainBound, libraryResolveLoadsAux, hc]

@[vm_run] theorem VM.libraryLoads_ordinary (st : VmState) (c : Cell) (hc : c.special = false) :
    st.libraryLoads c = #[] := by
  simp [VmState.libraryLoads, hc]

@[vm_run] theorem VM.registerCellLoads_cell (st : VmState) (c : Cell) :
    st.registerCellLoads [.cell c] = (st.registerCellLoad c, (st.registerCellLoad c).gasExhaustedNow) := by
  simp only [VmState.registerCellLoads]
  split <;> simp_all

@[vm_run] theorem VM.registerCellLoad_stack (st : VmState) (c : Cell) : (st.registerCellLoad c).stack = st.stack := by
  simp only [VmState.registerCellLoad]; split <;> rfl

namespace Spec

/-- `CTOS` (C++ `exec_cell_to_slice`): the load of the cell is charged (out of gas at once) and its
slice pushed. -/
@[vm_spec] theorem ctos (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) (hc : c.special = false) :
    ExceptT.run (execInstr .ctos) st =
      if ({ st with stack := s }.registerCellLoad c).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s }.registerCellLoad c)
      else
        (.ok (), { { st with stack := s }.registerCellLoad c with stack := s.push (.slice (Slice.ofCell c)) }) := by
  vm_simp [hs, hc]

/-- `LDU n` (C++ `exec_load_int_fixed`, mode 1, `1 ≤ n ≤ 256`): the first `n` bits of the
slice as an unsigned integer, then the rest of the slice; cell_und if the slice is shorter. -/
@[vm_spec] theorem ldu (st : VmState) (s : Stack) (sl : Slice) (n : Nat) (hn : 0 < n) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.ldu n)) st =
      if sl.haveBits n then
        (.ok (), { st with stack := (s.push (.int (.num (bitsToNat (sl.readBits n))))).push (.slice (sl.advanceBits n)) })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

/-- `LDREF` (C++ `exec_load_ref`): the first reference of the slice, then the rest; cell_und if
there is none. -/
@[vm_spec] theorem ldref (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .ldref) st =
      if sl.haveRefs 1 then
        (.ok (), { st with stack := ((s.push (.cell sl.cell.refs[sl.refPos]!)).push
                                      (.slice { sl with refPos := sl.refPos + 1 })) })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

/-- `ENDS` (C++ `exec_slice_chk_empty`): cell_und unless the slice is empty. -/
@[vm_spec] theorem ends (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .ends) st =
      if sl.bitsRemaining = 0 ∧ sl.refsRemaining = 0 then (.ok (), { st with stack := s })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

/-- `NEWC` (C++ `exec_new_builder`): an empty builder. -/
@[vm_spec] theorem newc (st : VmState) :
    ExceptT.run (execInstr .newc) st = (.ok (), { st with stack := st.stack.push (.builder Builder.empty) }) := by
  vm_simp

/-- `STU n` (C++ `exec_store_int`, unsigned, `1 ≤ n ≤ 256`): the integer below the builder is
stored in `n` bits; cell_ov if the builder has no room, range_chk if it does not fit. -/
@[vm_spec] theorem stu (st : VmState) (s : Stack) (x : Int) (b : Builder) (n : Nat) (hn : 0 < n)
    (hs : st.stack = (s.push (.int (.num x))).push (.builder b)) :
    ExceptT.run (execInstr (.stu n)) st =
      if b.canExtendBy n then
        if x < 0 ∨ x ≥ 2 ^ n then (.error .rangeChk, { st with stack := s })
        else (.ok (), { st with stack := s.push (.builder (b.storeBits (natToBits x.toNat n))) })
      else (.error .cellOv, { st with stack := s }) := by
  vm_simp [hs, intPow2]

/-- `STREF` (C++ `exec_store_ref`): the cell below the builder becomes its next reference; cell_ov
if it has four. -/
@[vm_spec] theorem stref (st : VmState) (s : Stack) (c : Cell) (b : Builder)
    (hs : st.stack = (s.push (.cell c)).push (.builder b)) :
    ExceptT.run (execInstr .stref) st =
      if b.canExtendBy 0 1 then (.ok (), { st with stack := s.push (.builder { b with refs := b.refs.push c }) })
      else (.error .cellOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `ENDC` (C++ `exec_builder_to_cell`): the cell's creation is charged and the cell pushed;
cell_ov if it would be too deep. -/
@[vm_spec] theorem endc (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr .endc) st =
      if Cell.refsDepthOk b.refs then
        (.ok (), { st with stack := s.push (.cell b.finalize), gas := st.gas.consume cellCreateGasPrice })
      else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice }) := by
  vm_simp [hs, VmState.consumeGas]

/-- `LDSLICEX` (C++ `exec_load_slice`, mode 0): the first `n` bits of the slice as a new slice,
then the rest; cell_und if the slice is shorter. -/
@[vm_spec] theorem ldslicex (st : VmState) (s : Stack) (sl : Slice) (n : Nat) (hn : n ≤ 1023)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num n))) :
    ExceptT.run (execInstr (.loadSliceX false false)) st =
      if sl.haveBits n then
        (.ok (), { st with stack := ((s.push (.slice (Slice.ofCell (Cell.mkOrdinary (sl.readBits n) #[])))).push
                                      (.slice (sl.advanceBits n))) })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

end Spec

end TvmLean

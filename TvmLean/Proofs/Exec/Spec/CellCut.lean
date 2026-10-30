import TvmLean.Proofs.Exec.Eval
import TvmLean.Proofs.Exec.Spec.Cell

/-!
# Specifications: slices cut by a bit count, prefixes, depths, `XCTOS`

In the format of `Proofs/Exec/Spec/Stack.lean`, on any slice or cell; a bit count from the stack
is an integer, range_chk outside `0..1023` (C++ `pop_smallint_range(1023)`, the count popped).

* `SDCUTFIRST`, `SDCUTLAST`, `SDSKIPLAST` (C++ `exec_slice_op_args`, cellops.cpp): the first
  `n` bits, the last `n` bits (no references), the slice without its last `n` bits; cell_und if
  the slice is shorter;
* `SDBEGINS`, `SDBEGINSQ` (the prefix a constant of the code) and `SDBEGINSX`, `SDBEGINSXQ` (the
  prefix a slice of the stack; C++ `exec_slice_begins_with_common`): the slice without the prefix
  (and -1 if quiet) if it begins with it; else cell_und, or (quiet) the slice back and 0;
* `SDEPTH` (C++ `exec_slice_depth`: the references left in the slice, `Slice.depth`), `CDEPTH` (C++
  `exec_cell_depth`; 0 for null);
* `XCTOS` (C++ `exec_cell_to_slice_maybe_special`): the cell's load charged (out of gas at once),
  its slice and whether it is exotic pushed.
-/

namespace TvmLean.Spec

/-- `SDCUTFIRST` (C++ `exec_slice_op_args`, cellops.cpp) on the stack `s sl n`: the first `n` bits
of the slice as a new slice without references; cell_und if the slice is shorter. -/
@[vm_spec] theorem sdcutfirst (st : VmState) (s : Stack) (sl : Slice) (n : Int)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num n))) :
    ExceptT.run (execInstr .sdcutfirst) st =
      if 0 ≤ n ∧ n ≤ 1023 then
        if sl.haveBits n.toNat then
          (.ok (), { st with stack := s.push (.slice (Slice.ofCell
            (Cell.mkOrdinary (sl.cell.bits.extract sl.bitPos (sl.bitPos + n.toNat)) #[]))) })
        else (.error .cellUnd, { st with stack := s })
      else (.error .rangeChk, { st with stack := s.push (.slice sl) }) := by
  by_cases hm : 0 ≤ n ∧ n ≤ 1023
  · have h1 : ¬ n < 0 := by omega
    have h2 : ¬ n.toNat > 1023 := by omega
    rw [if_pos hm]
    vm_simp [hs, h1, h2]
  · rw [if_neg hm]
    by_cases h1 : n < 0
    · vm_simp [hs, h1]
    · have h2 : n.toNat > 1023 := by omega
      vm_simp [hs, h1, h2]

/-- `SDCUTLAST` (C++ `exec_slice_op_args`) on the stack `s sl n`: the last `n` bits of the slice as
a new slice without references; cell_und if the slice is shorter. -/
@[vm_spec] theorem sdcutlast (st : VmState) (s : Stack) (sl : Slice) (n : Int)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num n))) :
    ExceptT.run (execInstr .sdcutlast) st =
      if 0 ≤ n ∧ n ≤ 1023 then
        if n.toNat ≤ sl.bitsRemaining then
          (.ok (), { st with stack := s.push (.slice (Slice.ofCell
            (Cell.mkOrdinary (sl.cell.bits.extract (sl.bitPos + (sl.bitsRemaining - n.toNat))
              (sl.bitPos + (sl.bitsRemaining - n.toNat) + n.toNat)) #[]))) })
        else (.error .cellUnd, { st with stack := s })
      else (.error .rangeChk, { st with stack := s.push (.slice sl) }) := by
  by_cases hm : 0 ≤ n ∧ n ≤ 1023
  · have h1 : ¬ n < 0 := by omega
    have h2 : ¬ n.toNat > 1023 := by omega
    rw [if_pos hm]
    vm_simp [hs, h1, h2]
  · rw [if_neg hm]
    by_cases h1 : n < 0
    · vm_simp [hs, h1]
    · have h2 : n.toNat > 1023 := by omega
      vm_simp [hs, h1, h2]

/-- `SDSKIPLAST` (C++ `exec_slice_op_args`) on the stack `s sl n`: the slice without its last `n`
bits (its references kept), as a new slice; cell_und if the slice is shorter. -/
@[vm_spec] theorem sdskiplast (st : VmState) (s : Stack) (sl : Slice) (n : Int)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num n))) :
    ExceptT.run (execInstr .sdskiplast) st =
      if 0 ≤ n ∧ n ≤ 1023 then
        if n.toNat ≤ sl.bitsRemaining then
          (.ok (), { st with stack := s.push (.slice (Slice.ofCell
            (Cell.mkOrdinary (sl.cell.bits.extract sl.bitPos (sl.bitPos + (sl.bitsRemaining - n.toNat)))
              (sl.cell.refs.extract sl.refPos sl.cell.refs.size)))) })
        else (.error .cellUnd, { st with stack := s })
      else (.error .rangeChk, { st with stack := s.push (.slice sl) }) := by
  by_cases hm : 0 ≤ n ∧ n ≤ 1023
  · have h1 : ¬ n < 0 := by omega
    have h2 : ¬ n.toNat > 1023 := by omega
    rw [if_pos hm]
    vm_simp [hs, h1, h2]
  · rw [if_neg hm]
    by_cases h1 : n < 0
    · vm_simp [hs, h1]
    · have h2 : n.toNat > 1023 := by omega
      vm_simp [hs, h1, h2]

/-- `SDBEGINS`, `SDBEGINSQ` (C++ `exec_slice_begins_with_const`) on the stack `s sl`, the prefix
`pref` a constant of the code: if the slice begins with the bits of `pref`, the rest (and -1 if
quiet); else cell_und, or (quiet) the slice back and 0. -/
@[vm_spec] theorem sdBeginsConst (st : VmState) (s : Stack) (sl pref : Slice) (quiet : Bool)
    (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.sdBeginsConst quiet pref)) st =
      if sl.haveBits (pref.readBits pref.bitsRemaining).size = true ∧
          sl.readBits (pref.readBits pref.bitsRemaining).size = pref.readBits pref.bitsRemaining then
        (.ok (), { st with
          stack := if quiet then (s.push (.slice (sl.advanceBits (pref.readBits pref.bitsRemaining).size))).push (.int (.num (-1)))
            else s.push (.slice (sl.advanceBits (pref.readBits pref.bitsRemaining).size)) })
      else if quiet then (.ok (), { st with stack := (s.push (.slice sl)).push (.int (.num 0)) })
      else (.error .cellUnd, { st with stack := s }) := by
  cases quiet <;> vm_simp [hs]

/-- `SDBEGINSX`, `SDBEGINSXQ` (C++ `exec_slice_begins_with`) on the stack `s sl pref`: as
`sdBeginsConst`, the prefix a slice of the stack. -/
@[vm_spec] theorem sdBeginsX (st : VmState) (s : Stack) (sl pref : Slice) (quiet : Bool)
    (hs : st.stack = (s.push (.slice sl)).push (.slice pref)) :
    ExceptT.run (execInstr (.sdBeginsX quiet)) st =
      if sl.haveBits (pref.readBits pref.bitsRemaining).size = true ∧
          sl.readBits (pref.readBits pref.bitsRemaining).size = pref.readBits pref.bitsRemaining then
        (.ok (), { st with
          stack := if quiet then (s.push (.slice (sl.advanceBits (pref.readBits pref.bitsRemaining).size))).push (.int (.num (-1)))
            else s.push (.slice (sl.advanceBits (pref.readBits pref.bitsRemaining).size)) })
      else if quiet then (.ok (), { st with stack := (s.push (.slice sl)).push (.int (.num 0)) })
      else (.error .cellUnd, { st with stack := s }) := by
  cases quiet <;> vm_simp [hs]

/-- `SDEPTH` (C++ `exec_slice_depth`, `CellSlice::get_depth`): one more than the deepest of the
references left in the slice, 0 if none (`Slice.depth`). -/
@[vm_spec] theorem sdepth (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cellOp .sdepth)) st =
      (.ok (), { st with stack := s.push (.int (.num (sl.depth : Nat))) }) := by
  vm_simp [hs]

/-- `CDEPTH` (C++ `exec_cell_depth`) of a cell: its depth. -/
@[vm_spec] theorem cdepth (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr .cdepth) st = (.ok (), { st with stack := s.push (.int (.num (c.depth : Nat))) }) := by
  vm_simp [hs]

/-- `CDEPTH` of null: 0. -/
@[vm_spec] theorem cdepth_null (st : VmState) (s : Stack) (hs : st.stack = s.push .null) :
    ExceptT.run (execInstr .cdepth) st = (.ok (), { st with stack := s.push (.int (.num 0)) }) := by
  vm_simp [hs]

/-- `XCTOS` (C++ `exec_cell_to_slice_maybe_special`): the load of the cell is charged (out of gas
at once), its slice and `-1` if it is exotic (0 else) pushed. -/
@[vm_spec] theorem xctos (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr .xctos) st =
      if ({ st with stack := s }.registerCellLoad c).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s }.registerCellLoad c)
      else
        (.ok (), { { st with stack := s }.registerCellLoad c with
          stack := (s.push (.slice (Slice.ofCell c))).push (.int (.num (if c.special then -1 else 0))) }) := by
  vm_simp [hs, VM.registerCellLoadSpecial]

end TvmLean.Spec

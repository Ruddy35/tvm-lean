import TvmLean.Proofs.Exec.Spec.Cell
import TvmLean.Proofs.Exec.Spec.Flow

/-!
# Specifications: the continuations of references

`CALLREF`, `JMPREF`, `IFREF`, `IFNOTREF`, `IFJMPREF`, `IFNOTJMPREF`, `IFREFELSE`, `IFELSEREF`,
`IFREFELSEREF` and `PUSHREFCONT` (C++ `exec_call_ref`, `exec_jmp_ref`, `exec_if_ref` and the like,
crypto/vm/contops.cpp, each `ref_to_cont(load_cell_slice_ref)`) on an ordinary cell, in the format
of `Proofs/Exec/Spec/Flow.lean`. The load of the cell is charged first (`VmState.registerCellLoad`,
out of gas at once, as `Spec.ctos`); then the code of the cell, a plain continuation (no saved
registers, no closure data), is called (the return continuation `VmState.retCont` becomes `c0`, as
`VM.run_call_plain`), jumped to, or pushed. A flag is an integer, true when nonzero (C++
`pop_bool`); the flag is popped before the load.
-/

namespace TvmLean.Spec

/-- `CALLREF` (C++ `exec_call_ref`): the load of the cell charged, its code called. -/
@[vm_spec] theorem callRef (st : VmState) (code : Slice) (hc : code.cell.special = false) :
    ExceptT.run (execInstr (.callRef code)) st =
      if (st.registerCellLoad code.cell).gasExhaustedNow then
        (.error .outOfGas, st.registerCellLoad code.cell)
      else
        (.ok (), { st.registerCellLoad code.cell with
          regs := { (st.registerCellLoad code.cell).regs with c0 := (st.registerCellLoad code.cell).retCont }
          cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty }) := by
  vm_simp [hc]

/-- `JMPREF` (C++ `exec_jmp_ref`): the load of the cell charged, its code jumped to. -/
@[vm_spec] theorem jmpRef (st : VmState) (code : Slice) (hc : code.cell.special = false) :
    ExceptT.run (execInstr (.jmpRef code)) st =
      if (st.registerCellLoad code.cell).gasExhaustedNow then
        (.error .outOfGas, st.registerCellLoad code.cell)
      else
        (.ok (), { st.registerCellLoad code.cell with
          cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty }) := by
  vm_simp [hc]

/-- `IFREF` (C++ `exec_if_ref`): if the flag is true, the load of the cell charged and its code
called. -/
@[vm_spec] theorem ifref (st : VmState) (s : Stack) (n : Int) (code : Slice) (hc : code.cell.special = false)
    (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.ifref code)) st =
      if n ≠ 0 then
        if ({ st with stack := s }.registerCellLoad code.cell).gasExhaustedNow then
          (.error .outOfGas, { st with stack := s }.registerCellLoad code.cell)
        else
          (.ok (), { { st with stack := s }.registerCellLoad code.cell with
            regs := { ({ st with stack := s }.registerCellLoad code.cell).regs with
              c0 := ({ st with stack := s }.registerCellLoad code.cell).retCont }
            cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty })
      else (.ok (), { st with stack := s }) := by
  by_cases h : n = 0 <;> vm_simp [hs, hc, h]

/-- `IFNOTREF` (C++ `exec_ifnot_ref`): if the flag is false, the load of the cell charged and its
code called. -/
@[vm_spec] theorem ifnotref (st : VmState) (s : Stack) (n : Int) (code : Slice) (hc : code.cell.special = false)
    (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.ifnotref code)) st =
      if n = 0 then
        if ({ st with stack := s }.registerCellLoad code.cell).gasExhaustedNow then
          (.error .outOfGas, { st with stack := s }.registerCellLoad code.cell)
        else
          (.ok (), { { st with stack := s }.registerCellLoad code.cell with
            regs := { ({ st with stack := s }.registerCellLoad code.cell).regs with
              c0 := ({ st with stack := s }.registerCellLoad code.cell).retCont }
            cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty })
      else (.ok (), { st with stack := s }) := by
  by_cases h : n = 0 <;> vm_simp [hs, hc, h]

/-- `IFJMPREF` (C++ `exec_if_jmp_ref`): if the flag is true, the load of the cell charged and its
code jumped to. -/
@[vm_spec] theorem ifjmpref (st : VmState) (s : Stack) (n : Int) (code : Slice) (hc : code.cell.special = false)
    (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.ifjmpref code)) st =
      if n ≠ 0 then
        if ({ st with stack := s }.registerCellLoad code.cell).gasExhaustedNow then
          (.error .outOfGas, { st with stack := s }.registerCellLoad code.cell)
        else
          (.ok (), { { st with stack := s }.registerCellLoad code.cell with
            cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty })
      else (.ok (), { st with stack := s }) := by
  by_cases h : n = 0 <;> vm_simp [hs, hc, h]

/-- `IFNOTJMPREF` (C++ `exec_ifnot_jmp_ref`): if the flag is false, the load of the cell charged and
its code jumped to. -/
@[vm_spec] theorem ifnotjmpref (st : VmState) (s : Stack) (n : Int) (code : Slice) (hc : code.cell.special = false)
    (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.ifnotjmpref code)) st =
      if n = 0 then
        if ({ st with stack := s }.registerCellLoad code.cell).gasExhaustedNow then
          (.error .outOfGas, { st with stack := s }.registerCellLoad code.cell)
        else
          (.ok (), { { st with stack := s }.registerCellLoad code.cell with
            cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty })
      else (.ok (), { st with stack := s }) := by
  by_cases h : n = 0 <;> vm_simp [hs, hc, h]

/-- `IFREFELSE` (C++ `exec_if_ref_else`) on the stack `s f k`: if the flag is true, the load of the
cell charged and its code called, else the plain continuation `k` called. -/
@[vm_spec] theorem ifrefElse (st : VmState) (s : Stack) (n : Int) (code k : Slice) (saved : Continuation)
    (hc : code.cell.special = false)
    (hs : st.stack = (s.push (.int (.num n))).push (.cont (.ordinary k saved OrdCregs.empty OrdCdata.empty))) :
    ExceptT.run (execInstr (.ifrefElse code)) st =
      if n ≠ 0 then
        if ({ st with stack := s }.registerCellLoad code.cell).gasExhaustedNow then
          (.error .outOfGas, { st with stack := s }.registerCellLoad code.cell)
        else
          (.ok (), { { st with stack := s }.registerCellLoad code.cell with
            regs := { ({ st with stack := s }.registerCellLoad code.cell).regs with
              c0 := ({ st with stack := s }.registerCellLoad code.cell).retCont }
            cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty })
      else
        (.ok (), { st with stack := s, regs := { st.regs with c0 := { st with stack := s }.retCont }
                           cc := .ordinary k saved OrdCregs.empty OrdCdata.empty }) := by
  by_cases h : n = 0 <;> vm_simp [hs, hc, h]

/-- `IFELSEREF` (C++ `exec_if_else_ref`) on the stack `s f k`: if the flag is true, the plain
continuation `k` called, else the load of the cell charged and its code called. -/
@[vm_spec] theorem ifelseRef (st : VmState) (s : Stack) (n : Int) (code k : Slice) (saved : Continuation)
    (hc : code.cell.special = false)
    (hs : st.stack = (s.push (.int (.num n))).push (.cont (.ordinary k saved OrdCregs.empty OrdCdata.empty))) :
    ExceptT.run (execInstr (.ifelseRef code)) st =
      if n ≠ 0 then
        (.ok (), { st with stack := s, regs := { st.regs with c0 := { st with stack := s }.retCont }
                           cc := .ordinary k saved OrdCregs.empty OrdCdata.empty })
      else
        if ({ st with stack := s }.registerCellLoad code.cell).gasExhaustedNow then
          (.error .outOfGas, { st with stack := s }.registerCellLoad code.cell)
        else
          (.ok (), { { st with stack := s }.registerCellLoad code.cell with
            regs := { ({ st with stack := s }.registerCellLoad code.cell).regs with
              c0 := ({ st with stack := s }.registerCellLoad code.cell).retCont }
            cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty }) := by
  by_cases h : n = 0 <;> vm_simp [hs, hc, h]

/-- `IFREFELSEREF` (C++ `exec_if_ref_else_ref`): the load of the first cell charged and its code
called if the flag is true, else the second's. -/
@[vm_spec] theorem ifrefElseRef (st : VmState) (s : Stack) (n : Int) (t f : Slice)
    (ht : t.cell.special = false) (hf : f.cell.special = false)
    (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.ifrefElseRef t f)) st =
      let c := if n ≠ 0 then t.cell else f.cell
      if ({ st with stack := s }.registerCellLoad c).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s }.registerCellLoad c)
      else
        (.ok (), { { st with stack := s }.registerCellLoad c with
          regs := { ({ st with stack := s }.registerCellLoad c).regs with
            c0 := ({ st with stack := s }.registerCellLoad c).retCont }
          cc := .ordinary (Slice.ofCell c) (.quit 0) OrdCregs.empty OrdCdata.empty }) := by
  by_cases h : n = 0 <;> vm_simp [hs, ht, hf, h]

/-- `PUSHREFCONT` (C++ `exec_push_ref_cont`... `exec_push_ref` mode 2): the load of the cell
charged, its code pushed as a plain continuation. -/
@[vm_spec] theorem pushRefCont (st : VmState) (c : Cell) (hc : c.special = false) :
    ExceptT.run (execInstr (.pushRefCont c)) st =
      if (st.registerCellLoad c).gasExhaustedNow then
        (.error .outOfGas, st.registerCellLoad c)
      else
        (.ok (), { st.registerCellLoad c with
          stack := st.stack.push (.cont (.ordinary (Slice.ofCell c) (.quit 0) OrdCregs.empty OrdCdata.empty)) }) := by
  vm_simp [hc]

end TvmLean.Spec

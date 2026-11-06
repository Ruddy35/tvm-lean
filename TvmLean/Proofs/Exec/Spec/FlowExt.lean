import TvmLean.Proofs.Exec.Spec.Cell
import TvmLean.Proofs.Basic

/-!
# Specifications: code pages, jumps on a bit of an integer, `TRY`

In the format of `Proofs/Exec/Spec/Stack.lean`. A jump is the run of `VM.jump` of the continuation
(its lemmas, `VM.run_jump_ordinary`, ..., `Proofs/Exec/VM.lean`, take it from there).

* `SETCP n` for `n ≠ 0` (C++ `exec_set_cp`, contops.cpp:1252, `force_cp`): inv_opcode (only the code
  page 0 exists); `SETCPX` (C++ `exec_set_cp_any`, contops.cpp:1258) on the stack `s n`: `SETCP n`
  (range_chk outside `-2^15..2^15-1`);
* `IFBITJMP i`, `IFNBITJMP i` (C++ `exec_if_bit_jmp`, contops.cpp:441) on the stack `s x c`: the
  integer `x` left, a jump to `c` if its bit `i` is set (clear) (the model's `intBit`);
  `IFBITJMPREF i`, `IFNBITJMPREF i` (C++ `exec_if_bit_jmpref`, contops.cpp:463) the same to the code
  of a reference (an ordinary cell, its load charged);
* `TRY` (C++ `exec_try`, contops.cpp:1201) on the stack `s c h` with an ordinary current continuation:
  the rest of the code as `c0` with `c0`, `c1`, `c2` saved, `c1 := quit 1`, the handler `h` with
  `c2` and that `c0` saved as `c2`, and the body `c` run.
-/

namespace TvmLean.Spec

/-- `SETCP n` (C++ `exec_set_cp`) for `n ≠ 0`: inv_opcode, the state unchanged. -/
@[vm_spec] theorem setcp_ne (st : VmState) (n : Int) (hn : n ≠ 0) :
    ExceptT.run (execInstr (.setcp n)) st = (.error .invOpcode, st) := by
  vm_simp [hn]

/-- `SETCPX` (C++ `exec_set_cp_any`) on the stack `s n`: the code page 0 if `n = 0`; inv_opcode
for another in `-2^15..2^15-1`, range_chk outside. -/
@[vm_spec] theorem setcpX (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .setcpX) st =
      if -0x8000 ≤ n ∧ n ≤ 0x7fff then
        if n = 0 then (.ok (), { st with stack := s, cp := 0 })
        else (.error .invOpcode, { st with stack := s })
      else (.error .rangeChk, { st with stack := s }) := by
  by_cases hr : -0x8000 ≤ n ∧ n ≤ 0x7fff
  · by_cases h0 : n = 0
    · subst h0; vm_simp [hs]
    · vm_simp [hs, hr, h0]
  · vm_simp [hs, hr]

/-- `IFBITJMP i` (C++ `exec_if_bit_jmp`) on the stack `s x c`: `x` left, and a jump to `c` if the
bit `i` of `x` is set. -/
@[vm_spec] theorem ifbitjmp (st : VmState) (s : Stack) (x : Int) (c : Continuation) (i : Nat)
    (hs : st.stack = (s.push (.int (.num x))).push (.cont c)) :
    ExceptT.run (execInstr (.contExt (.ifbitjmp i))) st =
      if (private% TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.intBit) x i then
        ExceptT.run (VM.jump c) { st with stack := s.push (.int (.num x)) }
      else (.ok (), { st with stack := s.push (.int (.num x)) }) := by
  cases h : (private% TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.intBit) x i <;>
    vm_simp [hs, h]

/-- `IFNBITJMP i` (C++ `exec_if_bit_jmp`) on the stack `s x c`: `x` left, and a jump to `c` if the
bit `i` of `x` is clear. -/
@[vm_spec] theorem ifnbitjmp (st : VmState) (s : Stack) (x : Int) (c : Continuation) (i : Nat)
    (hs : st.stack = (s.push (.int (.num x))).push (.cont c)) :
    ExceptT.run (execInstr (.contExt (.ifnbitjmp i))) st =
      if (private% TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.intBit) x i then
        (.ok (), { st with stack := s.push (.int (.num x)) })
      else ExceptT.run (VM.jump c) { st with stack := s.push (.int (.num x)) } := by
  cases h : (private% TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.intBit) x i <;>
    vm_simp [hs, h]

/-- `IFBITJMPREF i` (C++ `exec_if_bit_jmpref`) on the stack `s x`, the reference an ordinary cell:
`x` left, and if its bit `i` is set, the load of the cell charged (out of gas at once) and its code
jumped to. -/
@[vm_spec] theorem ifbitjmpref (st : VmState) (s : Stack) (x : Int) (i : Nat) (code : Slice)
    (hc : code.cell.special = false) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.contExt (.ifbitjmpref i code))) st =
      if (private% TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.intBit) x i then
        if ({ st with stack := s.push (.int (.num x)) }.registerCellLoad code.cell).gasExhaustedNow then
          (.error .outOfGas, { st with stack := s.push (.int (.num x)) }.registerCellLoad code.cell)
        else
          (.ok (), { { st with stack := s.push (.int (.num x)) }.registerCellLoad code.cell with
            cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty })
      else (.ok (), { st with stack := s.push (.int (.num x)) }) := by
  cases h : (private% TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.intBit) x i <;> vm_simp [hs, hc, h]

/-- `IFNBITJMPREF i` (C++ `exec_if_bit_jmpref`) on the stack `s x`: as `IFBITJMPREF i` if the bit is
clear. -/
@[vm_spec] theorem ifnbitjmpref (st : VmState) (s : Stack) (x : Int) (i : Nat) (code : Slice)
    (hc : code.cell.special = false) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.contExt (.ifnbitjmpref i code))) st =
      if (private% TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.intBit) x i then
        (.ok (), { st with stack := s.push (.int (.num x)) })
      else if ({ st with stack := s.push (.int (.num x)) }.registerCellLoad code.cell).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s.push (.int (.num x)) }.registerCellLoad code.cell)
      else
        (.ok (), { { st with stack := s.push (.int (.num x)) }.registerCellLoad code.cell with
          cc := .ordinary (Slice.ofCell code.cell) (.quit 0) OrdCregs.empty OrdCdata.empty }) := by
  cases h : (private% TvmLean.Semantics.Exec.Flow.IfBitJmp TvmLean.intBit) x i <;> vm_simp [hs, hc, h]

/-- `TRY` (C++ `exec_try`, contops.cpp:1201) on the stack `s c h`, the current continuation ordinary
with the code `code`: `c0` the rest of the code with `c0`, `c1`, `c2` saved (`extract_cc(7)`), `c1`
`quit 1`, `c2` the handler `h` with the old `c2` and that `c0` (`force_cregs`, `define_c2`,
`define_c0`), and the body `c` the current continuation (its saved registers and closure data
taken when it is entered, as after a jump). -/
@[vm_spec] theorem try_ (st : VmState) (s : Stack) (c h : Continuation) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata)
    (hs : st.stack = (s.push (.cont c)).push (.cont h)) (hcc : st.cc = .ordinary code saved cregs cdata) :
    ExceptT.run (execInstr .try_) st =
      (.ok (), { st with
        stack := s
        regs := { st.regs with
          c0 := .ordinary code (.quit 0)
            { OrdCregs.empty with c0 := some st.regs.c0, c1 := some st.regs.c1, c2 := some st.regs.c2 }
            OrdCdata.empty
          c1 := .quit 1
          c2 := (h.defineC2 st.regs.c2).defineC0 (.ordinary code (.quit 0)
            { OrdCregs.empty with c0 := some st.regs.c0, c1 := some st.regs.c1, c2 := some st.regs.c2 }
            OrdCdata.empty) }
        cc := c }) := by
  vm_simp [hs, hcc]

end TvmLean.Spec

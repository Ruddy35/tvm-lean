import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: control flow and exceptions

In the format of `Proofs/Exec/Spec/Stack.lean`. A flag is an integer, true when nonzero (C++
`pop_bool`). The continuations are the plain ones code pushes (`PUSHCONT`: an ordinary
continuation without saved registers or closure data); `IFJMP` and `RET` jump to any ordinary
continuation without closure data (the jumps of the model leave none).

An exception raised by an instruction (`THROWIF` and the like) is the run of `VM.throwToHandler`
(`VM.run_throwToHandler`): the stack `[0, n]`, `c2` the current continuation, the exception gas
charged.
-/

namespace TvmLean.Spec

/-- `PUSHCONT` (C++ `exec_push_cont`, `exec_push_cont_simple`): the code becomes a plain
continuation on the stack. -/
@[vm_spec] theorem pushCont (st : VmState) (code : Slice) :
    ExceptT.run (execInstr (.pushCont code)) st =
      (.ok (), { st with stack := st.stack.push (.cont (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)) }) := by
  vm_simp

/-- `PUSHREF` (C++ `exec_push_ref`, mode 0): the cell is pushed. -/
@[vm_spec] theorem pushRef (st : VmState) (c : Cell) :
    ExceptT.run (execInstr (.pushRef c)) st = (.ok (), { st with stack := st.stack.push (.cell c) }) := by
  vm_simp

/-- `IF` (C++ `exec_if`): if the flag is true the continuation is called (`VM.call`). -/
@[vm_spec] theorem if_ (st : VmState) (s : Stack) (n : Int) (code : Slice) (saved : Continuation)
    (hs : st.stack = (s.push (.int (.num n))).push (.cont (.ordinary code saved OrdCregs.empty OrdCdata.empty))) :
    ExceptT.run (execInstr .if_) st =
      if n ≠ 0 then
        (.ok (), { st with stack := s, regs := { st.regs with c0 := { st with stack := s }.retCont }
                           cc := .ordinary code saved OrdCregs.empty OrdCdata.empty })
      else (.ok (), { st with stack := s }) := by
  vm_simp [hs]

/-- `IFNOT` (C++ `exec_ifnot`): if the flag is false the continuation is called. -/
@[vm_spec] theorem ifnot (st : VmState) (s : Stack) (n : Int) (code : Slice) (saved : Continuation)
    (hs : st.stack = (s.push (.int (.num n))).push (.cont (.ordinary code saved OrdCregs.empty OrdCdata.empty))) :
    ExceptT.run (execInstr .ifnot) st =
      if n = 0 then
        (.ok (), { st with stack := s, regs := { st.regs with c0 := { st with stack := s }.retCont }
                           cc := .ordinary code saved OrdCregs.empty OrdCdata.empty })
      else (.ok (), { st with stack := s }) := by
  vm_simp [hs]

/-- `IFJMP` (C++ `exec_if_jmp`): if the flag is true the VM jumps to the continuation. -/
@[vm_spec] theorem ifjmp (st : VmState) (s : Stack) (n : Int) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (hs : st.stack = (s.push (.int (.num n))).push (.cont (.ordinary code saved cregs OrdCdata.empty))) :
    ExceptT.run (execInstr .ifjmp) st =
      if n ≠ 0 then (.ok (), { st with stack := s, cc := .ordinary code saved cregs OrdCdata.empty })
      else (.ok (), { st with stack := s }) := by
  vm_simp [hs]

/-- `IFNOTJMP` (C++ `exec_ifnot_jmp`): if the flag is false the VM jumps to the continuation. -/
@[vm_spec] theorem ifnotjmp (st : VmState) (s : Stack) (n : Int) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (hs : st.stack = (s.push (.int (.num n))).push (.cont (.ordinary code saved cregs OrdCdata.empty))) :
    ExceptT.run (execInstr .ifnotjmp) st =
      if n = 0 then (.ok (), { st with stack := s, cc := .ordinary code saved cregs OrdCdata.empty })
      else (.ok (), { st with stack := s }) := by
  vm_simp [hs]

/-- `RET` (C++ `exec_ret`) when `c0` is an ordinary continuation without closure data: `c0`
becomes `quit 0` and the current continuation. -/
@[vm_spec] theorem ret (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (hc0 : st.regs.c0 = .ordinary code saved cregs OrdCdata.empty) :
    ExceptT.run (execInstr .ret) st =
      (.ok (), { st with regs := { st.regs with c0 := .quit 0 }, cc := .ordinary code saved cregs OrdCdata.empty }) := by
  vm_simp [hc0]

/-- `RET` (C++ `exec_ret`) when `c0` is `quit n`: the VM goes to `quit n` (it halts at the next
step with exit code `~n`). -/
@[vm_spec] theorem ret_quit (st : VmState) (n : Int) (hc0 : st.regs.c0 = .quit n) :
    ExceptT.run (execInstr .ret) st =
      (.ok (), { st with regs := { st.regs with c0 := .quit 0 }, cc := .quit n }) := by
  vm_simp [hc0]

/-- `IFRET` (C++ `exec_ifret`) when `c0` is an ordinary continuation without closure data: if the
flag is true the VM returns. -/
@[vm_spec] theorem ifret (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n)))
    (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (hc0 : st.regs.c0 = .ordinary code saved cregs OrdCdata.empty) :
    ExceptT.run (execInstr .ifret) st =
      if n ≠ 0 then
        (.ok (), { st with stack := s, regs := { st.regs with c0 := .quit 0 }
                           cc := .ordinary code saved cregs OrdCdata.empty })
      else (.ok (), { st with stack := s }) := by
  vm_simp [hs, hc0]

/-- `THROW n` (C++ `exec_throw_fixed`): the exception `n` is raised. -/
@[vm_spec] theorem throw (st : VmState) (e : Int) :
    ExceptT.run (execInstr (.throw e)) st = ExceptT.run (VM.throwToHandler fun st => st.throwException e) st := by
  vm_simp

/-- `THROWIF n` (C++ `exec_throw_fixed`, mode 1): if the flag is true the exception `n` is
raised. -/
@[vm_spec] theorem throwIf (st : VmState) (s : Stack) (x e : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.throwIf e)) st =
      if x ≠ 0 then ExceptT.run (VM.throwToHandler fun st => st.throwException e) { st with stack := s }
      else (.ok (), { st with stack := s }) := by
  vm_simp [hs]

/-- `THROWIFNOT n` (C++ `exec_throw_fixed`, mode 2): if the flag is false the exception `n` is
raised. -/
@[vm_spec] theorem throwIfNot (st : VmState) (s : Stack) (x e : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.throwIfNot e)) st =
      if x ≠ 0 then (.ok (), { st with stack := s })
      else ExceptT.run (VM.throwToHandler fun st => st.throwException e) { st with stack := s } := by
  vm_simp [hs]

/-- `EXECUTE` = `CALLX` (C++ `exec_execute`): the continuation (plain: no saved registers, no
closure data) is called, the return continuation becoming `c0`. -/
@[vm_spec] theorem execute (st : VmState) (s : Stack) (code : Slice) (saved : Continuation)
    (hs : st.stack = s.push (.cont (.ordinary code saved OrdCregs.empty OrdCdata.empty))) :
    ExceptT.run (execInstr .execute) st =
      (.ok (), { st with stack := s, regs := { st.regs with c0 := { st with stack := s }.retCont }
                         cc := .ordinary code saved OrdCregs.empty OrdCdata.empty }) := by
  vm_simp [hs]

/-- `JMPX` (C++ `exec_jmpx`): the VM jumps to the continuation (no closure data; its saved
registers are restored when it is entered). -/
@[vm_spec] theorem jmpx (st : VmState) (s : Stack) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (hs : st.stack = s.push (.cont (.ordinary code saved cregs OrdCdata.empty))) :
    ExceptT.run (execInstr .jmpx) st = (.ok (), { st with stack := s, cc := .ordinary code saved cregs OrdCdata.empty }) := by
  vm_simp [hs]

/-- `IFELSE` (C++ `exec_if_else`) on the stack `s f k₁ k₀`: `k₁` is called if the flag is true,
else `k₀` (`VmState.callTo`). -/
@[vm_spec] theorem ifelse (st : VmState) (s : Stack) (n : Int) (k1 k0 : Continuation)
    (hs : st.stack = ((s.push (.int (.num n))).push (.cont k1)).push (.cont k0)) :
    ExceptT.run (execInstr .ifelse) st =
      if n ≠ 0 then (.ok (), { st with stack := s }.callTo k1) else (.ok (), { st with stack := s }.callTo k0) := by
  by_cases h : n = 0 <;> vm_simp [hs, h]

/-- `THROWANY` (C++ `exec_throw_any`, no parameter, unconditional) on the stack `s n`: the
exception `n` (in `0..65535`, range_chk else) is raised. -/
@[vm_spec] theorem throwAny (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.throwAny false false true)) st =
      if 0 ≤ n ∧ n ≤ 0xffff then ExceptT.run (VM.throwToHandler fun st => st.throwException n) { st with stack := s }
      else (.error .rangeChk, { st with stack := s }) := by
  by_cases hn : 0 ≤ n ∧ n ≤ 0xffff
  · rw [if_pos hn]
    have h1 : ¬ n < 0 := by omega
    have h2 : ¬ n.toNat > 0xffff := by omega
    have h3 : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg hn.1
    vm_simp [hs, h1, h2, h3]
  · rw [if_neg hn]
    by_cases h1 : n < 0
    · vm_simp [hs, h1]
    · have h2 : n.toNat > 0xffff := by omega
      vm_simp [hs, h1, h2]

end TvmLean.Spec

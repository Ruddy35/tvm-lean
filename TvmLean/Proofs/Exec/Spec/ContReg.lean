import TvmLean.Proofs.Exec.Spec.LoopBrk

/-!
# Specifications: the return and alternative continuations changed, the registers by an index on
the stack

In the format of `Proofs/Exec/Spec/Stack.lean` (C++ contops.cpp):

* `ATEXIT`, `ATEXITALT` (C++ `exec_atexit`, `exec_atexit_alt`) on the stack `s c`: `c` saving `c0`
  (`c1`) becomes `c0` (`c1`); `SETEXITALT` (C++ `exec_setexit_alt`): `c` saving `c0` and `c1`
  becomes `c1`;
* `THENRET`, `THENRETALT` (C++ `exec_thenret`, `exec_thenret_alt`): `c` saving `c0` (`c1` as its
  `c0`) pushed;
* `INVERT` (C++ `exec_invert`): `c0` and `c1` swapped; `SAMEALT` (C++ `exec_samealt`): `c1` is `c0`;
* `BOOLEVAL` (C++ `exec_booleval`) on the stack `s k` while running `code`: the rest of the code
  saving `c0` and `c1` (`extract_cc(3)`) after pushing -1 is `c0`, after pushing 0 is `c1`, then the
  jump to `k`;
* `PUSHCTRX`, `POPCTRX`, `SETCONTCTRX` (C++ `exec_push_ctr_var`, `exec_pop_ctr_var`,
  `exec_setcont_ctr_var`): the index on top in `0..16` (range_chk; for `POPCTRX`, `SETCONTCTRX` not
  6 nor above 7), then the register read (`VmState.getCtr`), set (`VmState.setCtr`) or defined in
  the continuation (`Continuation.defineCtr`, silent on a register it saves from version 14).
-/

namespace TvmLean

/-- The registers read do not depend on the stack. -/
theorem VmState.getCtr_stack (st : VmState) (s : Stack) (n : Nat) :
    ({ st with stack := s } : VmState).getCtr n = st.getCtr n := rfl

namespace Spec

/-- `ATEXIT` on the stack `s c`. -/
@[vm_spec] theorem atexit (st : VmState) (s : Stack) (c : Continuation) (hs : st.stack = s.push (.cont c)) :
    ExceptT.run (execInstr (.contExt .atexit)) st =
      (.ok (), { st with stack := s, regs := { st.regs with c0 := c.defineC0 st.regs.c0 } }) := by
  vm_simp [hs]

/-- `ATEXITALT` on the stack `s c`. -/
@[vm_spec] theorem atexitAlt (st : VmState) (s : Stack) (c : Continuation) (hs : st.stack = s.push (.cont c)) :
    ExceptT.run (execInstr (.contExt .atexitAlt)) st =
      (.ok (), { st with stack := s, regs := { st.regs with c1 := c.defineC1 st.regs.c1 } }) := by
  vm_simp [hs]

/-- `SETEXITALT` on the stack `s c`. -/
@[vm_spec] theorem setExitAlt (st : VmState) (s : Stack) (c : Continuation) (hs : st.stack = s.push (.cont c)) :
    ExceptT.run (execInstr (.contExt .setExitAlt)) st =
      (.ok (), { st with stack := s, regs := { st.regs with c1 := (c.defineC0 st.regs.c0).defineC1 st.regs.c1 } }) := by
  vm_simp [hs]

/-- `THENRET` on the stack `s c`. -/
@[vm_spec] theorem thenret (st : VmState) (s : Stack) (c : Continuation) (hs : st.stack = s.push (.cont c)) :
    ExceptT.run (execInstr (.contExt .thenret)) st =
      (.ok (), { st with stack := s.push (.cont (c.defineC0 st.regs.c0)) }) := by
  vm_simp [hs]

/-- `THENRETALT` on the stack `s c`. -/
@[vm_spec] theorem thenretAlt (st : VmState) (s : Stack) (c : Continuation) (hs : st.stack = s.push (.cont c)) :
    ExceptT.run (execInstr (.contExt .thenretAlt)) st =
      (.ok (), { st with stack := s.push (.cont (c.defineC0 st.regs.c1)) }) := by
  vm_simp [hs]

/-- `INVERT`. -/
@[vm_spec] theorem invert (st : VmState) :
    ExceptT.run (execInstr (.contExt .invert)) st =
      (.ok (), { st with regs := { st.regs with c0 := st.regs.c1, c1 := st.regs.c0 } }) := by
  vm_simp

/-- `SAMEALT`. -/
@[vm_spec] theorem sameAlt (st : VmState) :
    ExceptT.run (execInstr .sameAlt) st = (.ok (), { st with regs := { st.regs with c1 := st.regs.c0 } }) := by
  vm_simp

set_option maxHeartbeats 4000000 in
/-- `BOOLEVAL` on the stack `s k` while running `code`. -/
@[vm_spec] theorem booleval (st : VmState) (s : Stack) (k : Continuation) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr (.contExt .booleval)) st =
      ExceptT.run (VM.jump k) { st with
        stack := s,
        regs := { st.regs with
          c0 := .pushInt (-1) (.ordinary code (.quit 0)
            { OrdCregs.empty with c0 := some st.regs.c0, c1 := some st.regs.c1 } OrdCdata.empty),
          c1 := .pushInt 0 (.ordinary code (.quit 0)
            { OrdCregs.empty with c0 := some st.regs.c0, c1 := some st.regs.c1 } OrdCdata.empty) } } := by
  vm_simp [hs, hcc]

/-- `PUSHCTRX` on the stack `s i`. -/
@[vm_spec] theorem pushCtrX (st : VmState) (s : Stack) (i : Int) (hs : st.stack = s.push (.int (.num i))) :
    ExceptT.run (execInstr (.contExt .pushCtrX)) st =
      if i < 0 then (.error .rangeChk, { st with stack := s })
      else if 16 < i.toNat then (.error .rangeChk, { st with stack := s })
      else match st.getCtr i.toNat with
        | .ok v => (.ok (), { st with stack := s.push v })
        | .error e => (.error e, { st with stack := s }) := by
  by_cases h1 : i < 0
  · vm_simp [hs, h1]
  · by_cases h2 : 16 < i.toNat
    · vm_simp [hs, h1, h2]
    · cases h : st.getCtr i.toNat <;> vm_simp [hs, h1, h2, VmState.getCtr_stack, h]

/-- `POPCTRX` on the stack `s v i`. -/
@[vm_spec] theorem popCtrX (st : VmState) (s : Stack) (v : Value) (i : Int)
    (hs : st.stack = (s.push v).push (.int (.num i))) :
    ExceptT.run (execInstr (.contExt .popCtrX)) st =
      if i < 0 then (.error .rangeChk, { st with stack := s.push v })
      else if 16 < i.toNat then (.error .rangeChk, { st with stack := s.push v })
      else if i.toNat = 6 ∨ 7 < i.toNat then (.error .rangeChk, { st with stack := s.push v })
      else match ({ st with stack := s } : VmState).setCtr i.toNat v with
        | .ok st' => (.ok (), st')
        | .error e => (.error e, { st with stack := s }) := by
  by_cases h1 : i < 0
  · vm_simp [hs, h1]
  · by_cases h2 : 16 < i.toNat
    · vm_simp [hs, h1, h2]
    · by_cases h3 : i.toNat = 6 ∨ 7 < i.toNat
      · vm_simp [hs, h1, h2, h3]
      · cases h : ({ st with stack := s } : VmState).setCtr i.toNat v <;> vm_simp [hs, h1, h2, h3, h]

/-- `SETCONTCTRX` on the stack `s v k i`. -/
@[vm_spec] theorem setContCtrX (st : VmState) (s : Stack) (v : Value) (k : Continuation) (i : Int)
    (hs : st.stack = ((s.push v).push (.cont k)).push (.int (.num i))) :
    ExceptT.run (execInstr (.contExt .setContCtrX)) st =
      if i < 0 then (.error .rangeChk, { st with stack := (s.push v).push (.cont k) })
      else if 16 < i.toNat then (.error .rangeChk, { st with stack := (s.push v).push (.cont k) })
      else if i.toNat = 6 ∨ 7 < i.toNat then (.error .rangeChk, { st with stack := (s.push v).push (.cont k) })
      else match k.defineCtr i.toNat v (decide (14 ≤ st.globalVersion)) with
        | .ok k' => (.ok (), { st with stack := s.push (.cont k') })
        | .error e => (.error e, { st with stack := s }) := by
  by_cases h1 : i < 0
  · vm_simp [hs, h1]
  · by_cases h2 : 16 < i.toNat
    · vm_simp [hs, h1, h2]
    · by_cases h3 : i.toNat = 6 ∨ 7 < i.toNat
      · vm_simp [hs, h1, h2, h3]
      · cases h : k.defineCtr i.toNat v (decide (14 ≤ st.globalVersion)) <;>
          vm_simp [hs, h1, h2, h3, h]

end Spec

end TvmLean

import TvmLean.Proofs.Exec.Spec.LoopBrk

/-!
# Specifications: `REPEATEND` and the loops with `BRK`

In the format of `Proofs/Exec/Spec/Loop.lean`, while running the code `code`:

* `REPEATEND` (C++ `exec_repeat_end`, contops.cpp) on the stack `s n`: `n` a 32-bit signed integer
  (range_chk else); a return (`VM.ret`) if `n ≤ 0`, else the rest of the code (`loopRest`) `n`
  times, then `c0`;
* `REPEATBRK`, `REPEATENDBRK`, `UNTILBRK`, `UNTILENDBRK`, `WHILEBRK`, `WHILEENDBRK` (C++ the same
  functions with `brk`): as `REPEAT`, `REPEATEND`, `UNTIL`, `UNTILEND`, `WHILE`, `WHILEEND`, the
  continuation after the loop also made `c1` saving the current `c1` and `c0` (`c1_envelope_if`,
  `VmState.c1Envelope`), so that `RETALT` in the loop leaves it;
* `AGAINENDBRK` (C++ `exec_again_end` with `brk`): `c0` saving `c1` made both `c0` and `c1`
  (`c1_save_set`, `VmState.c1SaveSet`), then the rest of the code forever.
-/

namespace TvmLean.Spec

/-- The continuation after a loop with `BRK` (`VmState.c1Envelope` of `after` in the registers
`c0`, `c1`): `after` saving `c1` and `c0`. -/
abbrev brkAfter (after c0 c1 : Continuation) : Continuation := (after.defineC1 c1).defineC0 c0

/-- `REPEATEND` on the stack `s n`. -/
@[vm_spec] theorem repeatEnd (st : VmState) (s : Stack) (n : Int) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.contExt (.repeatEnd false))) st =
      if n < -0x80000000 ∨ n > 0x7fffffff then (.error .rangeChk, { st with stack := s })
      else if n ≤ 0 then ExceptT.run VM.ret { st with stack := s }
      else (.ok (), { st with stack := s, cc := .repeatBody (loopRest code) st.regs.c0 n.toNat }) := by
  vm_simp [hs, hcc, popSmallintRepeatCount]

/-- `REPEATBRK` on the stack `s n body`. -/
@[vm_spec] theorem repeatBrk (st : VmState) (s : Stack) (n : Int) (body : Continuation) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = (s.push (.int (.num n))).push (.cont body)) :
    ExceptT.run (execInstr (.contExt (.repeat true))) st =
      if n < -0x80000000 ∨ n > 0x7fffffff then (.error .rangeChk, { st with stack := s })
      else if n ≤ 0 then (.ok (), { st with stack := s })
      else (.ok (), { st with
        stack := s, cc := .repeatBody body (brkAfter (loopAfter code st.regs.c0) (.quit 0) st.regs.c1) n.toNat,
        regs := { st.regs with c0 := .quit 0, c1 := brkAfter (loopAfter code st.regs.c0) (.quit 0) st.regs.c1 } }) := by
  vm_simp [hs, hcc, popSmallintRepeatCount, VmState.c1Envelope]

/-- `REPEATENDBRK` on the stack `s n`. -/
@[vm_spec] theorem repeatEndBrk (st : VmState) (s : Stack) (n : Int) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.contExt (.repeatEnd true))) st =
      if n < -0x80000000 ∨ n > 0x7fffffff then (.error .rangeChk, { st with stack := s })
      else if n ≤ 0 then ExceptT.run VM.ret { st with stack := s }
      else (.ok (), { st with
        stack := s, cc := .repeatBody (loopRest code) (brkAfter st.regs.c0 st.regs.c0 st.regs.c1) n.toNat,
        regs := { st.regs with c1 := brkAfter st.regs.c0 st.regs.c0 st.regs.c1 } }) := by
  vm_simp [hs, hcc, popSmallintRepeatCount, VmState.c1Envelope]

/-- `UNTILBRK` on the stack `s body`. -/
@[vm_spec] theorem untilBrk (st : VmState) (s : Stack) (body : Continuation) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.cont body)) :
    ExceptT.run (execInstr (.contExt (.until true))) st =
      (.ok (), { st with
        stack := s, cc := body,
        regs := { st.regs with
          c0 := if body.hasC0 then .quit 0
            else .untilBody body (brkAfter (loopAfter code st.regs.c0) (.quit 0) st.regs.c1),
          c1 := brkAfter (loopAfter code st.regs.c0) (.quit 0) st.regs.c1 } }) := by
  vm_simp [hs, hcc, VmState.c1Envelope]
  cases body.hasC0 <;> rfl

/-- `UNTILENDBRK`: the rest of the code is the body. -/
@[vm_spec] theorem untilEndBrk (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata) :
    ExceptT.run (execInstr (.contExt (.untilEnd true))) st =
      (.ok (), { st with
        cc := loopRest code,
        regs := { st.regs with
          c0 := .untilBody (loopRest code) (brkAfter st.regs.c0 st.regs.c0 st.regs.c1),
          c1 := brkAfter st.regs.c0 st.regs.c0 st.regs.c1 } }) := by
  vm_simp [hcc, VmState.c1Envelope]

/-- `WHILEBRK` on the stack `s cond body`. -/
@[vm_spec] theorem whileBrk (st : VmState) (s : Stack) (cond body : Continuation) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = (s.push (.cont cond)).push (.cont body)) :
    ExceptT.run (execInstr (.contExt (.while true))) st =
      (.ok (), { st with
        stack := s, cc := cond,
        regs := { st.regs with
          c0 := if cond.hasC0 then .quit 0
            else .whileCond cond body (brkAfter (loopAfter code st.regs.c0) (.quit 0) st.regs.c1),
          c1 := brkAfter (loopAfter code st.regs.c0) (.quit 0) st.regs.c1 } }) := by
  vm_simp [hs, hcc, VmState.c1Envelope]
  cases cond.hasC0 <;> rfl

/-- `WHILEENDBRK` on the stack `s cond`: the rest of the code is the body. -/
@[vm_spec] theorem whileEndBrk (st : VmState) (s : Stack) (cond : Continuation) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.cont cond)) :
    ExceptT.run (execInstr (.contExt (.whileEnd true))) st =
      (.ok (), { st with
        stack := s, cc := cond,
        regs := { st.regs with
          c0 := if cond.hasC0 then st.regs.c0
            else .whileCond cond (loopRest code) (brkAfter st.regs.c0 st.regs.c0 st.regs.c1),
          c1 := brkAfter st.regs.c0 st.regs.c0 st.regs.c1 } }) := by
  vm_simp [hs, hcc, VmState.c1Envelope]
  cases cond.hasC0 <;> rfl

/-- `AGAINENDBRK`: `c0` saving `c1` is `c0` and `c1`, then the rest of the code forever. -/
@[vm_spec] theorem againEndBrk (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata) :
    ExceptT.run (execInstr (.contExt (.againEnd true))) st =
      (.ok (), { st with
        cc := .againBody (loopRest code),
        regs := { st.regs with c0 := st.regs.c0.defineC1 st.regs.c1, c1 := st.regs.c0.defineC1 st.regs.c1 } }) := by
  vm_simp [hcc, VmState.c1SaveSet]

end TvmLean.Spec

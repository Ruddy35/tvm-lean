import TvmLean.Proofs.Exec.Cont

/-!
# Specifications: loops, and the loop rule

In the format of `Proofs/Exec/Spec/Stack.lean`. The loop instructions (C++ `exec_while`,
`exec_until`, `exec_repeat`, `exec_again` and their `*END` forms, contops.cpp) install a loop
continuation (`whileCond`/`whileBody`, `untilBody`, `repeatBody`, `againBody`) as `c0` of the body
and run it; when the body returns, the step of the loop continuation (`VmState.stepOnceWith`) runs
the condition, the body again, or leaves the loop for the continuation after it (`loopAfter`: the
rest of the code, saving `c0`, C++ `extract_cc(1)`).

**The loop rule** (`VmState.runWith_loop`): a property `P` of every run from the states of a family
`head a` (the loop head, e.g. "the condition is about to run, with these values on the stack")
whose parameters satisfy `Inv` holds if it holds of a run out of fuel and of the run with one more
step from any such state, given it for the runs from any such state with no more fuel. An
iteration is proved by running the code (`vm_run`) from `head a` until it halts (the run leaves the
loop and ends: its goal), or reaches the loop head again (`head a'` with `Inv a'`: by the
hypothesis). `vm_run` stops at a loop head (`VmState.atLoopHead`: the current continuation is the
condition or body that `c0` loops on) so that the rule can be applied there: `vm_loop`
(`Proofs/Exec/Tactic.lean`) applies its form for an invariant of the state (`VmState.runWith_inv`)
with the family of states that differ from the loop head in gas, loaded cells, counters, `c5` and
the top stack payloads.
-/

namespace TvmLean

/-- The continuation after a loop (C++ `extract_cc(1)` of the running code `code`): the rest of
the code, saving the current `c0`. -/
abbrev loopAfter (code : Slice) (c0 : Continuation) : Continuation :=
  .ordinary code (.quit 0) { OrdCregs.empty with c0 := some c0 } OrdCdata.empty

/-- The continuation of the rest of the code (C++ `extract_cc(0)`, the body of the `*END` loops). -/
abbrev loopRest (code : Slice) : Continuation :=
  .ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty

/-- `VM.extractCc 1` (C++ `extract_cc(1)`) of a running ordinary continuation: the continuation
after the code, saving `c0`, which becomes `quit 0`. -/
@[vm_run] theorem VM.run_extractCc_1 (st : VmState) :
    ExceptT.run (VM.extractCc 1) st =
      match st.cc with
      | .ordinary code _ _ _ => (.ok (loopAfter code st.regs.c0), { st with regs := { st.regs with c0 := .quit 0 } })
      | _ => (.error .typeChk, st) := by
  unfold VM.extractCc
  rcases st with ⟨stack, regs, cc, _⟩
  cases cc <;> simp [VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_throw] <;> rfl

/-- `VM.extractCc 0` of a running ordinary continuation: the rest of the code. -/
@[vm_run] theorem VM.run_extractCc_0 (st : VmState) :
    ExceptT.run (VM.extractCc 0) st =
      match st.cc with
      | .ordinary code _ _ _ => (.ok (loopRest code), st)
      | _ => (.error .typeChk, st) := by
  unfold VM.extractCc
  rcases st with ⟨stack, regs, cc, _⟩
  cases cc <;> simp [VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_throw] <;> rfl

namespace Spec

/-- `WHILE` (C++ `exec_while`) on the stack `s cond body` while running `code`: the condition
runs, `c0` the loop (`whileCond`, unless the condition saves `c0`) with the code after the loop
saving the old `c0`. -/
@[vm_spec] theorem while_ (st : VmState) (s : Stack) (cond body : Continuation) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = (s.push (.cont cond)).push (.cont body)) :
    ExceptT.run (execInstr .while_) st =
      (.ok (), { st with
        stack := s, cc := cond,
        regs := { st.regs with c0 := if cond.hasC0 then .quit 0 else .whileCond cond body (loopAfter code st.regs.c0) } }) := by
  vm_simp [hs, hcc]
  cases cond.hasC0 <;> rfl

/-- `UNTIL` (C++ `exec_until`) on the stack `s body`: the body runs, `c0` the loop (`untilBody`,
unless the body saves `c0`). -/
@[vm_spec] theorem until_ (st : VmState) (s : Stack) (body : Continuation) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.cont body)) :
    ExceptT.run (execInstr .until) st =
      (.ok (), { st with
        stack := s, cc := body,
        regs := { st.regs with c0 := if body.hasC0 then .quit 0 else .untilBody body (loopAfter code st.regs.c0) } }) := by
  vm_simp [hs, hcc]
  cases body.hasC0 <;> rfl

/-- `AGAIN` (C++ `exec_again`) on the stack `s body`: the loop `againBody` runs the body forever
(left by an exception or a jump). -/
@[vm_spec] theorem again (st : VmState) (s : Stack) (body : Continuation) (hs : st.stack = s.push (.cont body)) :
    ExceptT.run (execInstr (.contExt (.again false))) st = (.ok (), { st with stack := s, cc := .againBody body }) := by
  vm_simp [hs]

/-- `REPEAT` (C++ `exec_repeat`) on the stack `s n body`: `n` (a 32-bit signed integer, range_chk
else) times the body, then the code after (`repeatBody`); nothing if `n ≤ 0`. -/
@[vm_spec] theorem repeat_ (st : VmState) (s : Stack) (n : Int) (body : Continuation) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = (s.push (.int (.num n))).push (.cont body)) :
    ExceptT.run (execInstr (.contExt (.repeat false))) st =
      if n < -0x80000000 ∨ n > 0x7fffffff then (.error .rangeChk, { st with stack := s })
      else if n ≤ 0 then (.ok (), { st with stack := s })
      else (.ok (), { st with
        stack := s, cc := .repeatBody body (loopAfter code st.regs.c0) n.toNat,
        regs := { st.regs with c0 := .quit 0 } }) := by
  vm_simp [hs, hcc, popSmallintRepeatCount]

/-- `WHILEEND` (C++ `exec_while_end`) on the stack `s cond`: the rest of the code is the body. -/
@[vm_spec] theorem whileEnd (st : VmState) (s : Stack) (cond : Continuation) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.cont cond)) :
    ExceptT.run (execInstr (.contExt (.whileEnd false))) st =
      (.ok (), { st with
        stack := s, cc := cond,
        regs := { st.regs with c0 := if cond.hasC0 then st.regs.c0 else .whileCond cond (loopRest code) st.regs.c0 } }) := by
  vm_simp [hs, hcc]
  cases cond.hasC0 <;> rfl

/-- `UNTILEND` (C++ `exec_until_end`): the rest of the code is the body. -/
@[vm_spec] theorem untilEnd (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata)
    (hcc : st.cc = .ordinary code saved cregs cdata) :
    ExceptT.run (execInstr (.contExt (.untilEnd false))) st =
      (.ok (), { st with
        cc := loopRest code,
        regs := { st.regs with c0 := .untilBody (loopRest code) st.regs.c0 } }) := by
  vm_simp [hcc]

/-- `AGAINEND` (C++ `exec_again_end`): the rest of the code, forever. -/
@[vm_spec] theorem againEnd (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata)
    (hcc : st.cc = .ordinary code saved cregs cdata) :
    ExceptT.run (execInstr (.contExt (.againEnd false))) st =
      (.ok (), { st with cc := .againBody (loopRest code) }) := by
  vm_simp [hcc]

end Spec

/-! ## The loop rule -/

/-- **The loop rule.** For a family of states `head a` (a loop head) and an invariant `Inv` of its
parameters: if `P` holds of the run out of fuel from every head, and of the run with `n + 1` steps
from every head given that it holds of the runs with at most `n` steps from every head, then it
holds of every run from every head. (Strong induction on the fuel: an iteration that comes back to
the loop head has used at least one step.) -/
theorem VmState.runWith_loop {α : Type} (exec : Instr → VM Unit) (head : α → VmState) (Inv : α → Prop)
    (P : StepResult → Prop)
    (hzero : ∀ a, Inv a → P ((head a).runWith exec 0))
    (hstep : ∀ n a, Inv a → (∀ m, m ≤ n → ∀ a', Inv a' → P ((head a').runWith exec m)) →
      P ((head a).runWith exec (n + 1))) :
    ∀ n a, Inv a → P ((head a).runWith exec n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a ha
    cases n with
    | zero => exact hzero a ha
    | succ n => exact hstep n a ha (fun m hm a' ha' => ih m (by omega) a' ha')

/-- The loop rule for an invariant of the state (`VmState.runWith_loop` with the states as their
own parameters): the form `vm_loop` applies. -/
theorem VmState.runWith_inv (exec : Instr → VM Unit) (Inv : VmState → Prop) (P : StepResult → Prop)
    (hzero : ∀ st, Inv st → P (st.runWith exec 0))
    (hstep : ∀ n st, Inv st → (∀ m, m ≤ n → ∀ st', Inv st' → P (st'.runWith exec m)) →
      P (st.runWith exec (n + 1))) :
    ∀ n st, Inv st → P (st.runWith exec n) :=
  VmState.runWith_loop exec id Inv P hzero hstep

/-- A loop head: the current continuation is the condition (`whileCond`) or body (`untilBody`,
`repeatBody`, `againBody`) that `c0` or the current continuation loops on. `vm_run` does not step
from it (`vm_not_at_loop_head`), so that the loop rule is applied there. -/
def VmState.atLoopHead (st : VmState) : Bool :=
  match st.regs.c0 with
  | .whileCond cond _ _ => cond.beq st.cc
  | .untilBody body _ => body.beq st.cc
  | .repeatBody body _ _ => body.beq st.cc
  | .againBody body => body.beq st.cc
  | _ => false

end TvmLean

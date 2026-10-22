import TvmLean.Proofs.Exec.Run

/-!
# Continuations with closure data

A continuation of TVM carries saved control registers (`OrdCregs`, C++ `ControlData::save`) and
closure data (`OrdCdata`: a captured stack and the number of arguments it takes, C++
`ControlData::stack` and `nargs`). Entering one applies them as C++ `VmState::adjust_cr` and
`adjust_jump_cont` do. The lemmas here state that entry for any continuation, and the steps of the
continuations of the loops, so that `vm_run` follows code that keeps closures and loops:

* `OrdCregs.restore`: the registers after entering a continuation with saved registers `cregs`;
  `VmState.closureStack`: the stack (and its gas) after entering one with closure data `cdata`;
  `VmState.applyCregsCdata_eq` puts the model's entry in these terms, `VmState.enter_eq` the step
  that enters an ordinary continuation with saved registers.
* `VM.run_jump_whileCond` and the like: a jump to the continuations of the loops (`WHILE`,
  `UNTIL`, `REPEAT`, `AGAIN`, and `pushInt`): they become the current continuation, entered at the
  next step.
* `VmState.jumped_eq`, `Continuation.hasC0_*`: the steps of the loop continuations
  (`VmState.stepOnceWith`, unfolded by `vm_step`).

The instructions that jump to or call a continuation without closure data (`JMPX`, `EXECUTE`,
`IF*`, `RET`) are specified in `Proofs/Exec/Spec/Flow.lean`; a jump or call of a continuation with
closure data runs the model's `VM.jump`/`VM.call` through `vm_run`'s lemmas.
-/

namespace TvmLean

/-! ## Entering a continuation -/

/-- The registers after entering a continuation that saved `cregs` (C++ `adjust_cr`): each saved
register replaces the current one. -/
def OrdCregs.restore (cregs : OrdCregs) (r : Regs) : Regs :=
  { c0 := cregs.c0.getD r.c0, c1 := cregs.c1.getD r.c1, c2 := cregs.c2.getD r.c2, c3 := cregs.c3.getD r.c3,
    c4 := cregs.c4.getD r.c4, c5 := cregs.c5.getD r.c5, c7 := cregs.c7.getD r.c7 }

/-- The state after the closure data `cdata` is applied to the stack (C++ `adjust_jump_cont`): with
`nargs ≥ 0` only the top `nargs` values are kept (the stack gas of the new depth charged if it
shrank), and a captured stack is put below them (its gas charged). -/
def VmState.closureStack (st : VmState) (cdata : OrdCdata) : VmState :=
  let stack1 : Stack :=
    if 0 ≤ cdata.nargs ∧ cdata.nargs.toNat < st.stack.size then
      st.stack.extract (st.stack.size - cdata.nargs.toNat) st.stack.size
    else st.stack
  if cdata.stack.isEmpty then
    if 0 ≤ cdata.nargs ∧ cdata.nargs.toNat < st.stack.size then
      { st with stack := stack1 }.consumeStackGas stack1.size
    else st
  else { st with stack := cdata.stack ++ stack1 }.consumeStackGas (cdata.stack ++ stack1).size

attribute [vm_run] OrdCregs.restore

attribute [vm_run] OrdCregs.empty_c0 OrdCregs.empty_c1 OrdCregs.empty_c2 OrdCregs.empty_c3
  OrdCregs.empty_c4 OrdCregs.empty_c5 OrdCregs.empty_c7 OrdCdata.empty_stack
@[vm_run] theorem OrdCdata.empty_nargs : OrdCdata.empty.nargs = -1 := rfl

/-- The closure data without a stack or arguments is `OrdCdata.empty`. -/
@[vm_run] theorem OrdCdata.mk_empty : ({ stack := #[], nargs := -1 } : OrdCdata) = OrdCdata.empty := rfl

@[vm_run] theorem VM.option_getD_some {α : Type} (a b : α) : (some a).getD b = a := rfl
@[vm_run] theorem VM.option_getD_none {α : Type} (b : α) : (none : Option α).getD b = b := rfl

/-- The closure data `OrdCdata.empty` leaves the state. -/
@[vm_run] theorem VmState.closureStack_empty (st : VmState) : st.closureStack OrdCdata.empty = st := by
  simp [VmState.closureStack, OrdCdata.empty]

/-- The registers written out field by field are the registers. -/
@[vm_run] theorem Regs.mk_eta (r : Regs) : Regs.mk r.c0 r.c1 r.c2 r.c3 r.c4 r.c5 r.c7 = r := rfl

/-- **Entering a continuation** (`VmState.applyCregsCdata`, C++ `adjust_cr` and `adjust_jump_cont`):
the saved registers restored, then the closure data applied. (Of low priority: entering a
continuation without saved registers or closure data is `VmState.applyCregsCdata_empty`.) -/
@[vm_run low] theorem VmState.applyCregsCdata_eq (st : VmState) (cregs : OrdCregs) (cdata : OrdCdata) :
    st.applyCregsCdata cregs cdata = { st with regs := cregs.restore st.regs }.closureStack cdata := by
  unfold VmState.applyCregsCdata VmState.closureStack OrdCregs.restore
  rcases cregs with ⟨c0, c1, c2, c3, c4, c5, c7⟩
  rcases cdata with ⟨cs, n⟩
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;> cases c7 <;>
    simp only [Option.getD_some, Option.getD_none] <;>
    by_cases h : 0 ≤ n <;> by_cases h2 : n.toNat < st.stack.size <;> simp [h, h2] <;> rfl

/-! ## Jumps to the continuations of loops -/

@[vm_run] theorem VM.run_jump_whileCond (st : VmState) (c b a : Continuation) :
    ExceptT.run (VM.jump (.whileCond c b a)) st = (.ok (), { st with cc := .whileCond c b a }) := by
  simp [VM.jump, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

@[vm_run] theorem VM.run_jump_whileBody (st : VmState) (c b a : Continuation) :
    ExceptT.run (VM.jump (.whileBody c b a)) st = (.ok (), { st with cc := .whileBody c b a }) := by
  simp [VM.jump, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

@[vm_run] theorem VM.run_jump_untilBody (st : VmState) (b a : Continuation) :
    ExceptT.run (VM.jump (.untilBody b a)) st = (.ok (), { st with cc := .untilBody b a }) := by
  simp [VM.jump, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

@[vm_run] theorem VM.run_jump_repeatBody (st : VmState) (b a : Continuation) (n : Nat) :
    ExceptT.run (VM.jump (.repeatBody b a n)) st = (.ok (), { st with cc := .repeatBody b a n }) := by
  simp [VM.jump, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

@[vm_run] theorem VM.run_jump_againBody (st : VmState) (b : Continuation) :
    ExceptT.run (VM.jump (.againBody b)) st = (.ok (), { st with cc := .againBody b }) := by
  simp [VM.jump, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

@[vm_run] theorem VM.run_jump_pushInt (st : VmState) (n : Int) (k : Continuation) :
    ExceptT.run (VM.jump (.pushInt n k)) st = (.ok (), { st with cc := .pushInt n k }) := by
  simp [VM.jump, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

/-! ## Steps of the loop continuations -/

/-- Whether a continuation saves `c0` (C++ `ControlData::save.c0`): the loops install themselves
as `c0` of their body only if it does not. -/
@[vm_run] theorem Continuation.hasC0_ordinary (code : Slice) (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) :
    (Continuation.ordinary code saved cregs cdata).hasC0 = cregs.c0.isSome := rfl
@[vm_run] theorem Continuation.hasC0_envelope (k : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) :
    (Continuation.envelope k cregs cdata).hasC0 = cregs.c0.isSome := rfl
@[vm_run] theorem Continuation.hasC0_quit (n : Int) : (Continuation.quit n).hasC0 = false := rfl
@[vm_run] theorem VM.option_isSome_none {α : Type} : (none : Option α).isSome = false := rfl
@[vm_run] theorem VM.option_isSome_some {α : Type} (a : α) : (some a).isSome = true := rfl

/-- The end of a step that jumped from a continuation that is not ordinary (a loop's, `quit`) to
another (`VmState.jumped`): the jump counted, out of gas at once if it costs gas it does not have. -/
@[vm_run] theorem VmState.jumped_eq (st : VmState) :
    st.jumped = if st.countJump.gasExhaustedNow then st.countJump.outOfGasHalt else .continue st.countJump := rfl

/-- The step that enters an ordinary continuation (`VmState.enter`), for any saved registers. Of low
priority: without saved registers it is `VmState.enter_empty`. -/
@[vm_run low] theorem VmState.enter_eq (st : VmState) (cregs : OrdCregs) (cc : Continuation) :
    st.enter cregs cc =
      { (st.applyCregsCdata cregs OrdCdata.empty).countJump with
        cc := cc, chainJumps := 0, steps := (st.applyCregsCdata cregs OrdCdata.empty).countJump.steps + 1 } := rfl

end TvmLean

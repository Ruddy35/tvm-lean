import TvmLean.Semantics

/-!
# One step of the VM, decomposed

`VmState.stepOnceWith` (one step of C++ `VmState::run`) does a lot before it runs an instruction:
it enters the current continuation (its saved control registers, closure stack and argument count),
counts the jump, checks the gas, decodes the next instruction, checks its global version and charges
its gas. When the current continuation is an ordinary one that is running (no closure stack) all of
this is fixed by the code bits: the theorems here say what is left, so that a proof about concrete
code on a symbolic stack only has to evaluate the decoder (`decodeCp0WithBits` on the concrete code,
by `decide`) and the instruction itself.

* `VmState.stepOnceWith_ordinary`: entering an ordinary continuation with no closure data (the
  jumps of the model clear it) leaves the step of its code, `VmState.codeStep`, in the state
  `VmState.enter` (its saved registers applied, the jump counted).
* `VmState.stepOnceWith_instr`: the next instruction `i` (decoded from `code` with `n` bits, the
  rest of the code `rest`) runs on the state with the code advanced and its gas `instrGas i n`
  charged; the step ends as `VmState.instrStep` says.
* `VmState.stepOnceWith_implicitRet`, `VmState.stepOnceWith_implicitJmpRef`: the code is
  exhausted (C++ `VmState::step`: implicit `RET`, implicit `JMPREF` to the first reference).
* `VmState.stepWith_of_stepOnceWith`: the libraries refused by `max_library_loads` change nothing
  when the step notes no refusal (`VmState.stepWith`), so `VmState.step` is `stepOnceWith`.
* `VmState.runWith_succ_*`: one step of a run.
-/

namespace TvmLean

/-- The 24-bit opcode `VmState.stepOnceWith` reads from `code` (its first 24 bits, zero-padded),
whose global version it checks (`cp0RequiredVersion`). -/
def Slice.opcode24 (code : Slice) : Nat :=
  let head : BitString := code.readBits (Nat.min 24 code.bitsRemaining)
  bitsToNat (head ++ Array.replicate (24 - head.size) false)

/-- How a step ends once its instruction `i` is decoded and `st` is the state with the code
advanced and the instruction's gas charged (`VmState.stepOnceWith`): out of gas at once from version
4 (C++ `consume_gas` in `OpcodeInstr*::dispatch`); else `exec i` runs; the `gas.check()` after it
ends the VM out of gas, an exception is handled by `VmState.raiseException` (an out of gas raised
inside the instruction ends the VM). -/
def VmState.instrStep (exec : Instr → VM Unit) (i : Instr) (st : VmState) : StepResult :=
  if st.gasExhaustedNow then st.outOfGasHalt else
  let (res, st1) := (exec i).run st
  match res with
  | .ok _ => if decide (st1.gas.gasRemaining < 0) then st1.outOfGasHalt else .continue st1
  | .error e => if e = .outOfGas then st1.outOfGasHalt else st1.raiseException e.toInt

/-- The state of the step that enters an ordinary continuation with the saved registers `cregs`
and no closure data from `st` (`VmState.stepOnceWith`): the registers applied (`applyCregsCdata`),
the jump counted (`countJump`), the current continuation `cc`, the jump chain ended and the step
counted. -/
def VmState.enter (st : VmState) (cregs : OrdCregs) (cc : Continuation) : VmState :=
  let st2 := (st.applyCregsCdata cregs OrdCdata.empty).countJump
  { st2 with cc := cc, chainJumps := 0, steps := st2.steps + 1 }

/-- The plain continuation running `code` that `VmState.stepOnceWith` leaves after an instruction. -/
abbrev Continuation.plain (code : Slice) : Continuation :=
  .ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty

/-- How the step of an implicit `RET` ends once its gas is charged on `st` (`VmState.stepOnceWith`):
out of gas (`consume_gas_chk`), else `VM.ret` runs and the `gas.check()` after it may end the VM
out of gas; an exception is handled by `VmState.raiseException`. -/
def VmState.retStep (st : VmState) : StepResult :=
  if decide (st.gas.gasRemaining < 0) then st.outOfGasHalt else
  let (res, st1) := (VM.ret).run st
  match res with
  | .ok _ => if decide (st1.gas.gasRemaining < 0) then st1.outOfGasHalt else .continue st1
  | .error e => st1.raiseException e.toInt

/-- How the step of an implicit `JMPREF` to the first reference of `code` ends once its gas is
charged on `st` (`VmState.stepOnceWith`): the reference is loaded (`load_cell_slice_ref`, a library
cell runs its library's root) and becomes the code of the current continuation. -/
def VmState.jmpRefStep (code : Slice) (st : VmState) : StepResult :=
  if decide (st.gas.gasRemaining < 0) then st.outOfGasHalt else
  if code.refPos < code.cell.refs.size then
    let refCell := code.cell.refs[code.refPos]!
    let (st1, exhausted) := st.registerCellLoads (.cell refCell :: (st.libraryLoads refCell).toList)
    if exhausted then
      st1.outOfGasHalt
    else
      match (libraryResolveLoads st1.libraries st1.globalVersion refCell st1.librariesRefused).2 with
      | .ok root =>
          if decide (st1.gas.gasRemaining < 0) then st1.outOfGasHalt else
          .continue { st1 with cc := .ordinary (Slice.ofCell root) (.quit 0) OrdCregs.empty OrdCdata.empty }
      | .error e => st1.raiseException e.toInt
  else
    st.raiseException Excno.cellUnd.toInt

theorem OrdCdata.empty_needsMoreArgs (depth : Nat) : OrdCdata.empty.needsMoreArgs depth = false := by
  simp [OrdCdata.needsMoreArgs, OrdCdata.empty]

theorem VmState.enteredCdata_empty (st : VmState) : st.enteredCdata OrdCdata.empty = OrdCdata.empty := by
  unfold VmState.enteredCdata; split <;> rfl

/-- With no closure data, entering a continuation only changes the registers. -/
theorem VmState.applyCregsCdata_emptyCdata (st : VmState) (cregs : OrdCregs) :
    st.applyCregsCdata cregs OrdCdata.empty = { st with regs := (st.applyCregsCdata cregs OrdCdata.empty).regs } := by
  simp [VmState.applyCregsCdata, OrdCdata.empty]

theorem VmState.applyCregsCdata_gas (st : VmState) (cregs : OrdCregs) :
    (st.applyCregsCdata cregs OrdCdata.empty).gas = st.gas := by
  simp [VmState.applyCregsCdata, OrdCdata.empty]

theorem VmState.applyCregsCdata_steps (st : VmState) (cregs : OrdCregs) :
    (st.applyCregsCdata cregs OrdCdata.empty).steps = st.steps := by
  simp [VmState.applyCregsCdata, OrdCdata.empty]

theorem VmState.ranOutEntering_self_gas (st st' : VmState) (h : st'.gas = st.gas) :
    VmState.ranOutEntering st st' = false := by
  simp only [VmState.ranOutEntering, h, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem VmState.countJump_steps (st : VmState) : st.countJump.steps = st.steps := by
  simp only [VmState.countJump]; split <;> rfl

/-- The rest of a step of `VmState.stepOnceWith` once the ordinary continuation running `code` is
entered (`st`): the implicit `RET` (no bits, no references left), the implicit `JMPREF` (no bits
left), or the next instruction (an opcode of a later global version, an invalid opcode, or the
instruction decoded, `VmState.instrStep`). -/
def VmState.codeStep (exec : Instr → VM Unit) (code : Slice) (st : VmState) : StepResult :=
  if code.bitsRemaining == 0 then
    if code.refsRemaining == 0 then VmState.retStep (st.consumeGas implicitRetGasPrice)
    else VmState.jmpRefStep code (st.consumeGas implicitJmpRefGasPrice)
  else if st.cp = 0 ∧ st.globalVersion < cp0RequiredVersion code.opcode24 then
    let st0 := st.consumeGas gasPerInstr
    if st0.gasExhaustedNow then st0.outOfGasHalt else st0.raiseException Excno.invOpcode.toInt
  else
    let decoded : Except Excno (Instr × Nat × Slice) :=
      if st.cp = 0 then decodeCp0WithBits code else .error .invOpcode
    match decoded with
    | .error e =>
        let st0 :=
          if e = .invOpcode ∧ code.bitsRemaining > 0 then
            st.consumeGas (gasPerInstr + Int.ofNat (cp0InvOpcodeGasBits code))
          else st
        if st0.gasExhaustedNow then st0.outOfGasHalt else st0.raiseException e.toInt
    | .ok (instr, totBits, rest) =>
        VmState.instrStep exec instr ({ st with cc := .plain rest }.consumeGas (instrGas instr totBits))

/-- **The step of an ordinary continuation.** If the current continuation is an ordinary
continuation with no closure data (the jumps of the model clear it) and entering it does not find
the gas exhausted, the step runs its code (`VmState.codeStep`) in the state that entered it. -/
theorem VmState.stepOnceWith_ordinary (exec : Instr → VM Unit) (st : VmState) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs)
    (hcc : st.cc = .ordinary code saved cregs OrdCdata.empty)
    (hgas : ((st.applyCregsCdata cregs OrdCdata.empty).countJump).gasExhaustedNow = false) :
    st.stepOnceWith exec =
      VmState.codeStep exec code (st.enter cregs (.ordinary code saved OrdCregs.empty OrdCdata.empty)) := by
  unfold VmState.stepOnceWith
  rw [hcc]
  simp only [VmState.enteredCdata_empty, OrdCdata.empty_needsMoreArgs, Bool.false_eq_true, if_false]
  rw [VmState.ranOutEntering_self_gas _ _ (VmState.applyCregsCdata_gas _ _)]
  simp only [Bool.false_eq_true, if_false, hgas]
  unfold VmState.codeStep VmState.enter
  generalize (st.applyCregsCdata cregs OrdCdata.empty).countJump = E
  rfl

theorem VmState.enter_cp (st : VmState) (cregs : OrdCregs) (cc : Continuation) :
    (st.enter cregs cc).cp = st.cp := by
  simp only [VmState.enter]
  rw [VmState.applyCregsCdata_emptyCdata]
  simp only [VmState.countJump]; split <;> rfl

theorem VmState.enter_globalVersion (st : VmState) (cregs : OrdCregs) (cc : Continuation) :
    (st.enter cregs cc).globalVersion = st.globalVersion := by
  simp only [VmState.enter]
  rw [VmState.applyCregsCdata_emptyCdata]
  simp only [VmState.countJump]; split <;> rfl

/-- **The step of an instruction.** If the current continuation is an ordinary continuation that
is running (no closure data: the jumps of the model clear it) on the code `code`, whose next
instruction (codepage 0, available at the global version) decodes to `i` of `n` bits followed by
`rest`, and the gas is not exhausted, the step charges `instrGas i n` and runs `exec i` on the state
with the code advanced (`VmState.enter`), ending as `VmState.instrStep` says. -/
theorem VmState.stepOnceWith_instr (exec : Instr → VM Unit) (st : VmState) (code rest : Slice)
    (saved : Continuation) (cregs : OrdCregs) (i : Instr) (n : Nat)
    (hcc : st.cc = .ordinary code saved cregs OrdCdata.empty)
    (hgas : ((st.applyCregsCdata cregs OrdCdata.empty).countJump).gasExhaustedNow = false)
    (hcp : st.cp = 0)
    (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : decodeCp0WithBits code = .ok (i, n, rest)) :
    st.stepOnceWith exec =
      VmState.instrStep exec i ((st.enter cregs (.plain rest)).consumeGas (instrGas i n)) := by
  rw [VmState.stepOnceWith_ordinary exec st code saved cregs hcc hgas]
  unfold VmState.codeStep
  rw [if_neg (by simpa using hbits),
    if_neg (by rw [VmState.enter_cp, VmState.enter_globalVersion]; omega),
    if_pos (by rw [VmState.enter_cp]; exact hcp), hdec]
  rfl

/-- **Implicit `RET`.** The code of the running ordinary continuation is exhausted (no bits, no
references): C++ `VmState::step` charges `implicit_ret_gas_price` and returns (`VmState.retStep`). -/
theorem VmState.stepOnceWith_implicitRet (exec : Instr → VM Unit) (st : VmState) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs)
    (hcc : st.cc = .ordinary code saved cregs OrdCdata.empty)
    (hgas : ((st.applyCregsCdata cregs OrdCdata.empty).countJump).gasExhaustedNow = false)
    (hbits : code.bitsRemaining = 0) (hrefs : code.refsRemaining = 0) :
    st.stepOnceWith exec =
      VmState.retStep ((st.enter cregs (.ordinary code saved OrdCregs.empty OrdCdata.empty)).consumeGas
        implicitRetGasPrice) := by
  rw [VmState.stepOnceWith_ordinary exec st code saved cregs hcc hgas]
  simp only [VmState.codeStep, hbits, hrefs, beq_self_eq_true, if_true]

/-- **Implicit `JMPREF`.** The code of the running ordinary continuation has no bits left but a
reference: C++ `VmState::step` charges `implicit_jmpref_gas_price` and jumps to the reference
(`VmState.jmpRefStep`). -/
theorem VmState.stepOnceWith_implicitJmpRef (exec : Instr → VM Unit) (st : VmState) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs)
    (hcc : st.cc = .ordinary code saved cregs OrdCdata.empty)
    (hgas : ((st.applyCregsCdata cregs OrdCdata.empty).countJump).gasExhaustedNow = false)
    (hbits : code.bitsRemaining = 0) (hrefs : code.refsRemaining ≠ 0) :
    st.stepOnceWith exec =
      VmState.jmpRefStep code ((st.enter cregs (.ordinary code saved OrdCregs.empty OrdCdata.empty)).consumeGas
        implicitJmpRefGasPrice) := by
  have hrefs' : (code.refsRemaining == 0) = false := by simpa using hrefs
  rw [VmState.stepOnceWith_ordinary exec st code saved cregs hcc hgas]
  simp only [VmState.codeStep, hbits, hrefs', beq_self_eq_true, if_true, Bool.false_eq_true, if_false]

/-! ## Entering a continuation without saved registers -/

theorem VmState.applyCregsCdata_empty (st : VmState) :
    st.applyCregsCdata OrdCregs.empty OrdCdata.empty = st := by
  simp [VmState.applyCregsCdata, OrdCregs.empty, OrdCdata.empty]

theorem VmState.countJump_of_lt (st : VmState) (h : st.chainJumps < freeNestedContJump) :
    st.countJump = { st with chainJumps := st.chainJumps + 1 } := by
  simp only [VmState.countJump]
  rw [if_neg (by omega)]

/-- Entering a continuation with no saved registers in a chain of fewer than
`freeNestedContJump` jumps changes nothing but the continuation, the chain and the steps. -/
theorem VmState.enter_empty (st : VmState) (cc : Continuation) (h : st.chainJumps < freeNestedContJump) :
    st.enter OrdCregs.empty cc = { st with cc := cc, chainJumps := 0, steps := st.steps + 1 } := by
  simp only [VmState.enter, VmState.applyCregsCdata_empty, VmState.countJump_of_lt st h]

theorem VmState.gasExhaustedNow_enterCheck_empty (st : VmState) (h : st.chainJumps < freeNestedContJump) :
    ((st.applyCregsCdata OrdCregs.empty OrdCdata.empty).countJump).gasExhaustedNow = st.gasExhaustedNow := by
  simp only [VmState.applyCregsCdata_empty, VmState.countJump_of_lt st h, VmState.gasExhaustedNow]

/-! ## The libraries refused by `max_library_loads` -/

theorem VmState.with_libraries_self (st : VmState) (hr : st.librariesRefused = #[])
    (hm : st.librariesMissed = #[]) :
    { st with librariesRefused := #[], librariesMissed := #[] } = st := by
  cases st; simp_all

theorem StepResult.mapState_self (r : StepResult) (f : VmState → VmState) (h : f r.state = r.state) :
    r.mapState f = r := by
  cases r <;> simp_all [StepResult.mapState, StepResult.state]

/-- **`VmState.stepWith` is one step.** Between steps no library is refused or noted
(`VmState.stepWith` clears both); a step that notes no refusal C++ makes is the step of C++,
whatever `max_library_loads` is. -/
theorem VmState.stepWith_eq_stepOnceWith (exec : Instr → VM Unit) (st : VmState)
    (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hr' : (st.stepOnceWith exec).state.librariesRefused = #[])
    (hm' : (st.stepOnceWith exec).state.librariesMissed = #[]) :
    st.stepWith exec = st.stepOnceWith exec := by
  unfold VmState.stepWith
  split
  · rfl
  · simp only [VmState.stepRefusingWith, libraryStepReruns, VmState.with_libraries_self st hr hm, hm',
      Array.isEmpty_empty, if_true]
    exact StepResult.mapState_self _ _ (VmState.with_libraries_self _ hr' hm')

/-- `VmState.stepWith_eq_stepOnceWith` with the step computed first. -/
theorem VmState.stepWith_of_stepOnceWith (exec : Instr → VM Unit) (st : VmState) (r : StepResult)
    (h : st.stepOnceWith exec = r)
    (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hr' : r.state.librariesRefused = #[]) (hm' : r.state.librariesMissed = #[]) :
    st.stepWith exec = r := by
  subst h
  exact VmState.stepWith_eq_stepOnceWith exec st hr hm hr' hm'

theorem VmState.step_eq (st : VmState) : st.step = st.stepWith execInstr := rfl

/-! ## Runs -/

/-- The result of a run whose last step halted with `exitCode` in `st` (`VmState.runWith`):
`try_commit` after exit code 0 or 1. -/
def VmState.haltResult (exitCode : Int) (st : VmState) : StepResult :=
  if exitCode = -1 ∨ exitCode = -2 then
    let (ok, st'') := st.tryCommit
    if ok then .halt exitCode st''
    else .halt (~~~ Excno.cellOv.toInt) { st'' with stack := #[.int (.num 0)] }
  else .halt exitCode st

theorem VmState.runWith_succ (exec : Instr → VM Unit) (fuel : Nat) (st : VmState) :
    st.runWith exec (fuel + 1) =
      match st.stepWith exec with
      | .continue st' => st'.runWith exec fuel
      | .halt exitCode st' => VmState.haltResult exitCode st' := by
  simp only [VmState.runWith, VmState.haltResult]
  rfl

theorem VmState.runWith_succ_continue (exec : Instr → VM Unit) (fuel : Nat) (st st' : VmState)
    (h : st.stepWith exec = .continue st') : st.runWith exec (fuel + 1) = st'.runWith exec fuel := by
  rw [VmState.runWith_succ, h]

theorem VmState.run_eq (fuel : Nat) (st : VmState) : VmState.run fuel st = st.runWith execInstr fuel := rfl

theorem VmState.runWith_succ_halt (exec : Instr → VM Unit) (fuel : Nat) (st st' : VmState) (ec : Int)
    (h : st.stepWith exec = .halt ec st') : st.runWith exec (fuel + 1) = VmState.haltResult ec st' := by
  rw [VmState.runWith_succ, h]

end TvmLean

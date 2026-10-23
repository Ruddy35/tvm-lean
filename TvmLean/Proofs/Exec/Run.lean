import TvmLean.Proofs.Exec.Step
import TvmLean.Proofs.Exec.Eval
import TvmLean.Proofs.Basic

/-!
# A run, one step at a time, as rewriting

The forms of `Proofs/Exec/Step.lean` stated so that `simp` can use them on a state written out (a
`VmState.mk` term with unknown fields, as a symbolic run makes): no hypothesis whose variables are
not in the left side, the cases of a step as `if`s in the result.

* `VmState.runWith_succ'`: a run is its first step followed by the rest (`VmState.runCont`), which
  distributes over the cases of the step (`VmState.runCont_ite`).
* `VmState.stepWith_unfold`: `VmState.stepWith` on a state between steps.
* `VmState.stepOnceWith_ordinary'`: the step of an ordinary continuation without closure data is
  the step of its code (`VmState.codeStep`) after the entry's gas check.
-/

namespace TvmLean

/-- What a run does after a step with result `r`: go on with `fuel` steps from a continuing state,
or end with `VmState.haltResult`. -/
def VmState.runCont (exec : Instr → VM Unit) (fuel : Nat) : StepResult → StepResult
  | .continue st => st.runWith exec fuel
  | .halt exitCode st => VmState.haltResult exitCode st

theorem VmState.runWith_succ' (exec : Instr → VM Unit) (fuel : Nat) (st : VmState) :
    st.runWith exec (fuel + 1) = VmState.runCont exec fuel (st.stepWith exec) := by
  rw [VmState.runWith_succ]
  cases st.stepWith exec <;> rfl

/-- A run out of fuel halts with `fatal` (`VmState.runWith`). -/
theorem VmState.runWith_zero (exec : Instr → VM Unit) (st : VmState) :
    st.runWith exec 0 = .halt Excno.fatal.toInt st := rfl

theorem VmState.runCont_continue (exec : Instr → VM Unit) (fuel : Nat) (st : VmState) :
    VmState.runCont exec fuel (.continue st) = st.runWith exec fuel := rfl

theorem VmState.runCont_halt (exec : Instr → VM Unit) (fuel : Nat) (ec : Int) (st : VmState) :
    VmState.runCont exec fuel (.halt ec st) = VmState.haltResult ec st := rfl

theorem VmState.runCont_ite (exec : Instr → VM Unit) (fuel : Nat) (c : Prop) [Decidable c] (x y : StepResult) :
    VmState.runCont exec fuel (if c then x else y) = if c then VmState.runCont exec fuel x else VmState.runCont exec fuel y := by
  split <;> rfl

theorem VmState.runCont_dite (exec : Instr → VM Unit) (fuel : Nat) (c : Prop) [Decidable c]
    (x : c → StepResult) (y : ¬c → StepResult) :
    VmState.runCont exec fuel (if h : c then x h else y h) =
      if h : c then VmState.runCont exec fuel (x h) else VmState.runCont exec fuel (y h) := by
  split <;> rfl

theorem StepResult.state_ite (c : Prop) [Decidable c] (x y : StepResult) :
    (if c then x else y).state = if c then x.state else y.state := by
  split <;> rfl
theorem StepResult.mapState_continue (f : VmState → VmState) (st : VmState) :
    (StepResult.continue st).mapState f = .continue (f st) := rfl
theorem StepResult.mapState_halt (f : VmState → VmState) (ec : Int) (st : VmState) :
    (StepResult.halt ec st).mapState f = .halt ec (f st) := rfl
theorem StepResult.mapState_ite (f : VmState → VmState) (c : Prop) [Decidable c] (x y : StepResult) :
    (if c then x else y).mapState f = if c then x.mapState f else y.mapState f := by
  split <;> rfl

/-- How the step of an instruction ends once it ran with result `r` (`VmState.instrStep`): the
`gas.check()` after it, or the exception handled. -/
def VmState.instrEnd (r : Except Excno Unit × VmState) : StepResult :=
  match r with
  | (.ok _, st1) => if decide (st1.gas.remaining < 0) then st1.outOfGasHalt else .continue st1
  | (.error e, st1) => if e = .outOfGas then st1.outOfGasHalt else st1.raiseException e.toInt

theorem VmState.instrStep_eq (exec : Instr → VM Unit) (i : Instr) (st : VmState) :
    VmState.instrStep exec i st =
      if st.gasExhaustedNow then st.outOfGasHalt else VmState.instrEnd (ExceptT.run (exec i) st) := by
  unfold VmState.instrStep VmState.instrEnd
  split
  · rfl
  · rcases ExceptT.run (exec i) st with ⟨r, st1⟩
    cases r <;> rfl

theorem VmState.instrEnd_ok (st : VmState) :
    VmState.instrEnd (.ok (), st) =
      if decide (st.gas.remaining < 0) then st.outOfGasHalt else .continue st := rfl

theorem VmState.instrEnd_error (e : Excno) (st : VmState) :
    VmState.instrEnd (.error e, st) = if e = .outOfGas then st.outOfGasHalt else st.raiseException e.toInt := rfl

theorem VmState.instrEnd_ite (c : Prop) [Decidable c] (x y : Except Excno Unit × VmState) :
    VmState.instrEnd (if c then x else y) = if c then VmState.instrEnd x else VmState.instrEnd y := by
  split <;> rfl

theorem VmState.instrEnd_ite_id (c : Prop) [Decidable c] (x y : Id (Except Excno Unit × VmState)) :
    VmState.instrEnd (@ite (Id (Except Excno Unit × VmState)) c _ x y) =
      if c then VmState.instrEnd x else VmState.instrEnd y := by
  split <;> rfl

theorem VmState.instrEnd_dite (c : Prop) [Decidable c] (x : c → Except Excno Unit × VmState)
    (y : ¬c → Except Excno Unit × VmState) :
    VmState.instrEnd (if h : c then x h else y h) = if h : c then VmState.instrEnd (x h) else VmState.instrEnd (y h) := by
  split <;> rfl

/-- How the step of an implicit `RET` ends once `VM.ret` ran with result `r` (`VmState.retStep`). -/
def VmState.retEnd (r : Except Excno Unit × VmState) : StepResult :=
  match r with
  | (.ok _, st1) => if decide (st1.gas.remaining < 0) then st1.outOfGasHalt else .continue st1
  | (.error e, st1) => st1.raiseException e.toInt

theorem VmState.retStep_eq (st : VmState) :
    VmState.retStep st =
      if decide (st.gas.remaining < 0) then st.outOfGasHalt else VmState.retEnd (ExceptT.run VM.ret st) := by
  unfold VmState.retStep VmState.retEnd
  split
  · rfl
  · rcases ExceptT.run VM.ret st with ⟨r, st1⟩
    cases r <;> rfl

theorem VmState.retEnd_ok (st : VmState) :
    VmState.retEnd (.ok (), st) = if decide (st.gas.remaining < 0) then st.outOfGasHalt else .continue st := rfl

theorem VmState.retEnd_error (e : Excno) (st : VmState) :
    VmState.retEnd (.error e, st) = st.raiseException e.toInt := rfl

/-- `VmState.stepWith` on a state between steps (no library refused or noted): the step, and, when
`max_library_loads` is set, the step again with the libraries it notes refused if it notes any. -/
theorem VmState.stepWith_unfold (exec : Instr → VM Unit) (st : VmState)
    (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[]) :
    st.stepWith exec =
      if st.maxLibraryLoads.isNone then st.stepOnceWith exec
      else if (st.stepOnceWith exec).state.librariesMissed.isEmpty then
        (st.stepOnceWith exec).mapState fun st => { st with librariesRefused := #[], librariesMissed := #[] }
      else st.stepRefusingWith exec (#[] ++ (st.stepOnceWith exec).state.librariesMissed) 7 := by
  unfold VmState.stepWith
  split
  · rfl
  · simp only [VmState.stepRefusingWith, libraryStepReruns, VmState.with_libraries_self st hr hm]

/-- Without `max_library_loads` (the compute phase sets it only when configuration parameter 43
does), `VmState.stepWith` is the step. -/
theorem VmState.stepWith_of_none (exec : Instr → VM Unit) (st : VmState) (h : st.maxLibraryLoads = none) :
    st.stepWith exec = st.stepOnceWith exec := by
  simp [VmState.stepWith, h]

/-- `VmState.stepOnceWith_ordinary` with the entry's gas check as a case. -/
theorem VmState.stepOnceWith_ordinary' (exec : Instr → VM Unit) (st : VmState) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs)
    (hcc : st.cc = .ordinary code saved cregs OrdCdata.empty) :
    st.stepOnceWith exec =
      if (st.applyCregsCdata cregs OrdCdata.empty).jumpRanOut then
        ((st.applyCregsCdata cregs OrdCdata.empty).countJump).outOfGasHalt
      else VmState.codeStep exec code (st.enter cregs (.ordinary code saved OrdCregs.empty OrdCdata.empty)) := by
  split
  · rename_i h
    unfold VmState.stepOnceWith
    rw [hcc]
    simp only [VmState.enteredCdata_empty, OrdCdata.empty_needsMoreArgs, Bool.false_eq_true, if_false]
    rw [VmState.ranOutEntering_self_gas _ _ (VmState.applyCregsCdata_gas _ _)]
    simp only [Bool.false_eq_true, if_false, h, if_true]
  · rename_i h
    exact VmState.stepOnceWith_ordinary exec st code saved cregs hcc (by simpa using h)

/-- `VmState.stepOnceWith_instr` with the entry's gas check as a case and the code's facts as the
equations a tactic proves by evaluation: the bits left (`b`, not zero), the global version the
opcode needs (`k`, reached), the decoded instruction. -/
theorem VmState.stepOnceWith_instr' (exec : Instr → VM Unit) (st : VmState) (code rest : Slice)
    (saved : Continuation) (cregs : OrdCregs) (i : Instr) (n b k : Nat)
    (hcc : st.cc = .ordinary code saved cregs OrdCdata.empty)
    (hcp : st.cp = 0)
    (hbits : code.bitsRemaining = b) (hb : b ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 = k) (hk : k ≤ st.globalVersion)
    (hdec : decodeCp0WithBits code = .ok (i, n, rest)) :
    st.stepOnceWith exec =
      if (st.applyCregsCdata cregs OrdCdata.empty).jumpRanOut then
        ((st.applyCregsCdata cregs OrdCdata.empty).countJump).outOfGasHalt
      else VmState.instrStep exec i ((st.enter cregs (.plain rest)).consumeGas (instrGas i n)) := by
  split
  · rw [VmState.stepOnceWith_ordinary' exec st code saved cregs hcc, if_pos (by assumption)]
  · rename_i h
    exact VmState.stepOnceWith_instr exec st code rest saved cregs i n hcc (by simpa using h) hcp
      (by rw [hbits]; exact hb) (by rw [hver]; exact hk) hdec

/-- `VmState.stepOnceWith_implicitRet` with the entry's gas check as a case. -/
theorem VmState.stepOnceWith_implicitRet' (exec : Instr → VM Unit) (st : VmState) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs)
    (hcc : st.cc = .ordinary code saved cregs OrdCdata.empty)
    (hbits : code.bitsRemaining = 0) (hrefs : code.refsRemaining = 0) :
    st.stepOnceWith exec =
      if (st.applyCregsCdata cregs OrdCdata.empty).jumpRanOut then
        ((st.applyCregsCdata cregs OrdCdata.empty).countJump).outOfGasHalt
      else VmState.retStep ((st.enter cregs (.ordinary code saved OrdCregs.empty OrdCdata.empty)).consumeGas
        implicitRetGasPrice) := by
  rw [VmState.stepOnceWith_ordinary' exec st code saved cregs hcc]
  simp only [VmState.codeStep, hbits, hrefs, beq_self_eq_true, if_true]

/-- `VmState.stepOnceWith_implicitJmpRef` with the entry's gas check as a case. -/
theorem VmState.stepOnceWith_implicitJmpRef' (exec : Instr → VM Unit) (st : VmState) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs) (r : Nat)
    (hcc : st.cc = .ordinary code saved cregs OrdCdata.empty)
    (hbits : code.bitsRemaining = 0) (hrefs : code.refsRemaining = r) (hr : r ≠ 0) :
    st.stepOnceWith exec =
      if (st.applyCregsCdata cregs OrdCdata.empty).jumpRanOut then
        ((st.applyCregsCdata cregs OrdCdata.empty).countJump).outOfGasHalt
      else VmState.jmpRefStep code ((st.enter cregs (.ordinary code saved OrdCregs.empty OrdCdata.empty)).consumeGas
        implicitJmpRefGasPrice) := by
  rw [VmState.stepOnceWith_ordinary' exec st code saved cregs hcc]
  have hrefs' : (code.refsRemaining == 0) = false := by simp [hrefs, hr]
  simp only [VmState.codeStep, hbits, hrefs', beq_self_eq_true, if_true, Bool.false_eq_true, if_false]

end TvmLean

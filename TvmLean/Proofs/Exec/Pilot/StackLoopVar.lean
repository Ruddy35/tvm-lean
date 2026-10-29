import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.StackVar
import TvmLean.Proofs.Exec.Spec.LoopBrk

/-!
# Pilots: `BLKSWX` and `AGAINBRK`

The specifications of `Proofs/Exec/Spec/StackVar.lean` and `LoopBrk.lean` used by `vm_run` (the
codes assembled by the model's assembler, `code_eq`):

* `BLKSWX` on `[a, b, c, 2, 1]`, any three values: `[c, a, b]`, exit code 0; on `[a, 2, 1]`
  stk_und (exit code 2) (`BlkSwapXPilot`);
* `AGAINBRK; PUSHINT 7` with the body `RETALT` on the stack: the body leaves the loop at once
  through `c1`, the code after the loop runs, `[7]`, exit code 0; on the empty stack stk_und
  (`AgainBrkPilot`).
-/

namespace TvmLean.Pilot

/-- The state that runs `code` on the stack `stk` with 1000 gas, `c0` the end of the run and `c2`
the exception handler of the compute phase; the rest of `st` is anything. -/
def stackLoopStart (code : Cell) (st : VmState) (stk : Stack) : VmState :=
  { st with stack := stk, cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

namespace BlkSwapXPilot

/-- The bits of `BLKSWX` (`0x63`). -/
def bits : BitString := #[false, true, true, false, false, false, true, true]

/-- The code `BLKSWX`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the instruction. -/
theorem code_eq : assembleCp0 [.blkSwapX] = .ok code := by decide

/-- **The top value moves below the two under it.** -/
theorem run_swap (fuel : Nat) (st : VmState) (a b c : Value) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
        (stackLoopStart code st (((((#[].push a).push b).push c).push (.int (.num 2))).push (.int (.num 1)))) =
          VmState.haltResult (~~~ 0) stF ∧
      stF.stack = ((#[].push c).push a).push b := by
  unfold stackLoopStart
  vm_run
  all_goals exact ⟨_, rfl, rfl⟩

/-- Three values asked of one: stk_und, the run halts with exit code `~~~2`. -/
theorem run_underflow (fuel : Nat) (st : VmState) (a : Value) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
      (stackLoopStart code st (((#[].push a).push (.int (.num 2))).push (.int (.num 1)))) = .halt (~~~ 2) stF := by
  unfold stackLoopStart
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end BlkSwapXPilot

namespace AgainBrkPilot

/-- The bits of `AGAINBRK` (`0xe31a`) and `PUSHINT 7` (`0x77`). -/
def bits : BitString :=
  #[true, true, true, false, false, false, true, true, false, false, false, true, true, false, true, false,
    false, true, true, true, false, true, true, true]

/-- The code `AGAINBRK; PUSHINT 7`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the two instructions. -/
theorem code_eq : assembleCp0 [.contExt (.again true), .pushInt (.num 7)] = .ok code := by decide

/-- The body `RETALT` (`0xdb31`): it returns through `c1`. -/
def body : Continuation :=
  .ordinary (Slice.ofCell (Cell.mkOrdinary
    #[true, true, false, true, true, false, true, true, false, false, true, true, false, false, false, true] #[]))
    (.quit 0) OrdCregs.empty OrdCdata.empty

/-- It is what the model's assembler makes of `RETALT`. -/
theorem body_eq : assembleCp0 [.retAlt] =
    .ok (Cell.mkOrdinary
      #[true, true, false, true, true, false, true, true, false, false, true, true, false, false, false, true] #[]) := by
  decide

/-- **A loop whose body breaks out at once**: the code after the loop runs, `[7]`. -/
theorem run_break (fuel : Nat) (st : VmState) :
    ∃ stF, VmState.runWith execInstr (fuel + 10) (stackLoopStart code st (#[].push (.cont body))) =
        VmState.haltResult (~~~ 0) stF ∧ stF.stack = #[].push (.int (.num 7)) := by
  unfold stackLoopStart body
  vm_run
  all_goals try (vm_has_run; vm_step)
  all_goals try vm_run
  all_goals exact ⟨_, rfl, rfl⟩

/-- No body on the stack: stk_und, the run halts with exit code `~~~2`. -/
theorem run_underflow (fuel : Nat) (st : VmState) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (stackLoopStart code st #[]) = .halt (~~~ 2) stF := by
  unfold stackLoopStart
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end AgainBrkPilot

end TvmLean.Pilot

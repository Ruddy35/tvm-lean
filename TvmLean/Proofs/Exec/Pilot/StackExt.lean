import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.StackExt

/-!
# Pilot: `2SWAP; 2OVER` on unknown values

The specifications of `Proofs/Exec/Spec/StackExt.lean` used by `vm_run`: the code `2SWAP; 2OVER`
(assembled by the model's assembler, `StackExtPilot.code_eq`) on the stack `[a, b, c, d]`, any
four values, halts with the stack `[c, d, a, b, c, d]` (`2SWAP` makes `c d a b`, `2OVER` pushes
`c d` again), exit code 0 (`StackExtPilot.run_swap_over`). A stack of three values is stack
underflow (exception 2, `StackExtPilot.run_short`).
-/

namespace TvmLean.Pilot.StackExtPilot

/-- The bits of `2SWAP` (`0x5a`) and `2OVER` (`0x5d`). -/
def bits : BitString :=
  #[false, true, false, true, true, false, true, false,
    false, true, false, true, true, true, false, true]

/-- The code `2SWAP; 2OVER`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the two instructions. -/
theorem code_eq : assembleCp0 [.twoSwap, .twoOver] = .ok code := by decide

/-- The state that runs `code` on the stack `stk` with 1000 gas, `c0` the end of the run and `c2`
the exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) (stk : Stack) : VmState :=
  { st with stack := stk, cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

/-- **`2SWAP; 2OVER` on four values.** On `[a, b, c, d]` the run halts with exit code `~~~0` and
the stack `[c, d, a, b, c, d]`. -/
theorem run_swap_over (fuel : Nat) (st : VmState) (a b c d : Value) :
    ∃ stF, VmState.runWith execInstr (fuel + 4)
        (start st ((((#[].push a).push b).push c).push d)) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = (((((#[].push c).push d).push a).push b).push c).push d := by
  unfold start
  vm_run
  exact ⟨_, rfl, rfl⟩

/-- On a stack of three values `2SWAP` underflows: the run halts with exit code `~~~2`. -/
theorem run_short (fuel : Nat) (st : VmState) (a b c : Value) :
    ∃ stF, VmState.runWith execInstr (fuel + 4) (start st (((#[].push a).push b).push c)) = .halt (~~~ 2) stF := by
  unfold start
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end TvmLean.Pilot.StackExtPilot

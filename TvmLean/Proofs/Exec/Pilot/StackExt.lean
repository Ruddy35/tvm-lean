import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.StackExt

/-!
# Pilot: `TUCK; -ROT; 2DROP` on unknown values

The specifications of `Proofs/Exec/Spec/StackExt.lean` used by `vm_run`: the code `TUCK; -ROT;
2DROP` (assembled by the model's assembler, `StackExtPilot.code_eq`) on the stack `[a, b]`, any
two values, halts with the stack `[b]` (`TUCK` makes `b a b`, `-ROT` `b b a`, `2DROP` leaves `b`),
exit code 0. A stack of one value is stack underflow (exception 2, `StackExtPilot.run_short`).
-/

namespace TvmLean.Pilot.StackExtPilot

/-- The bits of `TUCK` (`0x66`), `-ROT` (`0x59`) and `2DROP` (`0x5b`). -/
def bits : BitString :=
  #[false, true, true, false, false, true, true, false,
    false, true, false, true, true, false, false, true,
    false, true, false, true, true, false, true, true]

/-- The code `TUCK; -ROT; 2DROP`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the three instructions. -/
theorem code_eq : assembleCp0 [.tuck, .rotRev, .drop2] = .ok code := by decide

/-- The state that runs `code` on the stack `stk` with 1000 gas, `c0` the end of the run and `c2`
the exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) (stk : Stack) : VmState :=
  { st with stack := stk, cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

/-- **`TUCK; -ROT; 2DROP` drops the value below the top.** On `[a, b]` the run halts with exit code
`~~~0` and the stack `[b]`. -/
theorem run_nip (fuel : Nat) (st : VmState) (a b : Value) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st ((#[].push a).push b)) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = #[].push b := by
  unfold start
  vm_run
  exact ⟨_, rfl, rfl⟩

/-- On a stack of one value `TUCK` underflows: the run halts with exit code `~~~2`. -/
theorem run_short (fuel : Nat) (st : VmState) (a : Value) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st (#[].push a)) = .halt (~~~ 2) stF := by
  unfold start
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end TvmLean.Pilot.StackExtPilot

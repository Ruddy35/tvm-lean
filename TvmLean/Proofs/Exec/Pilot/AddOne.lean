import TvmLean.Proofs.Exec.Tactic

/-!
# Pilot: `PUSHINT 1; ADD` on an unknown integer

The smallest run of concrete code on a symbolic stack: the code `PUSHINT 1; ADD` (assembled by the
model's assembler, `AddOne.code_eq`) on the stack `[x]`, `x` any integer whose successor fits 257
bits, runs to its end (the implicit `RET` to `quit 0`) and halts with the stack `[x + 1]`, exit
code 0 (`~~~0`), whatever the rest of the state. Proved by `vm_run`; the case of an `x + 1` out of
range is `AddOne.run_overflow` (int_ov, exception 4).
-/

namespace TvmLean.Pilot.AddOne

/-- The bits of `PUSHINT 1` (`0x71`) and `ADD` (`0xa0`). -/
def bits : BitString :=
  #[false, true, true, true, false, false, false, true, true, false, true, false, false, false, false, false]

/-- The code `PUSHINT 1; ADD`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the two instructions. -/
theorem code_eq : assembleCp0 [.pushInt (.num 1), .add] = .ok code := by decide

/-- The state that runs `code` on the stack `[x]` with 1000 gas, `c0` the end of the run and `c2`
the exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) (x : Int) : VmState :=
  { st with stack := #[].push (.int (.num x)), cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

/-- **`PUSHINT 1; ADD` adds one.** When `x + 1` fits 257 bits, the run halts with exit code
`~~~0` and the stack `[x + 1]`. -/
theorem run_add_one (fuel : Nat) (st : VmState) (x : Int) (hx : -2 ^ 256 ≤ x + 1 ∧ x + 1 < 2 ^ 256) :
    ∃ stF, VmState.runWith execInstr (fuel + 4) (start st x) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = #[].push (.int (.num (x + 1))) := by
  unfold start
  vm_run
  exact ⟨_, rfl, rfl⟩

/-- When `x + 1` does not fit 257 bits, `ADD` raises int_ov: the run halts with exit code `~~~4`. -/
theorem run_overflow (fuel : Nat) (st : VmState) (x : Int) (hx : 2 ^ 256 ≤ x + 1) :
    ∃ stF, VmState.runWith execInstr (fuel + 4) (start st x) = .halt (~~~ 4) stF := by
  unfold start
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end TvmLean.Pilot.AddOne

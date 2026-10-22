import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.ArithExt

/-!
# Pilot: `MUL; PUSHINT 3; DIV` on unknown integers

The specifications of `Proofs/Exec/Spec/ArithExt.lean` used by `vm_run`: the code `MUL; PUSHINT 3;
DIV` (assembled by the model's assembler, `ArithExtPilot.code_eq`) on the stack `[x, y]`, `x` and
`y` any integers whose product fits 257 bits, halts with the stack `[⌊x * y / 3⌋]` (the quotient
of `divModRound` rounding down), exit code 0. The steps of `MUL` and `DIV` are `Spec.mul` and
`Spec.div` (the handler of `DIV` would leave the dividend `x * y + 0`); a product out of range is
int_ov (`ArithExtPilot.run_overflow`).
-/

namespace TvmLean.Pilot.ArithExtPilot

/-- The bits of `MUL` (`0xa8`), `PUSHINT 3` (`0x73`) and `DIV` (`0xa904`). -/
def bits : BitString :=
  #[true, false, true, false, true, false, false, false,
    false, true, true, true, false, false, true, true,
    true, false, true, false, true, false, false, true, false, false, false, false, false, true, false, false]

/-- The code `MUL; PUSHINT 3; DIV`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the three instructions. -/
theorem code_eq : assembleCp0 [.mul, .pushInt (.num 3), .divMod 1 (-1) false false] = .ok code := by decide

/-- The state that runs `code` on the stack `[x, y]` with 1000 gas, `c0` the end of the run and
`c2` the exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) (x y : Int) : VmState :=
  { st with stack := (#[].push (.int (.num x))).push (.int (.num y)),
            cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

/-- **`MUL; PUSHINT 3; DIV` divides the product by 3, rounding down.** When `x * y` fits 257 bits,
the run halts with exit code `~~~0` and the stack `[(divModRound (x * y) 3 (-1)).1]`. -/
theorem run_muldiv (fuel : Nat) (st : VmState) (x y : Int) (hxy : -2 ^ 256 ≤ x * y ∧ x * y < 2 ^ 256)
    (hq : -2 ^ 256 ≤ (divModRound (x * y) 3 (-1)).1 ∧ (divModRound (x * y) 3 (-1)).1 < 2 ^ 256) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st x y) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = #[].push (.int (.num (divModRound (x * y) 3 (-1)).1)) := by
  unfold start
  vm_run
  exact ⟨_, rfl, rfl⟩

/-- When `x * y` does not fit 257 bits, `MUL` raises int_ov: the run halts with exit code `~~~4`. -/
theorem run_overflow (fuel : Nat) (st : VmState) (x y : Int) (hxy : 2 ^ 256 ≤ x * y) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st x y) = .halt (~~~ 4) stF := by
  unfold start
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end TvmLean.Pilot.ArithExtPilot

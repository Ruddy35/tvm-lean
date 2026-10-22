import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.CellExt

/-!
# Pilot: `NEWC; 8 STI; BBITS` on an unknown integer

The specifications of `Proofs/Exec/Spec/CellExt.lean` used by `vm_run`: the code `NEWC; 8 STI;
BBITS` (assembled by the model's assembler, `CellExtPilot.code_eq`) on the stack `[x]`: an
integer that fits 8 bits signed is stored in a new builder, which then has 8 bits; the run halts
with the stack `[8]`, exit code 0 (`CellExtPilot.run_store`). Out of range, `STI` raises range_chk
(exception 5, `CellExtPilot.run_range`).
-/

namespace TvmLean.Pilot.CellExtPilot

/-- The bits of `NEWC` (`0xc8`), `8 STI` (`0xca07`) and `BBITS` (`0xcf31`). -/
def bits : BitString :=
  #[true, true, false, false, true, false, false, false,
    true, true, false, false, true, false, true, false, false, false, false, false, false, true, true, true,
    true, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true]

/-- The code `NEWC; 8 STI; BBITS`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the three instructions. -/
theorem code_eq : assembleCp0 [.newc, .sti 8, .bbits] = .ok code := by decide

/-- The state that runs `code` on the stack `[x]` with 1000 gas, `c0` the end of the run and `c2`
the exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) (x : Int) : VmState :=
  { st with stack := #[].push (.int (.num x)), cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

/-- The 8-bit two's complement of an integer has 8 bits. -/
theorem twosBits_size (x : Int) (n : Nat) : (twosBits x n).size = n := by
  simp [twosBits, natToBits]

/-- **A byte stored in a new builder takes 8 bits.** For `-128 ≤ x < 128` the run halts with exit
code `~~~0` and the stack `[8]`. -/
theorem run_store (fuel : Nat) (st : VmState) (x : Int) (hx : -128 ≤ x ∧ x < 128) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st x) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = #[].push (.int (.num 8)) := by
  unfold start
  vm_run [Builder.canExtendBy, Builder.storeBits, Builder.empty, twosBits_size]
  exact ⟨_, rfl, rfl⟩

/-- For `x ≥ 128`, `STI` raises range_chk: the run halts with exit code `~~~5`. -/
theorem run_range (fuel : Nat) (st : VmState) (x : Int) (hx : 128 ≤ x) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st x) = .halt (~~~ 5) stF := by
  unfold start
  vm_run [Builder.canExtendBy, Builder.empty]
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end TvmLean.Pilot.CellExtPilot

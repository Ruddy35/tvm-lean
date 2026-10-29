import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.ArithShift
import TvmLean.Proofs.Exec.Spec.ArithShiftMod
import TvmLean.Proofs.Exec.Spec.ArithMulShift
import TvmLean.Proofs.Exec.Spec.ArithShlDiv

/-!
# Pilots: `MODPOW2`, `RSHIFTMOD`, `MULRSHIFT`, `LSHIFT#DIV` on unknown integers

The specifications of `Proofs/Exec/Spec/ArithShift.lean`, `ArithShiftMod.lean`,
`ArithMulShift.lean` and `ArithShlDiv.lean` used by `vm_run`, each instruction alone (assembled by the model's assembler,
`code_eq`) on unknown integers, rounding down, its result the operation of `Int`
(`rshiftPow2Round_floor`, `modPow2Round_floor`, `divModRound_floor`), exit code 0; and an error:

* `MODPOW2` on `[x, 4]`: `[x % 16]`; on `[x, 257]` range_chk (exit code 5) (`ModPow2Pilot`);
* `RSHIFTMOD` on `[x, 3]`: `[x / 8, x % 8]` for an `x` of 257 bits; on `[x, 300]` range_chk (exit
  code 5) at any global version (`ShrModPilot`);
* `MULRSHIFT` on `[x, y, 4]`: `[x * y / 16]`; on `[x, y, -1]` range_chk (`MulShrPilot`);
* `LSHIFT#DIV 2` on `[x, 3]`: `[x * 4 / 3]`; on `[x, 0]` int_ov (exit code 4) (`ShlDivPilot`).
-/

namespace TvmLean.Pilot

open TvmLean.Spec

/-- The state that runs `code` on the stack `stk` with 1000 gas, `c0` the end of the run and `c2`
the exception handler of the compute phase; the rest of `st` is anything. -/
def arithStart (code : Cell) (st : VmState) (stk : Stack) : VmState :=
  { st with stack := stk, cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

namespace ModPow2Pilot

/-- The bits of `MODPOW2` (`0xa928`). -/
def bits : BitString :=
  #[true, false, true, false, true, false, false, true, false, false, true, false, true, false, false, false]

/-- The code `MODPOW2`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the instruction. -/
theorem code_eq : assembleCp0 [.arithExt (.shrMod false false 2 (-1) false none)] = .ok code := by decide

/-- **`MODPOW2` by 4: the remainder by 16.** -/
theorem run_modpow2 (fuel : Nat) (st : VmState) (x : Int) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
        (arithStart code st ((#[].push (.int (.num x))).push (.int (.num 4)))) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = #[].push (.int (.num (x % 16))) := by
  unfold arithStart
  vm_run [modPow2Round_floor]
  all_goals exact ⟨_, rfl, rfl⟩

/-- A shift of 257 bits is range_chk: the run halts with exit code `~~~5`. -/
theorem run_range (fuel : Nat) (st : VmState) (x : Int) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
      (arithStart code st ((#[].push (.int (.num x))).push (.int (.num 257)))) = .halt (~~~ 5) stF := by
  unfold arithStart
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end ModPow2Pilot

namespace ShrModPilot

/-- The bits of `RSHIFTMOD` (`0xa92c`). -/
def bits : BitString :=
  #[true, false, true, false, true, false, false, true, false, false, true, false, true, true, false, false]

/-- The code `RSHIFTMOD`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the instruction. -/
theorem code_eq : assembleCp0 [.arithExt (.shrMod false false 3 (-1) false none)] = .ok code := by decide

/-- **`RSHIFTMOD` by 3: the quotient and the remainder by 8.** -/
theorem run_shrmod (fuel : Nat) (st : VmState) (x : Int) (hx : -2 ^ 256 ≤ x ∧ x < 2 ^ 256) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
        (arithStart code st ((#[].push (.int (.num x))).push (.int (.num 3)))) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = (#[].push (.int (.num (x / 8)))).push (.int (.num (x % 8))) := by
  unfold arithStart
  vm_run [rshiftPow2Round_floor, modPow2Round_floor]
  all_goals exact ⟨_, rfl, rfl⟩

/-- A shift of 300 bits is range_chk: the run halts with exit code `~~~5`. -/
theorem run_range (fuel : Nat) (st : VmState) (x : Int) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
      (arithStart code st ((#[].push (.int (.num x))).push (.int (.num 300)))) = .halt (~~~ 5) stF := by
  unfold arithStart
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end ShrModPilot

namespace MulShrPilot

/-- The bits of `MULRSHIFT` (`0xa9a4`). -/
def bits : BitString :=
  #[true, false, true, false, true, false, false, true, true, false, true, false, false, true, false, false]

/-- The code `MULRSHIFT`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the instruction. -/
theorem code_eq : assembleCp0 [.arithExt (.shrMod true false 1 (-1) false none)] = .ok code := by decide

/-- **`MULRSHIFT` by 4: the product divided by 16.** -/
theorem run_mulshr (fuel : Nat) (st : VmState) (x y : Int) (hq : -2 ^ 256 ≤ x * y / 16 ∧ x * y / 16 < 2 ^ 256) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
        (arithStart code st (((#[].push (.int (.num x))).push (.int (.num y))).push (.int (.num 4)))) =
          VmState.haltResult (~~~ 0) stF ∧
      stF.stack = #[].push (.int (.num (x * y / 16))) := by
  unfold arithStart
  vm_run [rshiftPow2Round_floor]
  all_goals exact ⟨_, rfl, rfl⟩

/-- A negative shift is range_chk: the run halts with exit code `~~~5`. -/
theorem run_range (fuel : Nat) (st : VmState) (x y : Int) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
      (arithStart code st (((#[].push (.int (.num x))).push (.int (.num y))).push (.int (.num (-1))))) =
        .halt (~~~ 5) stF := by
  unfold arithStart
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end MulShrPilot

namespace ShlDivPilot

/-- The bits of `LSHIFT#DIV 2` (`0xa9d401`). -/
def bits : BitString :=
  #[true, false, true, false, true, false, false, true, true, true, false, true, false, true, false, false,
    false, false, false, false, false, false, false, true]

/-- The code `LSHIFT#DIV 2`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the instruction. -/
theorem code_eq : assembleCp0 [.arithExt (.shlDivMod 1 (-1) false false (some 2))] = .ok code := by decide

/-- **`LSHIFT#DIV 2` by 3: `x * 4 / 3`.** -/
theorem run_shldiv (fuel : Nat) (st : VmState) (x : Int) (hq : -2 ^ 256 ≤ x * 4 / 3 ∧ x * 4 / 3 < 2 ^ 256) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
        (arithStart code st ((#[].push (.int (.num x))).push (.int (.num 3)))) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = #[].push (.int (.num (x * 4 / 3))) := by
  unfold arithStart
  vm_run [divModRound_floor]
  all_goals exact ⟨_, rfl, rfl⟩

/-- A zero divisor is int_ov: the run halts with exit code `~~~4`. -/
theorem run_zero (fuel : Nat) (st : VmState) (x : Int) :
    ∃ stF, VmState.runWith execInstr (fuel + 5)
      (arithStart code st ((#[].push (.int (.num x))).push (.int (.num 0)))) = .halt (~~~ 4) stF := by
  unfold arithStart
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end ShlDivPilot

end TvmLean.Pilot

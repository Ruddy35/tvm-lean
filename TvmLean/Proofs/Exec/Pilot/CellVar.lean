import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.CellCheck
import TvmLean.Proofs.Exec.Spec.CellIntVar
import TvmLean.Proofs.Exec.Spec.CellSize

/-!
# Pilots: `BCHKBITS`, `STUX`, `CDATASIZE` with their arguments on the stack

The specifications of `Proofs/Exec/Spec/CellCheck.lean`, `CellIntVar.lean` and `CellSize.lean`
used by `vm_run` (the codes assembled by the model's assembler, `code_eq`), on an unknown integer
`x` or a known count, exit code 0, and an error:

* `NEWC; SWAP; BCHKBITS` on `[10]`: a new builder has room for 10 bits, the stack ends empty; on
  `[1024]` range_chk (exit code 5) (`BchkPilot`);
* `NEWC; PUSHINT 8; STUX; BBITS` on `[x]`, `0 ≤ x < 256`: the builder has 8 bits, `[8]`; for
  `x ≥ 256` range_chk (`StuxPilot`);
* `PUSHNULL; SWAP; CDATASIZE` on `[5]`: `[0, 0, 0]`; on `[-1]` range_chk (`CdataSizePilot`).
-/

namespace TvmLean.Pilot

open TvmLean.Spec

/-- The state that runs `code` on the stack `stk` with 1000 gas, `c0` the end of the run and `c2`
the exception handler of the compute phase; the rest of `st` is anything. -/
def cellStart (code : Cell) (st : VmState) (stk : Stack) : VmState :=
  { st with stack := stk, cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

namespace BchkPilot

/-- The bits of `NEWC` (`0xc8`), `SWAP` (`0x01`) and `BCHKBITS` (`0xcf39`). -/
def bits : BitString :=
  #[true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, true,
    true, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true]

/-- The code `NEWC; SWAP; BCHKBITS`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the three instructions. -/
theorem code_eq : assembleCp0 [.newc, .xchg0 1, .cellOp (.bchk true false false)] = .ok code := by decide

/-- **A new builder has room for 10 bits**: the check passes, the stack ends empty. -/
theorem run_room (fuel : Nat) (st : VmState) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (cellStart code st (#[].push (.int (.num 10)))) =
        VmState.haltResult (~~~ 0) stF ∧ stF.stack = #[] := by
  unfold cellStart
  vm_run [Builder.canExtendBy, Builder.empty]
  exact ⟨_, rfl, rfl⟩

/-- A count of 1024 bits is range_chk: the run halts with exit code `~~~5`. -/
theorem run_range (fuel : Nat) (st : VmState) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (cellStart code st (#[].push (.int (.num 1024)))) =
      .halt (~~~ 5) stF := by
  unfold cellStart
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end BchkPilot

namespace StuxPilot

/-- The bits of `NEWC` (`0xc8`), `PUSHINT 8` (`0x78`), `STUX` (`0xcf01`) and `BBITS` (`0xcf31`). -/
def bits : BitString :=
  #[true, true, false, false, true, false, false, false, false, true, true, true, true, false, false, false,
    true, true, false, false, true, true, true, true, false, false, false, false, false, false, false, true,
    true, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true]

/-- The code `NEWC; PUSHINT 8; STUX; BBITS`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the four instructions. -/
theorem code_eq : assembleCp0 [.newc, .pushInt (.num 8), .stIntVar true false false, .bbits] = .ok code := by
  decide

/-- **A byte stored with its width from the stack takes 8 bits.** -/
theorem run_store (fuel : Nat) (st : VmState) (x : Int) (hx : 0 ≤ x ∧ x < 256) :
    ∃ stF, VmState.runWith execInstr (fuel + 10) (cellStart code st (#[].push (.int (.num x)))) =
        VmState.haltResult (~~~ 0) stF ∧ stF.stack = #[].push (.int (.num 8)) := by
  unfold cellStart
  vm_run [Builder.canExtendBy, Builder.empty]
  exact ⟨_, rfl, by simp [Builder.storeBits, natToBits_size]⟩

/-- For `x ≥ 256`, `STUX` with 8 bits raises range_chk: the run halts with exit code `~~~5`. -/
theorem run_range (fuel : Nat) (st : VmState) (x : Int) (hx : 256 ≤ x) :
    ∃ stF, VmState.runWith execInstr (fuel + 10) (cellStart code st (#[].push (.int (.num x)))) =
      .halt (~~~ 5) stF := by
  unfold cellStart
  vm_run [Builder.canExtendBy, Builder.empty]
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end StuxPilot

namespace CdataSizePilot

/-- The bits of `PUSHNULL` (`0x6d`), `SWAP` (`0x01`) and `CDATASIZE` (`0xf941`). -/
def bits : BitString :=
  #[false, true, true, false, true, true, false, true, false, false, false, false, false, false, false, true,
    true, true, true, true, true, false, false, true, false, true, false, false, false, false, false, true]

/-- The code `PUSHNULL; SWAP; CDATASIZE`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the three instructions. -/
theorem code_eq : assembleCp0 [.pushNull, .xchg0 1, .cellExt (.cdataSize false)] = .ok code := by decide

/-- **Null has no cells, bits or references**: `[0, 0, 0]`. -/
theorem run_null (fuel : Nat) (st : VmState) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (cellStart code st (#[].push (.int (.num 5)))) =
        VmState.haltResult (~~~ 0) stF ∧
      stF.stack = ((#[].push (.int (.num 0))).push (.int (.num 0))).push (.int (.num 0)) := by
  unfold cellStart
  vm_run
  exact ⟨_, rfl, rfl⟩

/-- A negative bound is range_chk: the run halts with exit code `~~~5`. -/
theorem run_range (fuel : Nat) (st : VmState) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (cellStart code st (#[].push (.int (.num (-1))))) =
      .halt (~~~ 5) stF := by
  unfold cellStart
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end CdataSizePilot

end TvmLean.Pilot

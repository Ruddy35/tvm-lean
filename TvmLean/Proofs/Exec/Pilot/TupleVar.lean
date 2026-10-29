import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.TupleVar

/-!
# Pilot: `UNPACKFIRSTVAR` on a tuple of unknown values

The specifications of `Proofs/Exec/Spec/TupleVar.lean` used by `vm_run`: `UNPACKFIRSTVAR`
(assembled by the model's assembler, `TupleVarPilot.code_eq`) on the stack `[(a, b, c), 2]`, any
three values, halts with the stack `[a, b]` (charged 2 gas for the entries), exit code 0
(`TupleVarPilot.run_unpack`); asked for 4 entries of the triple it raises type_chk (exception 7,
`TupleVarPilot.run_short`).
-/

namespace TvmLean.Pilot.TupleVarPilot

/-- The bits of `UNPACKFIRSTVAR` (`0x6f83`). -/
def bits : BitString :=
  #[false, true, true, false, true, true, true, true, true, false, false, false, false, false, true, true]

/-- The code `UNPACKFIRSTVAR`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the instruction. -/
theorem code_eq : assembleCp0 [.tupleOp .unpackFirstVar] = .ok code := by decide

/-- The state that runs `code` on the stack `[(a, b, c), n]` with 1000 gas, `c0` the end of the run
and `c2` the exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) (a b c : Value) (n : Int) : VmState :=
  { st with stack := (#[].push (.tuple #[a, b, c])).push (.int (.num n)),
            cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

/-- **The first two entries of a triple.** -/
theorem run_unpack (fuel : Nat) (st : VmState) (a b c : Value) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st a b c 2) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = (#[].push a).push b := by
  unfold start
  vm_run [tupleEntryGasPrice]
  exact ⟨_, rfl, rfl⟩

/-- Four entries of a triple: type_chk, the run halts with exit code `~~~7`. -/
theorem run_short (fuel : Nat) (st : VmState) (a b c : Value) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st a b c 4) = .halt (~~~ 7) stF := by
  unfold start
  vm_run
  all_goals (first | (exfalso; omega) | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩))

end TvmLean.Pilot.TupleVarPilot

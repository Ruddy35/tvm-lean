import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.Tuple

/-!
# Pilot: `PAIR; SECOND; ISNULL` on unknown values

The specifications of `Proofs/Exec/Spec/Tuple.lean` used by `vm_run`: the code `TUPLE 2; INDEX 1;
ISNULL` (assembled by the model's assembler, `TuplePilot.code_eq`) on the stack `[a, b]`, any two
values: `TUPLE 2` makes the pair (charged 2 gas), `INDEX 1` takes back `b`, `ISNULL` tests it; the
run halts with the stack `[-1]` if `b` is null (`TuplePilot.run_null`) and `[0]` otherwise
(`TuplePilot.run_not_null`), exit code 0.
-/

namespace TvmLean.Pilot.TuplePilot

/-- The bits of `TUPLE 2` (`0x6f02`), `INDEX 1` (`0x6f11`) and `ISNULL` (`0x6e`). -/
def bits : BitString :=
  #[false, true, true, false, true, true, true, true, false, false, false, false, false, false, true, false,
    false, true, true, false, true, true, true, true, false, false, false, true, false, false, false, true,
    false, true, true, false, true, true, true, false]

/-- The code `TUPLE 2; INDEX 1; ISNULL`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the three instructions. -/
theorem code_eq : assembleCp0 [.tupleOp (.mktuple 2), .tupleOp (.index 1), .isNull] = .ok code := by decide

/-- The state that runs `code` on the stack `[a, b]` with 1000 gas, `c0` the end of the run and
`c2` the exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) (a b : Value) : VmState :=
  { st with stack := (#[].push a).push b, cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

/-- **The second of a pair is tested for null.** For a null `b` the run halts with exit code `~~~0`
and the stack `[-1]`. -/
theorem run_null (fuel : Nat) (st : VmState) (a : Value) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st a .null) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = #[].push (.int (.num (-1))) := by
  unfold start
  vm_run [tupleEntryGasPrice]
  exact ⟨_, rfl, rfl⟩

/-- For an integer `b` the stack at the end is `[0]`. -/
theorem run_not_null (fuel : Nat) (st : VmState) (a : Value) (n : IntVal) :
    ∃ stF, VmState.runWith execInstr (fuel + 5) (start st a (.int n)) = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = #[].push (.int (.num 0)) := by
  unfold start
  vm_run [tupleEntryGasPrice]
  exact ⟨_, rfl, rfl⟩

end TvmLean.Pilot.TuplePilot

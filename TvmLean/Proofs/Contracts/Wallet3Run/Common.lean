import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Contracts.Wallet3Code
import TvmLean.Proofs.Contracts.Wallet3Spec
import TvmLean.Semantics.Contract
import TvmLean.Proofs.Fast.Run
import TvmLean.Proofs.Contracts.Wallet3Run.Tactic

/-!
# Wallet v3 from every state the compute phase starts from: the statements

The runs of `wallet3Code` that `TvmLean/Proofs/Contracts/Wallet3Induction.lean` needs, stated on
`start`: the state of `TvmLean.Tx.VmStart` (the compute phase's `computePhaseInit` of the code,
`c7 = #[c7]`, any gas limits `gl gm gc`, global version `gv`, libraries, `max_data_depth` and
`max_library_loads`), with any set of loaded cells `lc` (the compute phase starts with none; with
`lc` unknown the gas of every load stays a term the kernel cannot evaluate, see
`Wallet3Run/External.lean`).

* `ExtSpec`: a run of an external message (selector -1) that commits leaves `c4` the stored data
  with the seqno increased by one (`dataOf`, as `recv_external` reads it) and an action list of
  `SENDRAWMSG` actions only (`SendList`);
* `IntSpec`: a run of an internal message (selector 0) that commits leaves the data and the empty
  action list;
* a run of tick-tock (selector -2) never commits.

The tactics `ext_no_commit` and `ext_commit` close the goals `vm_run` leaves at the end of the paths
of a run (`VmState.haltResult`, `VmState.runWith_zero`).
-/

/-! ## The closed facts of the code, over the fast twins

With the option `vm.fastFacts` (`TvmLean/Proofs/Exec/Tactic.lean`) the facts of the code a run rests
on (the bits left, the opcode's version, the decoded instruction, the dictionary lookups) are proved
by kernel evaluation over the fast twins (`TvmLean/Proofs/Fast/`). Their twins are made here, once:
a theorem elaborated in parallel may not add them. -/

set_option Elab.async false in
fast_twin TvmLean.Slice.bitsRemaining TvmLean.Slice.refsRemaining TvmLean.Slice.opcode24
  TvmLean.cp0RequiredVersion TvmLean.decodeCp0WithBits TvmLean.dictKeyBits? TvmLean.dictLookupLoads
  TvmLean.Contracts.wallet3Code

namespace TvmLean.Contracts.Wallet3.Run

/-- The data as `recv_external` reads it (`32 LDU`, `32 LDU`, `256 LDU` from `c4`), as
`TvmLean.Pilot.Wallet3.dataOf` (`TvmLean/Proofs/Exec/Pilot/Wallet3.lean`). -/
def dataOf (data : Cell) : Wallet3.Data :=
  ⟨bitsToNat (data.bits.extract 0 32), bitsToNat (data.bits.extract 32 64), bitsToNat (data.bits.extract 64 320)⟩

/-- The fields `recv_external` reads from a cell that decodes (`Wallet3.Data.decode`) are the decoded
data. -/
theorem dataOf_of_decode {data : Cell} {d : Wallet3.Data} (hd : Wallet3.Data.decode data = some d) :
    dataOf data = d := by
  unfold Wallet3.Data.decode at hd
  split at hd
  · cases hd
    rfl
  · cases hd

theorem int_toNat_natCast_add_one (x : Nat) : ((x : Int) + 1).toNat = x + 1 := by omega

/-- The state the compute phase starts `wallet3Code` from (`TvmLean.Tx.VmStart`, the code loaded as
itself), with the loaded cells `lc`. -/
def start (data : Cell) (stack : Stack) (c7 : Value) (gl gm gc : Int) (gv : Nat) (libs : Array Cell)
    (mdd : Nat) (mll : Option Nat) (lc : Array (Array UInt8)) : VmState :=
  { computePhaseInit wallet3Code data stack #[c7] gl gm gc gv with
    libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll, loadedCells := lc }

/-- What a committed run of `recv_external` leaves: the data with the seqno increased by one (the
fields as `recv_external` reads them, `dataOf`), and `SENDRAWMSG` actions only. -/
def ExtSpec (data : Cell) (r : StepResult) : Prop :=
  r.state.cstate.committed = true →
    r.state.cstate.c4 = Wallet3.Data.encode { dataOf data with seqno := (dataOf data).seqno + 1 } ∧
      SendList r.state.cstate.c5

/-- What a committed run of `recv_internal` leaves: the data and no action. -/
def IntSpec (data : Cell) (r : StepResult) : Prop :=
  r.state.cstate.committed = true → r.state.cstate.c4 = data ∧ r.state.cstate.c5 = Cell.empty

/-- `vm_run` with the lemmas of a run from `start`: the dispatch (`Spec.dictJump`), the bounds of
slices, the step whatever `max_library_loads` is (`VmState.stepWith_finish`), `ACCEPT` for any gas
maximum, and the facts `args`. -/
syntax "wallet_run" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| wallet_run [$args,*]) => `(tactic| vm_run [Spec.dictJump, Slice.haveBits, Slice.advanceBits,
      ↓ VmState.stepWith_finish, VmState.stepFinish_continue, VmState.stepFinish_halt, VmState.stepFinish_ite,
      VmState.stepFinish_dite, GasLimits.changeLimit_infty_min, $args,*])

/-- `wallet_run` that stops where the code at bit `n` is about to run (`vm_not_at_pos`): the goals
there are left (to a lemma about the runs from that point). -/
syntax "wallet_run_to " num " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| wallet_run_to $n [$args,*]) => `(tactic| set_option maxRecDepth 100000 in repeat' (first
      | (vm_split <;> try vm_prune_cheap)
      | (vm_not_at_loop_head; vm_not_at_pos $n; vm_step [Spec.dictJump, Slice.haveBits, Slice.advanceBits,
          ↓ VmState.stepWith_finish, VmState.stepFinish_continue, VmState.stepFinish_halt,
          VmState.stepFinish_ite, VmState.stepFinish_dite, GasLimits.changeLimit_infty_min, $args,*])
      | (vm_not_at_loop_head; vm_not_at_pos $n; vm_fuel <;> try simp only [VmState.runWith_zero, Excno.toInt])
      | (vm_has_run; vm_step_simp [Spec.dictJump, Slice.haveBits, Slice.advanceBits,
          ↓ VmState.stepWith_finish, VmState.stepFinish_continue, VmState.stepFinish_halt,
          VmState.stepFinish_ite, VmState.stepFinish_dite, GasLimits.changeLimit_infty_min, $args,*])
      | vm_loop_close))

/-- `vm_step` with the lemmas of `wallet_run`. -/
syntax "wallet_step" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| wallet_step [$args,*]) => `(tactic| vm_step [Spec.dictJump, Slice.haveBits, Slice.advanceBits,
      ↓ VmState.stepWith_finish, VmState.stepFinish_continue, VmState.stepFinish_halt, VmState.stepFinish_ite,
      VmState.stepFinish_dite, GasLimits.changeLimit_infty_min, $args,*])

/-- A path that does not commit: its result keeps the empty committed state. -/
macro "ext_no_commit" : tactic => `(tactic| (
  simp only [ExtSpec, IntSpec, VmState.haltResult, VmState.runWith_zero, Excno.toInt, Int.reduceEq,
    Int.reduceNeg, or_self, or_false, false_or, if_false, ite_false, StepResult.state_halt,
    CommittedState.empty, Bool.false_eq_true, false_implies, not_false_eq_true]; done))

/-- The path of `recv_external` that commits: the data built by `NEWC 32 STU 32 STU 256 STU ENDC`
is `encode` of the stored fields with the seqno increased, the action list is that of the loop
(`vm_c5_close`). -/
macro "ext_commit" : tactic => `(tactic| (
  unfold ExtSpec VmState.haltResult VmState.tryCommit
  simp only [Int.reduceEq, or_false, if_true]
  split
  · intro _
    try clear ih
    simp only [StepResult.state_halt, if_true]
    refine ⟨?_, by vm_c5_close⟩
    simp only [Wallet3.Data.encode, dataOf, Builder.finalize, Builder.storeBits, Builder.empty,
      int_toNat_natCast_add_one, Array.empty_append, Array.append_assoc, Slice.readBits, Slice.ofCell,
      Nat.zero_add, Nat.reduceAdd]
  · ext_no_commit))

/-- The path of `recv_internal` that commits: the data and the action list are those it started
with. -/
macro "int_commit" : tactic => `(tactic| (
  unfold IntSpec VmState.haltResult VmState.tryCommit
  simp only [Int.reduceEq, or_false, or_true, if_true]
  split
  · intro _
    simp only [StepResult.state_halt, if_true]
    constructor <;> first | rfl | trivial
  · ext_no_commit))

end TvmLean.Contracts.Wallet3.Run

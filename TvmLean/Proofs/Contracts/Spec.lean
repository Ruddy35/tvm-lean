import TvmLean.Semantics.Contract

/-!
# Contract specifications

The format in which a contract's correctness is stated, the same for every contract: a contract
supplies a `ContractSpec` (how its persistent data `c4` decodes, the invariant on the decoded data,
what one compute phase may do to it, and what an external message must satisfy to be accepted), and
`ContractSpec.Holds S code` is the statement that the bytecode `code` meets it. Wallet v3
(`TvmLean/Proofs/Contracts/Wallet3Spec.lean`) is the first instance.

Everything is stated over the compute phase as the transaction model runs it
(`TvmLean/Semantics/Contract.lean`, `Tx.runVm`): the initial state is `computePhaseInit` of the code,
the data and the stack of `computePhaseStack` (or of a tick-tock transaction), the run is
`VmState.run`, and what persists is `ComputeOutcome.ofHalt` (only a committed state survives).
`ComputeInput` holds everything else the VM is given, so the statements quantify over every
message, environment (`c7`), gas limits and global version the transaction can produce
(`ComputeInput.Valid`: what C++ `Transaction::prepare_compute_phase` guarantees of them).

For the induction over transactions (`TvmLean/Proofs/Tx/`) this is the step: a transaction either
does not run the compute phase, or runs it on such an input and keeps `ComputeRun.outcome`'s `c4`
only if the action phase succeeds. Either way the new data is the old one or the outcome's: the
invariant holds of both, and the data either did not change or changed by `Step` (a run that does
not commit keeps the old data, `ComputeRun.outcome_c4_of_not_committed`).
-/

namespace TvmLean.Contracts

open TvmLean

/-- What starts the compute phase (C++ `Transaction::prepare_vm_stack`). -/
inductive ComputeTrigger where
  /-- An inbound message: the value it carries (`msg_balance_remaining`), the message cell, its
  body, and whether it is external. -/
  | message (msgValue : Int) (msg : Cell) (body : Slice) (isExternal : Bool)
  /-- A tick or tock transaction of a special account at address `addr` (as an integer). -/
  | tickTock (addr : Int) (isTock : Bool)

/-- Everything the VM of the compute phase is given besides the code and the data: the account's
balance, the trigger, register `c7`, the gas limits (`gasCredit` nonzero only for an external
message), the global version and the settings `Tx.runVm` adds (libraries, data depth, library
loads). -/
structure ComputeInput where
  balance : Int
  trigger : ComputeTrigger
  c7 : Array Value
  gasLimit : Int
  gasMax : Int
  gasCredit : Int
  globalVersion : Nat
  libraries : Array Cell := #[]
  maxDataDepth : Nat := 512
  maxLibraryLoads : Option Nat := none

namespace ComputeInput

/-- The initial stack (`Tx.runVm`): `computePhaseStack` for a message; balance, address, tock flag
and `-2` for tick-tock. -/
def stack (i : ComputeInput) : Stack :=
  match i.trigger with
  | .message v m b e => computePhaseStack i.balance v m b e
  | .tickTock a tock => #[.int (.num i.balance), .int (.num a), .int (.num (if tock then -1 else 0)), .int (.num (-2))]

/-- The initial VM state of the compute phase of `code` on `data`, as `Tx.runVm` builds it. -/
def init (i : ComputeInput) (code data : Cell) : VmState :=
  { computePhaseInit code data i.stack i.c7 i.gasLimit i.gasMax i.gasCredit i.globalVersion with
      libraries := i.libraries, maxDataDepth := i.maxDataDepth, maxLibraryLoads := i.maxLibraryLoads }

/-- An external inbound message. -/
def isExternal (i : ComputeInput) : Bool :=
  match i.trigger with
  | .message _ _ _ e => e
  | .tickTock _ _ => false

/-- The body of the inbound message (`none` for tick-tock). -/
def body? (i : ComputeInput) : Option Slice :=
  match i.trigger with
  | .message _ _ b _ => some b
  | .tickTock _ _ => none

/-- `NOW` as the contract reads it: entry 3 of the tuple `c7[0]`, an integer. -/
def now? (i : ComputeInput) : Option Int :=
  match (i.c7[0]? : Option Value) with
  | some (.tuple p) =>
      match (p[3]? : Option Value) with
      | some (.int (.num n)) => some n
      | _ => none
  | _ => none

/-- What C++ guarantees of a compute phase it runs (`Transaction::compute_gas_limits`,
`prepare_compute_phase`): nonnegative gas limits, a gas credit exactly for an external message
(where it is nonzero: with neither limit nor credit the phase is skipped). Without it an external
message would count as accepted from the start. -/
def Valid (i : ComputeInput) : Prop :=
  0 ≤ i.gasLimit ∧ 0 ≤ i.gasCredit ∧ (i.isExternal = true ↔ 0 < i.gasCredit)

end ComputeInput

/-- A compute phase that halted: its input, the data `c4` it started with, the exit code of
`VmState.run` and the final VM state. -/
structure ComputeRun where
  input : ComputeInput
  data : Cell
  exitCode : Int
  final : VmState

namespace ComputeRun

/-- `r` is a run of `code`: the VM of `r.input.init code r.data` halts in `r.final` with
`r.exitCode` within some number of steps. -/
def Of (code : Cell) (r : ComputeRun) : Prop :=
  ∃ fuel, VmState.run fuel (r.input.init code r.data) = .halt r.exitCode r.final

/-- Accepted (C++ `cp.accepted`): no gas credit left, the contract took the gas on itself (`ACCEPT`,
`SETGASLIMIT`); always so for internal messages and tick-tock. -/
def accepted (r : ComputeRun) : Bool := r.final.gas.gasCredit == 0

/-- What persists: the exit code, the committed `c4` and `c5`, the gas used. -/
def outcome (r : ComputeRun) : ComputeOutcome := ComputeOutcome.ofHalt r.exitCode r.final r.data

/-- Committed (C++ `cp.success`): accepted and with a committed state; only then do the new data
and actions persist. -/
def committed (r : ComputeRun) : Bool := r.accepted && r.final.cstate.committed

/-- A run that does not commit leaves the data as it was. -/
theorem outcome_c4_of_not_committed (r : ComputeRun) (h : r.committed = false) : r.outcome.c4 = r.data := by
  simp only [committed, Bool.and_eq_false_iff] at h
  simp only [outcome, ComputeOutcome.ofHalt]
  rcases h with h | h
  · simp [accepted] at h; simp [h]
  · simp [h]

/-- A run that commits leaves the committed `c4`. -/
theorem outcome_c4_of_committed (r : ComputeRun) (h : r.committed = true) :
    r.outcome.c4 = r.final.cstate.c4 := by
  simp only [committed, accepted, Bool.and_eq_true, beq_iff_eq] at h
  simp [outcome, ComputeOutcome.ofHalt, h.1, h.2]

end ComputeRun

/-- A contract specification. -/
structure ContractSpec where
  /-- The contract's persistent data, decoded. -/
  Data : Type
  /-- Decoding of `c4` (`none`: not a state of the contract). -/
  decode : Cell → Option Data
  /-- The invariant: holds of the data of every reachable state. -/
  Inv : Data → Prop
  /-- What one compute phase may do: the data before, the run (its input, whether it was accepted
  and committed, ...), the data after. -/
  Step : Data → ComputeRun → Data → Prop
  /-- The precondition on external messages: an external message is accepted (the contract pays
  for it) only if this holds of the data and the input. -/
  Accept : Data → ComputeInput → Prop
  /-- What the environment guarantees of each input (default: `ComputeInput.Valid`). -/
  Env : ComputeInput → Prop := ComputeInput.Valid

namespace ContractSpec

/-- Every compute phase of `code`, started on data that decodes and satisfies the invariant, leaves
data that decodes, satisfies the invariant and is related to the old by `Step`. -/
def StepSpec (S : ContractSpec) (code : Cell) : Prop :=
  ∀ (r : ComputeRun) (d : S.Data), r.Of code → S.Env r.input → S.decode r.data = some d → S.Inv d →
    ∃ d', S.decode r.outcome.c4 = some d' ∧ S.Inv d' ∧ S.Step d r d'

/-- An external message is accepted only if `Accept` holds of the data and the input. -/
def AcceptSpec (S : ContractSpec) (code : Cell) : Prop :=
  ∀ (r : ComputeRun) (d : S.Data), r.Of code → S.Env r.input → S.decode r.data = some d → S.Inv d →
    r.input.isExternal = true → r.accepted = true → S.Accept d r.input

/-- `code` meets the specification `S`. -/
def Holds (S : ContractSpec) (code : Cell) : Prop :=
  S.StepSpec code ∧ S.AcceptSpec code

end ContractSpec

end TvmLean.Contracts

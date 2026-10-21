import TvmLean.Proofs.Tx.Phases

/-!
# The compute phase of a transaction

`Tx.computePhaseRun` (C++ `Transaction::prepare_compute_phase`) decides which code and data the
account runs with (its own, or those of the inbound message's `StateInit` when it activates an
uninitialized or frozen account), runs the VM (`Tx.runVm`: `computePhaseInit` of the code and the
data) and keeps what the run committed (`ComputeOutcome.ofHalt`). This module states that in terms a
contract proof uses:
* `VmStart code data st`: `st` is a VM state the compute phase starts the code `code` from, with the
  data `data`, whatever the rest (stack of an inbound message or of tick-tock, `c7`, gas, libraries);
* `vmFinal st`: the state the run of the compute phase ends in;
* `computePhaseRun_spec`: after the compute phase, an active account runs either its own code and
  data, or those of the message's `StateInit` (then activated); if the phase succeeded, the data and
  the action list it hands on are what a run from `VmStart` of that code and data committed.
-/

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-- The initial stack of the compute phase: `recv_internal` / `recv_external` (balance, value,
message, body, selector) or `run_ticktock` (balance, address, whether tock, `-2`). -/
def ComputeStack (stack : Stack) : Prop :=
  (∃ balance value msg body ext, stack = computePhaseStack balance value msg body ext) ∨
    ∃ balance addr tock : Int, stack = #[.int (.num balance), .int (.num addr), .int (.num tock), .int (.num (-2))]

/-- `st` is a state the compute phase starts the code `code` from with the data `data`
(`Tx.runVm`): `computePhaseInit` of the code as the VM loads it (`convertCodeCell`, the code itself
for an ordinary cell), with any stack of `ComputeStack`, any `c7`, gas limits, libraries and
limits. -/
def VmStart (code data : Cell) (st : VmState) : Prop :=
  ∃ (gv : Nat) (libs : Array Cell) (stack : Stack) (c7 : Value) (gl gm gc : Int) (mdd : Nat)
    (mll : Option Nat), ComputeStack stack ∧
    st = { computePhaseInit (convertCodeCell code gv libs) data stack #[c7] gl gm gc gv with
           libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll }

/-- The state the run of the compute phase from `st` ends in (`Tx.runVm`: at most the gas bound of
steps). -/
def vmFinal (st : VmState) : VmState :=
  match VmState.run (st.gas.stepBound + 16) st with
  | .halt _ stF => stF
  | .continue stF => stF

/-- An ordinary code cell is run as it is. -/
theorem convertCodeCell_ordinary (code : Cell) (gv : Nat) (libs : Array Cell) (h : code.special = false) :
    convertCodeCell code gv libs = code := by
  unfold convertCodeCell
  split
  · unfold libraryResolveLoads
    cases hb : libraryChainBound with
    | zero => simp [libraryChainBound] at hb
    | succ n => simp [libraryResolveLoadsAux, h]
  · simp [h]

/-- The run of `Tx.runVm`: from a state of `VmStart` of the code and the account's data. -/
theorem runVm_spec (t : Tx) (code : Cell) (gl gm gc : Nat) (seed : BitString) (sl : SizeLimits) :
    OKp (fun r : VmState × Int => ∃ st, VmStart code (t.newData.getD Cell.empty) st ∧ r.1 = vmFinal st)
      (t.runVm code gl gm gc seed sl) := by
  unfold OKp Tx.runVm
  extract_lets stack libs st0 st fuel
  refine ⟨st, ⟨t.gv, libs, stack, t.c7 seed, _, _, _, sl.maxVmDataDepth, sl.maxTransactionLibraryLoads, ?_, rfl⟩, ?_⟩
  · simp only [stack]
    split
    · exact Or.inr ⟨_, _, _, rfl⟩
    · exact Or.inl ⟨_, _, _, _, _, rfl⟩
  · simp only [vmFinal, fuel]
    cases VmState.run (st.gas.stepBound + 16) st <;> rfl

/-- After the compute phase, an active account runs its own code and data (it was active) or those
of the message's `StateInit` (it is activated with them). -/
def ActiveFrom (t₀ u : Tx) : Prop :=
  (t₀.accStatus = .active ∧ u.newCode = t₀.newCode ∧ u.newData = t₀.newData) ∨
    (u.useMsgState = true ∧ u.wasActivated = true ∧
      ∃ si, msgStateInit? t₀ = some si ∧ u.newCode = si.code ∧ u.newData = si.data)

/-- A successful compute phase: the VM ran the account's code `code` on its data from a state of
`VmStart`, the run committed, and the committed `c4` and `c5` are handed on. -/
def RunFacts (u : Tx) : Prop :=
  ∃ code st, u.newCode = some code ∧ VmStart code (u.newData.getD Cell.empty) st ∧
    (vmFinal st).cstate.committed = true ∧ (vmFinal st).gas.gasCredit = 0 ∧
    u.computePhase.newData = some (vmFinal st).cstate.c4 ∧ u.computePhase.actions = some (vmFinal st).cstate.c5

/-- What the compute phase leaves: see the module docstring. -/
def ComputeResult (t₀ u : Tx) : Prop :=
  t₀.Fixed u ∧ u.inMsgState = t₀.inMsgState ∧ (u.accStatus = .active → ActiveFrom t₀ u) ∧
    (u.computePhase.success = true → RunFacts u)

/-- Invariant of the compute phase before it looks at the message's `StateInit`. -/
@[reducible] def CpInv0 (t₀ u : Tx) : Prop :=
  t₀.Fixed u ∧ u.inMsgState = t₀.inMsgState ∧ t₀.SameState u ∧ u.computePhase.success = false

/-- Invariant of the compute phase once it looked at the message's `StateInit`. -/
@[reducible] def CpInv (t₀ u : Tx) : Prop :=
  t₀.Fixed u ∧ u.inMsgState = t₀.inMsgState ∧ u.wasActivated = false ∧ u.computePhase.success = false ∧
    u.accStatus = t₀.accStatus ∧
    ((u.useMsgState = false ∧ u.newCode = t₀.newCode ∧ u.newData = t₀.newData) ∨
      (u.useMsgState = true ∧ t₀.accStatus ≠ .active ∧
        ∃ si, msgStateInit? t₀ = some si ∧ u.newCode = si.code ∧ u.newData = si.data))

/-- The commit rule of the compute phase (`ComputeOutcome.ofHalt`): a run that committed, with no
gas credit left, hands on its `c4` and `c5`. -/
theorem ofHalt_spec (ec : Int) (stF : VmState) (data0 : Cell) :
    OKp (fun o : ComputeOutcome => (stF.gas.gasCredit == 0 && stF.cstate.committed) = true →
      o.c4 = stF.cstate.c4 ∧ o.c5 = stF.cstate.c5) (ComputeOutcome.ofHalt ec stF data0) := by
  unfold OKp ComputeOutcome.ofHalt
  intro h
  simp [h]

/-- The message's `StateInit` is used (`state_hash` matches) only for an account that is not active. -/
theorem stateHashOk_spec (t : Tx) :
    OKp (fun b : Bool => b = true → t.accStatus ≠ .active)
      (match t.inMsgState with
       | some c => t.accStatus == .uninit ||
           (!t.wasFrozen && t.accStatus == .frozen && t.account.stateHash == bytesToBits c.hashBytes)
       | none => false) := by
  unfold OKp
  split
  · intro h hc
    rw [hc] at h
    revert h
    simp only [show (AccStatus.active == AccStatus.uninit) = false from rfl,
      show (AccStatus.active == AccStatus.frozen) = false from rfl]
    simp
  · intro h; cases h

set_option maxHeartbeats 4000000 in
/-- **The compute phase** (`Transaction::prepare_compute_phase`): from a transaction that has not
used the message's `StateInit` yet, the result satisfies `ComputeResult`. -/
theorem computePhaseRun_spec (t₀ : Tx) (gas : GasPrices) (sl : SizeLimits) (seed : BitString)
    (h1 : t₀.useMsgState = false) (h2 : t₀.wasActivated = false) (h3 : t₀.computePhase.success = false) :
    OKe (OKo (ComputeResult t₀)) (t₀.computePhaseRun gas sl seed) := by
  unfold Tx.computePhaseRun
  tx_vcg keep_jps
  tx_jp_spec [CpInv0 t₀]
  all_goals tx_vcg_inv [CpInv t₀]
  all_goals try trivial
  all_goals tx_specs [payGas_spec, checkInMsgStateHash_spec, unpackMsgState_spec, runVm_spec, ofHalt_spec,
    stateHashOk_spec]
  all_goals tx_close [Tx.account, Tx.kind, Tx.cfg, Tx.gv, Tx.globalLibs, Tx.inMsgState, Tx.accStatus,
    Tx.newCode, Tx.newData, Tx.useMsgState, Tx.wasActivated, Tx.computePhase, ComputePhase.success,
    ComputePhase.newData, ComputePhase.actions]
    [ComputeResult, ActiveFrom, RunFacts, CpInv, CpInv0, Tx.Fixed, Tx.SameState, msgStateInit?]

end TvmLean.Tx

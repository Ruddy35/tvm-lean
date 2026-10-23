import TvmLean.Proofs.Contracts.StorageRun.Ops

/-!
# TON Storage: an internal message from its sender on

The run of `recv_internal` (`Run.internal`, `StorageRun/Internal.lean`) cut where the sender
address is read (bit 114 of `recv_internal`'s cell): `Run.atSender` is the state there, the stack
`balance, msg_value, in_msg_body, sender` (any body and sender), any gas, loaded cells and
libraries. `Run.sender`: a run from there that commits leaves an outcome of `Run.Outcome`:
* an empty body, or operation 0: `add_to_balance(msg_value)` (`Run.Outcome.credit`);
* a body too short for the operation and the query id: an exception, no commit;
* any other operation: the runs from `Run.atOps` (`Run.ops`).
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

/-- The state of `recv_internal` at bit 114 of its cell, the sender address read: the stack
`balance, msg_value, in_msg_body, sender`, `c4` the data `d`, no action, any gas `g`, loaded cells
`lc` and libraries `ll`, steps and `c7`. -/
def atSender (d : Data) (bal val : Int) (body sender : Slice) (c7 : Value) (g : GasLimits)
    (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell) (mdd gv steps : Nat)
    (mll : Option Nat) : VmState :=
  { stack := (((#[].push (.int (.num bal))).push (.int (.num val))).push (.slice body)).push (.slice sender),
    regs := { c0 := .quit 0, c1 := .quit 1, c2 := .excQuit,
              c3 := .ordinary (Slice.ofCell storageCode) (.quit 0) OrdCregs.empty OrdCdata.empty,
              c4 := d.encode, c5 := Cell.empty, c7 := #[].push c7 },
    cc := .plain { cell := storageCode.refs[0]!.refs[0]!.refs[0]!.refs[0]!, bitPos := 114, refPos := 0 },
    cp := 0, gas := g, chksgnCounter := 0, loadedCells := lc, libraries := libs, callStack := #[],
    cstate := CommittedState.empty, maxDataDepth := mdd, globalVersion := gv, steps := steps,
    maxLibraryLoads := mll, loadedLibraries := ll }

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **From the sender on.** A run that commits leaves an outcome of `Run.Outcome`. -/
theorem sender (d : Data) (hwf : d.WF) (bal val : Int) (body sender : Slice) (c7 : Value) (g : GasLimits)
    (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell) (mdd gv steps : Nat)
    (mll : Option Nat) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel (atSender d bal val body sender c7 g lc ll libs mdd gv steps mll)) := by
  simp only [atSender]
  storage_setup d hwf
  by_cases hgv : 4 ≤ gv
  · storage_run_to 306 [hgv]
    all_goals first
      | storage_no_commit
      | storage_commit exact Outcome.credit_of d val _ ‹_› ‹_› (by storage_encode)
      | exact ops d hwf bal val sender _ _ _ c7 _ lc ll libs mdd gv _ mll _
  · storage_run_to 306 [hgv]
    all_goals first
      | storage_no_commit
      | storage_commit exact Outcome.credit_of d val _ ‹_› ‹_› (by storage_encode)
      | exact ops d hwf bal val sender _ _ _ c7 _ lc ll libs mdd gv _ mll _

end TvmLean.Contracts.Storage.Run

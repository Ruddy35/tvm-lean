import TvmLean.Proofs.Contracts.StorageRun.Common

/-!
# TON Storage: external messages and tick-tock

The storage contract has neither `recv_external` (method -1) nor `run_ticktock` (method -2): from
every state the compute phase starts from (`Run.start`: any data, `c7`, gas limits, global
version, libraries, limits, loaded cells), for any number of steps, the dispatcher (`SETCP0`,
`19 DICTPUSHCONST`, `DICTIGETJMPZ`) does not find the method id, `11 THROWARG` raises exception 11,
and the run never commits:

* `Run.external`: an external message (selector -1);
* `Run.tickTock`: tick-tock (selector -2).
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **An external message.** A run never commits. -/
theorem external (data msg : Cell) (body : Slice) (bal val : Int) (c7 : Value) (gl gm gc : Int) (gv : Nat)
    (libs : Array Cell) (mdd : Nat) (mll : Option Nat) (lc : Array (Array UInt8)) (fuel : Nat) :
    (VmState.runWith execInstr fuel
      (start data (computePhaseStack bal val msg body true) c7 gl gm gc gv libs mdd mll lc)).state.cstate.committed
      = false := by
  simp only [start, computePhaseInit, VmState.initial, computePhaseStack, Regs.initial]
  by_cases hgv : 4 ≤ gv
  · storage_run_to 100000 [hgv]
    all_goals ext_no_commit
  · storage_run_to 100000 [hgv]
    all_goals ext_no_commit

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **Tick-tock.** A run never commits. -/
theorem tickTock (data : Cell) (bal addr tock : Int) (c7 : Value) (gl gm gc : Int) (gv : Nat)
    (libs : Array Cell) (mdd : Nat) (mll : Option Nat) (lc : Array (Array UInt8)) (fuel : Nat) :
    (VmState.runWith execInstr fuel
      (start data #[.int (.num bal), .int (.num addr), .int (.num tock), .int (.num (-2))] c7 gl gm gc gv
        libs mdd mll lc)).state.cstate.committed = false := by
  simp only [start, computePhaseInit, VmState.initial, Regs.initial]
  by_cases hgv : 4 ≤ gv
  · storage_run_to 100000 [hgv]
    all_goals ext_no_commit
  · storage_run_to 100000 [hgv]
    all_goals ext_no_commit

end TvmLean.Contracts.Storage.Run

import TvmLean.Proofs.Contracts.Wallet3Run.Common

/-!
# Wallet v3: internal messages and tick-tock

From every state the compute phase starts from (`Run.start`: any data, `c7`, gas limits, global
version, libraries, limits, loaded cells), for any number of steps:

* `Run.internal`: on an internal message (selector 0) the dispatcher jumps to `recv_internal`
  (`DROP`), which returns: a run that commits leaves the data and the empty action list
  (`IntSpec`);
* `Run.tickTock`: on tick-tock (selector -2) the method id is not in the dictionary
  (`DICTIGETJMPZ` pushes it back) and `11 THROWARG` raises exception 11: the run never commits.
-/

namespace TvmLean.Contracts.Wallet3.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **An internal message.** A run that commits leaves the data and no action. -/
theorem internal (data msg : Cell) (body : Slice) (bal val : Int) (c7 : Value) (gl gm gc : Int) (gv : Nat)
    (libs : Array Cell) (mdd : Nat) (mll : Option Nat) (lc : Array (Array UInt8)) (fuel : Nat) :
    IntSpec data (VmState.runWith execInstr fuel
      (start data (computePhaseStack bal val msg body false) c7 gl gm gc gv libs mdd mll lc)) := by
  simp only [start, computePhaseInit, VmState.initial, computePhaseStack, Regs.initial]
  by_cases hgv : 4 ≤ gv
  · wallet_run [hgv]
    all_goals first | ext_no_commit | int_commit
  · wallet_run [hgv]
    all_goals first | ext_no_commit | int_commit

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
  · wallet_run [hgv]
    all_goals ext_no_commit
  · wallet_run [hgv]
    all_goals ext_no_commit

end TvmLean.Contracts.Wallet3.Run

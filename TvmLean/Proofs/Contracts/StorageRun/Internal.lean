import TvmLean.Proofs.Contracts.StorageRun.Sender

/-!
# TON Storage: an internal message

`Run.internal`: from every state the compute phase starts `storageCode` from on an internal message
(`Run.start` with the stack of `computePhaseStack … false`: any balance, value, message and body;
any `c7`, gas limits `gl gm gc`, global version, libraries, `max_data_depth`, `max_library_loads`
and loaded cells), on the data `Data.encode d` of a `d` within its widths, for any number of steps,
a run that commits leaves an outcome of `Run.Outcome` (`Run.Post`).

The run: the dispatcher (`SETCP0`, `19 DICTPUSHCONST`, `DICTIGETJMPZ` to `recv_internal`), then
`CTOS` of the message, any cell (`vm_ctos_any`: a slice, or an exception), `4 LDU` of the flags (a
bounced message: `recv_internal` returns, `Run.Outcome.keep`), `LDMSGADDR` of the sender (any
slice: the address read, or cell_und), up to bit 114 of `recv_internal`'s cell, then `Run.sender`.
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **An internal message.** A run that commits leaves an outcome of `Run.Outcome`. -/
theorem internal (d : Data) (hwf : d.WF) (msg : Cell) (body : Slice) (bal val : Int) (c7 : Value)
    (gl gm gc : Int) (gv : Nat) (libs : Array Cell) (mdd : Nat) (mll : Option Nat) (lc : Array (Array UInt8))
    (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel
      (start d.encode (computePhaseStack bal val msg body false) c7 gl gm gc gv libs mdd mll lc)) := by
  simp only [start, computePhaseInit, VmState.initial, computePhaseStack, Regs.initial]
  storage_setup d hwf
  by_cases hgv : 4 ≤ gv
  · storage_run_to 10 [hgv]
    all_goals try storage_no_commit
    all_goals (vm_ctos_any; · intro r h; exact post_of_not_committed d val r h)
    all_goals intro sl g lc ll fuel _
    all_goals simp only [Framed.after]
    all_goals vm_clear_unused
    storage_run_to 114 [hgv]
    all_goals first
      | storage_no_commit
      | storage_commit exact Outcome.keep
      | exact sender d hwf bal val body _ c7 _ _ _ libs mdd gv _ mll _
  · storage_run_to 10 [hgv]
    all_goals try storage_no_commit
    all_goals (vm_ctos_any; · intro r h; exact post_of_not_committed d val r h)
    all_goals intro sl g lc ll fuel _
    all_goals simp only [Framed.after]
    all_goals vm_clear_unused
    storage_run_to 114 [hgv]
    all_goals first
      | storage_no_commit
      | storage_commit exact Outcome.keep
      | exact sender d hwf bal val body _ c7 _ _ _ libs mdd gv _ mll _

end TvmLean.Contracts.Storage.Run

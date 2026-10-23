import TvmLean.Proofs.Contracts.StorageRun.Common

/-!
# TON Storage: `accept_storage_contract`

From the state of `recv_internal` after the operation and the query id are read (`Run.atOps`), for
the operation `accept_storage_contract` (`0x7a361688`): the data is read (`LDI 1`, `LDGRAMS`,
`LDMSGADDR`); a contract already active throws 1007, a sender that is not the provider throws 401
(`SDEQ`); else the data with the flag set is written (`NEWC 1 STI STGRAMS STSLICER STSLICER ENDC`,
`c4 POP`), the client and the torrent hash read (`get_client_data`), the message
`storage_contract_confirmed` built (`LTIME` from `c7`, any `c7`) and sent (mode 0); the other
checks of `recv_internal` fail, it returns. A run that commits: `Run.Outcome.accept`.
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **`accept_storage_contract`.** A run that commits sets the flag `active` of a contract that was
not active and sends one message. -/
theorem opAccept (d : Data) (hwf : d.WF) (bal val : Int) (sender : Slice) (qid : Int) (rest : Slice)
    (c7 : Value) (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell)
    (mdd gv steps : Nat) (mll : Option Nat) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel
      (atOps d bal val sender 2050365064 qid rest c7 g lc ll libs mdd gv steps mll)) := by
  simp only [atOps]
  storage_setup d hwf
  storage_run_to 100000 []
  all_goals first
    | storage_no_commit
    | storage_commit exact Outcome.accept_of _ _ (flag_false_of_not ‹_›) (by storage_encode)

end TvmLean.Contracts.Storage.Run

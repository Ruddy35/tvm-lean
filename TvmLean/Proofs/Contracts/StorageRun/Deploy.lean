import TvmLean.Proofs.Contracts.StorageRun.Common

/-!
# TON Storage: `deploy_storage_contract`

From the state of `recv_internal` after the operation and the query id are read (`Run.atOps`), for
the operation `deploy_storage_contract` (`0xe4748df1`): `add_to_balance(msg_value - 2 *
fee::receipt_value)` (the data with the new balance), the client and the torrent hash read from the
new data (`get_client_data`), the message `contract_deployed` built and sent (mode 0); the other
checks of `recv_internal` fail, it returns. A run that commits: `Run.Outcome.deploy`.
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **`deploy_storage_contract`.** A run that commits adds the message value less
`2 * fee::receipt_value` to the balance and sends one message. -/
theorem opDeploy (d : Data) (hwf : d.WF) (bal val : Int) (sender : Slice) (qid : Int) (rest : Slice)
    (c7 : Value) (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell)
    (mdd gv steps : Nat) (mll : Option Nat) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel
      (atOps d bal val sender 3832843761 qid rest c7 g lc ll libs mdd gv steps mll)) := by
  simp only [atOps]
  storage_setup d hwf
  storage_run_to 100000 []
  all_goals first
    | storage_no_commit
    | storage_commit exact Outcome.deploy_of d val _ _ ‹_› ‹_› (by storage_encode)

end TvmLean.Contracts.Storage.Run

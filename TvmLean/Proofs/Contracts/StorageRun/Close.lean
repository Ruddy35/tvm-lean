import TvmLean.Proofs.Contracts.StorageRun.Common

/-!
# TON Storage: `close_contract`

From the state of `recv_internal` after the operation and the query id are read (`Run.atOps`), for
the operation `close_contract` (`0x79f937ea`): the data is read (`LDI 1`, `LDGRAMS`, `LDMSGADDR`,
then the client and the torrent hash, `get_client_data`); a sender that is neither the provider nor
the client throws 401 (`SDEQ`, `SDEQ`, `OR`); the message `storage_contract_terminated` to the
client (`LTIME` from `c7`, any `c7`) is sent with all the balance (mode 128 + 32) when the contract
is not active; when it is, with mode 64, and the same message to the provider with mode 128 + 32.
The data is kept. A run that commits: `Run.Outcome.closeInactive` or `Run.Outcome.closeActive`.
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **`close_contract`.** A run that commits keeps the data and sends one message (a contract not
active) or two (an active one). -/
theorem opClose (d : Data) (hwf : d.WF) (bal val : Int) (sender : Slice) (qid : Int) (rest : Slice)
    (c7 : Value) (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell)
    (mdd gv steps : Nat) (mll : Option Nat) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel
      (atOps d bal val sender 2046375914 qid rest c7 g lc ll libs mdd gv steps mll)) := by
  simp only [atOps]
  storage_setup d hwf
  storage_run_to 100000 []
  all_goals first
    | storage_no_commit
    | storage_commit exact Outcome.closeInactive _ (flag_false_of_not ‹_›)
    | storage_commit exact Outcome.closeActive _ _ (flag_true_of_not ‹_›)

end TvmLean.Contracts.Storage.Run

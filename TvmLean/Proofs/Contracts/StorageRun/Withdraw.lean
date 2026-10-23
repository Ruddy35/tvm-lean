import TvmLean.Proofs.Contracts.StorageRun.Common

/-!
# TON Storage: `withdraw`

From the state of `recv_internal` after the operation and the query id are read (`Run.atOps`), for
the operation `withdraw` (`0x46ed2e94`): the data is read (`LDI 1`, `LDGRAMS`, `LDMSGADDR`); a
contract not active throws 1003, a sender that is not the provider throws 401 (`SDEQ`); with a
positive balance, `RAWRESERVE` of the balance and `fee::storage` (mode 2, `Spec.rawReserve_le15`:
in every global version); the message `reward_withdrawal` is built and sent (mode 128 + 32); the
other checks of `recv_internal` fail, it returns. A run that commits: `Run.Outcome.withdraw` or
`Run.Outcome.withdrawReserve`.
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **`withdraw`.** A run that commits keeps the data, reserves the balance if positive, and sends
one message. -/
theorem opWithdraw (d : Data) (hwf : d.WF) (bal val : Int) (sender : Slice) (qid : Int) (rest : Slice)
    (c7 : Value) (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell)
    (mdd gv steps : Nat) (mll : Option Nat) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel
      (atOps d bal val sender 1189949076 qid rest c7 g lc ll libs mdd gv steps mll)) := by
  simp only [atOps]
  storage_setup d hwf
  storage_run_to 100000 []
  all_goals first
    | storage_no_commit
    | storage_commit exact Outcome.withdrawReserve_of _ (flag_true_of_ne ‹_›) ‹_›
    | storage_commit exact Outcome.withdraw_of _ (flag_true_of_ne ‹_›) ‹_›

end TvmLean.Contracts.Storage.Run

import TvmLean.Proofs.Contracts.StorageRun.Common

/-!
# TON Storage: an operation the contract does not know

From the state of `recv_internal` after the operation and the query id are read (`Run.atOps`), for
an operation that is none of `deploy_storage_contract`, `accept_storage_contract`,
`close_contract`, `withdraw`, `proof_storage`: the five checks fail, `recv_internal` returns, and a
run that commits leaves the data and no action (`Run.Outcome.keep`).
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **An unknown operation.** A run that commits leaves the data and no action. -/
theorem opOther (d : Data) (hwf : d.WF) (bal val : Int) (sender : Slice) (op qid : Int) (rest : Slice)
    (c7 : Value) (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell)
    (mdd gv steps : Nat) (mll : Option Nat) (h1 : op ≠ 3832843761) (h2 : op ≠ 2050365064)
    (h3 : op ≠ 2046375914) (h4 : op ≠ 1189949076) (h5 : op ≠ 1100832077) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel
      (atOps d bal val sender op qid rest c7 g lc ll libs mdd gv steps mll)) := by
  simp only [atOps]
  storage_setup d hwf
  by_cases hgv : 4 ≤ gv
  · storage_run_to 100000 [hgv]
    all_goals first | storage_no_commit | storage_commit exact Outcome.keep
  · storage_run_to 100000 [hgv]
    all_goals first | storage_no_commit | storage_commit exact Outcome.keep

end TvmLean.Contracts.Storage.Run

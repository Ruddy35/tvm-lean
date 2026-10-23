import TvmLean.Proofs.Contracts.StorageRun.Deploy
import TvmLean.Proofs.Contracts.StorageRun.Accept
import TvmLean.Proofs.Contracts.StorageRun.Close
import TvmLean.Proofs.Contracts.StorageRun.Withdraw
import TvmLean.Proofs.Contracts.StorageRun.Proof
import TvmLean.Proofs.Contracts.StorageRun.Other

/-!
# TON Storage: every operation

From the state of `recv_internal` after the operation and the query id are read (`Run.atOps`),
whatever the operation: `Run.ops`, by cases, the runs of `Run.opDeploy`, `Run.opAccept`,
`Run.opClose`, `Run.opWithdraw`, `Run.opProof`, and `Run.opOther` for any other operation.
-/

namespace TvmLean.Contracts.Storage.Run

/-- **Any operation.** A run that commits leaves an outcome of `Run.Outcome`. -/
theorem ops (d : Data) (hwf : d.WF) (bal val : Int) (sender : Slice) (op qid : Int) (rest : Slice)
    (c7 : Value) (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell)
    (mdd gv steps : Nat) (mll : Option Nat) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel
      (atOps d bal val sender op qid rest c7 g lc ll libs mdd gv steps mll)) := by
  by_cases h1 : op = 3832843761
  · subst h1; exact opDeploy d hwf bal val sender qid rest c7 g lc ll libs mdd gv steps mll fuel
  by_cases h2 : op = 2050365064
  · subst h2; exact opAccept d hwf bal val sender qid rest c7 g lc ll libs mdd gv steps mll fuel
  by_cases h3 : op = 2046375914
  · subst h3; exact opClose d hwf bal val sender qid rest c7 g lc ll libs mdd gv steps mll fuel
  by_cases h4 : op = 1189949076
  · subst h4; exact opWithdraw d hwf bal val sender qid rest c7 g lc ll libs mdd gv steps mll fuel
  by_cases h5 : op = 1100832077
  · subst h5; exact opProof d hwf bal val sender qid rest c7 g lc ll libs mdd gv steps mll fuel
  exact opOther d hwf bal val sender op qid rest c7 g lc ll libs mdd gv steps mll h1 h2 h3 h4 h5 fuel

end TvmLean.Contracts.Storage.Run

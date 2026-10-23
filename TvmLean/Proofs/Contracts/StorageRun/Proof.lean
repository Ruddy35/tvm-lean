import TvmLean.Proofs.Contracts.StorageRun.ProofEnd
import TvmLean.Proofs.Exec.FramedDict

/-!
# TON Storage: `proof_storage`

From the state of `recv_internal` after the operation and the query id are read (`Run.atOps`), for
the operation `proof_storage` (`0x419d5d4d`): the proof is read from the body (`LDREF`, any cell),
the data is read; a contract not active throws 1003, a sender that is not the provider throws 401
(`SDEQ`); then `check_proof` (procedure 1):
* `XCTOS` of the proof (any cell): not special, false;
* the Merkle proof's tag (`8 LDU`, 3) and hash (`256 LDU`, the stored Merkle root), else false;
* the loop `while ((CHUNK_SIZE << key_len) < file_size) { key_len += 1; }` (`WHILE`): by the loop
  rule (`vm_loop_keep_c5`: the loop sends nothing), the key length any integer;
* `DICTUGET` of the chunk `next_proof / 64` in the dictionary of the proof (any cell, framed:
  `vm_dict_get_any`): found or not;
`check_proof` returns its result to bit 352 of the cell of `proof_storage` (`Run.atChecked`), and
the run goes on as `Run.checked` (`StorageRun/ProofEnd.lean`): a proof that fails throws 1002;
else the new balance, next byte to prove and time of the proof are written and the rest of the
message value is sent back. A run that commits: `Run.Outcome.proof`.
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **`proof_storage`.** A run that commits writes the data with a new balance, next byte to prove
and time of the proof, and sends one message. -/
theorem opProof (d : Data) (hwf : d.WF) (bal val : Int) (sender : Slice) (qid : Int) (rest : Slice)
    (c7 : Value) (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell)
    (mdd gv steps : Nat) (mll : Option Nat) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel
      (atOps d bal val sender 1100832077 qid rest c7 g lc ll libs mdd gv steps mll)) := by
  simp only [atOps]
  storage_setup d hwf
  -- up to the loop head of `check_proof`
  storage_run_to 100000 []
  all_goals try storage_no_commit
  -- the loop: the key length any integer
  all_goals (vm_at_loop_head; vm_loop_keep_c5 1)
  all_goals try storage_no_commit
  all_goals storage_step []
  all_goals storage_run_to 370 []
  all_goals try storage_no_commit
  -- `DICTUGET` on the dictionary of the proof
  all_goals vm_dict_get_any
  all_goals first | (intro r h; exact post_of_not_committed d val r h) | skip
  all_goals intros
  all_goals simp only [Framed.after]
  all_goals vm_clear_unused
  -- up to the return of `check_proof`, then `Run.checked`
  storage_run_to 352 []
  all_goals first
    | storage_no_commit
    | exact checked d hwf bal sender _ c7 _ _ _ libs mdd gv _ mll val (flag_true_of_ne ‹_›) _

end TvmLean.Contracts.Storage.Run

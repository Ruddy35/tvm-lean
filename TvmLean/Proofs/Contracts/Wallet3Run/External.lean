import TvmLean.Proofs.Contracts.Wallet3Run.Signature

/-!
# Wallet v3: an external message, from global version 4

`Run.external_le`: from every state the compute phase starts `wallet3Code` from on an external
message (`Run.start` with the stack of `computePhaseStack … true`: any balance, value, message and
body; any `c7`, gas limits `gl gm gc`, libraries, `max_data_depth`, `max_library_loads` and loaded
cells), at global version 4 or later, for any number of steps: a run that commits leaves the stored
data with the seqno increased by one and an action list of `SENDRAWMSG` actions only (`ExtSpec`).

The proof is the run (`wallet_run_to`, `vm_run` of `TvmLean/Proofs/Exec/Tactic.lean`) from the
dispatcher on (`SETCP0`, `19 DICTPUSHCONST`, `DICTIGETJMPZ` to `recv_external`) up to the
signature check, then `Run.signature_le` (`Wallet3Run/Signature.lean`, to `ACCEPT`) and
`Run.accepted_le` (`Wallet3Run/Accepted.lean`, after `ACCEPT`): one run in three modules. The run
is split where the state does not decide a case, and every path but the one that reaches `ACCEPT`
ends without committing:
* the gas: from version 4 an instruction (or a load) that runs out of gas stops the VM at once
  (`VmState.gasExhaustedNow`, C++ `consume_gas` with `consume_chk`, vm.h:203-209), each check a
  case on the unknown limits;
* `c7`: `NOW` reads entry 3 of `c7[0]`; if that is not a tuple of more than 3 entries whose entry 3
  is a finite integer, `NOW` or the `LEQ` after it raises an exception;
* the checks of `recv_external` (`valid_until`, seqno, subwallet, signature), each a case;
* `ACCEPT` makes the gas limit `min gasMax (2^63 - 1)` for any `gasMax`
  (`GasLimits.changeLimit_infty_min`, C++ `GasLimits::change_limit`).

The loaded cells are any (`lc`): from the empty set, the gas of the loads of the code's cells is a
term the kernel can evaluate (`cellLoadGas` compares representation hashes) and does, at a cost of
gigabytes, when it checks the steps of a path on which the gas is a case; with unknown loaded cells
it cannot. The closed facts of the code are proved over the fast twins (`vm.fastFacts`).
-/

namespace TvmLean.Contracts.Wallet3.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **An external message, from global version 4.** A run that commits leaves the data with the
seqno increased by one and `SENDRAWMSG` actions only. -/
theorem external_le (data msg : Cell) (body : Slice) (bal val : Int) (c7 : Value) (hdata : data.special = false)
    (gl gm gc : Int) (gv : Nat) (hgv : 4 ≤ gv) (libs : Array Cell) (mdd : Nat) (mll : Option Nat)
    (lc : Array (Array UInt8)) (fuel : Nat) :
    ExtSpec data (VmState.runWith execInstr fuel
      (start data (computePhaseStack bal val msg body true) c7 gl gm gc gv libs mdd mll lc)) := by
  simp only [start, computePhaseInit, VmState.initial, computePhaseStack, Regs.initial]
  -- up to the signature check (bit 304 of `recv_external`'s cell), then the runs from there
  wallet_run_to 304 [hgv]
  all_goals try (vm_has_run; exact signature_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgv _)
  all_goals ext_no_commit

end TvmLean.Contracts.Wallet3.Run

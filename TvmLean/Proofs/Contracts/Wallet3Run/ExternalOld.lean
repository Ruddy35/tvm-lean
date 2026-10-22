import TvmLean.Proofs.Contracts.Wallet3Run.Common

/-!
# Wallet v3: an external message, before global version 4

`Run.external_lt`: `Run.external_le` (`Wallet3Run/External.lean`) for the global versions below 4,
where the gas is checked after an instruction rather than when it is charged (`VmState.instrStep`,
C++ `consume_gas` without `consume_chk` before version 4, vm.h:203-209) and `CHKSIGNU` is not
counted (`VmState.registerChkSgnCall`, vm.h:434-443): the same run, with these cases decided the
other way.
-/

namespace TvmLean.Contracts.Wallet3.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **An external message, before global version 4.** A run that commits leaves the data with the
seqno increased by one and `SENDRAWMSG` actions only. -/
theorem external_lt (data msg : Cell) (body : Slice) (bal val : Int) (c7 : Value) (hdata : data.special = false)
    (gl gm gc : Int) (gv : Nat) (hgv : ¬ 4 ≤ gv) (libs : Array Cell) (mdd : Nat) (mll : Option Nat)
    (lc : Array (Array UInt8)) (fuel : Nat) :
    ExtSpec data (VmState.runWith execInstr fuel
      (start data (computePhaseStack bal val msg body true) c7 gl gm gc gv libs mdd mll lc)) := by
  simp only [start, computePhaseInit, VmState.initial, computePhaseStack, Regs.initial]
  wallet_run [hgv]
  -- the `WHILE` loop of the orders, by the loop rule with the action list made of `SENDRAWMSG` actions
  all_goals try (vm_has_run; vm_loop_c5 SendList)
  all_goals try (vm_has_run; wallet_step [hgv])
  all_goals try wallet_run [hgv]
  all_goals try vm_loop_close_c5
  all_goals first | ext_no_commit | ext_commit

end TvmLean.Contracts.Wallet3.Run

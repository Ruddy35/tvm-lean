import TvmLean.Proofs.Contracts.Wallet3Run.Common

/-!
# Wallet v3: an external message after `ACCEPT`, from global version 4

The run of `Run.external_le` (`Wallet3Run/External.lean`) cut where `recv_external` has accepted
the message (`ACCEPT`, bit 400 of its cell): `Run.accepted` is the state there, the stored key, seqno
and subwallet on the stack as `recv_external` read them from the data, `cs` the rest of the body
(the orders), and the parts that differ between the paths that reach it (gas, loaded cells,
counters, `c7`) any. `Run.accepted_le`: from every such state, at global version 4 or later, a run
that commits leaves the data with the seqno increased by one and `SENDRAWMSG` actions only
(`ExtSpec`): the orders are sent by the `WHILE` loop (the loop rule with the invariant `SendList`
of `c5`, `vm_loop_c5`), then `SWAP INC NEWC 32 STU 32 STU 256 STU ENDC c4 POP`.
-/

namespace TvmLean.Contracts.Wallet3.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

/-- The state of `recv_external` right after `ACCEPT` (bit 400 of its cell) on the data `data`:
the stack `balance, value, message, key, seqno, subwallet, cs` (the fields as `LDU` read them, `cs`
the rest of the body), `c4` the data, no action, and any gas `g`, `CHKSIGNU` count `cnt`, loaded
cells `lc`, free gas `fgc`, steps and `c7`. -/
def accepted (data msg : Cell) (bal val : Int) (cs : Slice) (c7 : Array Value) (g : GasLimits) (cnt : Nat)
    (lc : Array (Array UInt8)) (libs : Array Cell) (mdd gv : Nat) (fgc : Int) (steps : Nat)
    (mll : Option Nat) : VmState :=
  { stack := ((((((#[].push (.int (.num bal))).push (.int (.num val))).push (.cell msg)).push
        (.int (.num ↑(bitsToNat (Slice.readBits ({ cell := data, bitPos := 64, refPos := 0 } : Slice) 256))))).push
        (.int (.num ↑(bitsToNat ((Slice.ofCell data).readBits 32))))).push
        (.int (.num ↑(bitsToNat (Slice.readBits ({ cell := data, bitPos := 32, refPos := 0 } : Slice) 32))))).push
        (.slice cs)
    regs := { c0 := .quit 0, c1 := .quit 1, c2 := .excQuit,
              c3 := .ordinary (Slice.ofCell wallet3Code) (.quit 0) OrdCregs.empty OrdCdata.empty,
              c4 := data, c5 := Cell.empty, c7 := c7 }
    cc := .ordinary { cell := wallet3Code.refs[0]!.refs[1]!, bitPos := 400, refPos := 0 } (.quit 0)
      OrdCregs.empty OrdCdata.empty
    cp := 0, gas := g, chksgnCounter := cnt, loadedCells := lc, libraries := libs, callStack := #[],
    cstate := CommittedState.empty, maxDataDepth := mdd, globalVersion := gv, freeGasConsumed := fgc,
    steps := steps, maxLibraryLoads := mll }

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **After `ACCEPT`, from global version 4.** A run that commits leaves the data with the seqno
increased by one and `SENDRAWMSG` actions only. -/
theorem accepted_le (data msg : Cell) (bal val : Int) (cs : Slice) (c7 : Array Value) (g : GasLimits)
    (cnt : Nat) (lc : Array (Array UInt8)) (libs : Array Cell) (mdd gv : Nat) (fgc : Int) (steps : Nat)
    (mll : Option Nat) (hgv : 4 ≤ gv) (fuel : Nat) :
    ExtSpec data (VmState.runWith execInstr fuel
      (accepted data msg bal val cs c7 g cnt lc libs mdd gv fgc steps mll)) := by
  simp only [accepted]
  wallet_run [hgv]
  -- the `WHILE` loop of the orders, by the loop rule with the action list made of `SENDRAWMSG` actions
  all_goals try (vm_has_run; vm_loop_c5 SendList)
  all_goals try (vm_has_run; wallet_step [hgv])
  all_goals try wallet_run [hgv]
  all_goals try vm_loop_close_c5
  all_goals first | ext_no_commit | ext_commit

end TvmLean.Contracts.Wallet3.Run

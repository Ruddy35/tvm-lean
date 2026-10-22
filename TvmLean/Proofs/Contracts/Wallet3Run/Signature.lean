import TvmLean.Proofs.Contracts.Wallet3Run.Accepted

/-!
# Wallet v3: an external message from the signature check, from global version 4

The run of `Run.external_le` (`Wallet3Run/External.lean`) cut where `recv_external` has read the
body and the data and checked the seqno and the subwallet (bit 304 of its cell, before
`s0 s4 XCHG HASHSU s0 s5 s5 XC2PU CHKSIGNU 35 THROWIFNOT ACCEPT`): `Run.signature` is the state
there, the signature, the signed part and the orders of the body any slices (`sig`, `signed`,
`cs`), the stored subwallet, key and seqno on the stack as `recv_external` read them from the data,
and the parts that differ between the paths that reach it (gas, loaded cells, steps, `c7`) any.
`Run.signature_le`: from every such state, at global version 4 or later, a run that commits leaves
the data with the seqno increased by one and `SENDRAWMSG` actions only (`ExtSpec`): the run to
`ACCEPT`, then `Run.accepted_le`.
-/

namespace TvmLean.Contracts.Wallet3.Run

open TvmLean.Contracts

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

/-- The state of `recv_external` at bit 304 of its cell (the seqno and the subwallet checked) on the
data `data`: the stack `balance, value, message, sig, signed, subwallet, cs, key, seqno` (the
stored fields as `LDU` read them), `c4` the data, no action, no signature check counted, and any
gas `g`, loaded cells `lc`, steps and `c7`. -/
def signature (data msg : Cell) (bal val : Int) (sig signed cs : Slice) (c7 : Array Value) (g : GasLimits)
    (lc : Array (Array UInt8)) (libs : Array Cell) (mdd gv : Nat) (steps : Nat) (mll : Option Nat) : VmState :=
  { stack := ((((((((#[].push (.int (.num bal))).push (.int (.num val))).push (.cell msg)).push
        (.slice sig)).push (.slice signed)).push
        (.int (.num ↑(bitsToNat (Slice.readBits ({ cell := data, bitPos := 32, refPos := 0 } : Slice) 32))))).push
        (.slice cs)).push
        (.int (.num ↑(bitsToNat (Slice.readBits ({ cell := data, bitPos := 64, refPos := 0 } : Slice) 256))))).push
        (.int (.num ↑(bitsToNat ((Slice.ofCell data).readBits 32))))
    regs := { c0 := .quit 0, c1 := .quit 1, c2 := .excQuit,
              c3 := .ordinary (Slice.ofCell wallet3Code) (.quit 0) OrdCregs.empty OrdCdata.empty,
              c4 := data, c5 := Cell.empty, c7 := c7 }
    cc := .ordinary { cell := wallet3Code.refs[0]!.refs[1]!, bitPos := 304, refPos := 0 } (.quit 0)
      OrdCregs.empty OrdCdata.empty
    cp := 0, gas := g, chksgnCounter := 0, loadedCells := lc, libraries := libs, callStack := #[],
    cstate := CommittedState.empty, maxDataDepth := mdd, globalVersion := gv, steps := steps,
    maxLibraryLoads := mll }

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **From the signature check, from global version 4.** A run that commits leaves the data with
the seqno increased by one and `SENDRAWMSG` actions only. -/
theorem signature_le (data msg : Cell) (bal val : Int) (sig signed cs : Slice) (c7 : Array Value)
    (g : GasLimits) (lc : Array (Array UInt8)) (libs : Array Cell) (mdd gv : Nat) (steps : Nat)
    (mll : Option Nat) (hgv : 4 ≤ gv) (fuel : Nat) :
    ExtSpec data (VmState.runWith execInstr fuel
      (signature data msg bal val sig signed cs c7 g lc libs mdd gv steps mll)) := by
  simp only [signature]
  -- up to `ACCEPT` (bit 400 of `recv_external`'s cell), then the runs from there
  wallet_run_to 400 [hgv]
  all_goals try (vm_has_run; exact accepted_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgv _)
  all_goals ext_no_commit

end TvmLean.Contracts.Wallet3.Run

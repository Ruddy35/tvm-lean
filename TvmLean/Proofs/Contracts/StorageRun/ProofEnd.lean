import TvmLean.Proofs.Contracts.StorageRun.Common

/-!
# TON Storage: `proof_storage` after the proof is checked

The run of `proof_storage` (`StorageRun/Proof.lean`) cut where `check_proof` has returned (bit 352
of the cell of `proof_storage`, `Run.atChecked`): the stack holds what the data read left and the
result `flag` of `check_proof`, any gas, loaded cells and libraries. From there
(`Run.checked`): a flag 0 throws 1002 (`THROWIFNOT`); else `rand(file_size)` (`RAND`, from the seed
of `c7`, any `c7`), `now()` (`NOW`), the span paid `min(now() - last_proof_time, max_span)`, the
bounty `muldiv(file_size * rate_per_mb_day, span, 24 * 60 * 60 * 1024 * 1024)`, the balance
`max(0, balance - bounty)`, the new data written, and the message sent back with the rest of the
message value (mode 64 + 2). A run that commits: `Run.Outcome.proof`.
-/

namespace TvmLean.Contracts.Storage.Run

open TvmLean.Contracts

/-- The state of `proof_storage` when `check_proof` has returned its result `flag` (bit 352 of the
cell of `proof_storage`, entered as the return continuation): the stack `balance, sender,
max_span, client data, balance, provider, merkle_hash, file_size, last_proof_time,
rate_per_mb_day, flag`, `c4` the data `d`, no action, any gas `g`, loaded cells `lc`, libraries
`ll`, steps and `c7`. -/
def atChecked (d : Data) (bal : Int) (sender : Slice) (flag : Int) (c7 : Value) (g : GasLimits)
    (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell) (mdd gv steps : Nat)
    (mll : Option Nat) : VmState :=
  { stack := ((((((((((#[].push (.int (.num bal))).push (.slice sender)).push (.int (.num d.maxSpan))).push
      (.cell d.clientCell)).push (.int (.num d.balance))).push (.slice (Slice.ofCell (Cell.mkOrdinary d.provider)))).push
      (.int (.num d.merkleHash))).push (.int (.num d.fileSize))).push (.int (.num d.lastProofTime))).push
      (.int (.num d.ratePerMbDay))).push (.int (.num flag)),
    regs := { c0 := .quit 0, c1 := .quit 1, c2 := .excQuit,
              c3 := .ordinary (Slice.ofCell storageCode) (.quit 0) OrdCregs.empty OrdCdata.empty,
              c4 := d.encode, c5 := Cell.empty, c7 := #[].push c7 },
    cc := .ordinary { cell := storageCode.refs[0]!.refs[0]!.refs[0]!.refs[0]!.refs[3]!.refs[2]!, bitPos := 352, refPos := 0 }
      (.quit 0)
      ({ c0 := some (.ordinary { cell := storageCode.refs[0]!.refs[0]!.refs[0]!.refs[0]!.refs[3]!, bitPos := 920, refPos := 3 }
          (.quit 0) ({ c0 := some (.quit 0) } : OrdCregs) OrdCdata.empty) } : OrdCregs)
      OrdCdata.empty,
    cp := 0, gas := g, chksgnCounter := 0, loadedCells := lc, libraries := libs, callStack := #[],
    cstate := CommittedState.empty, maxDataDepth := mdd, globalVersion := gv, steps := steps,
    maxLibraryLoads := mll, loadedLibraries := ll }

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`)
set_option vm.fastFacts true

/-- The state of `proof_storage` when the new data is written (bit 872 of its cell, after `c4 POP`):
the stack `balance, sender`, `c4` any cell `c4`, no action, `c7` any `c7`, any gas, loaded cells,
libraries and steps. -/
def atStored (bal : Int) (sender : Slice) (c4 : Cell) (c7 : Array Value) (g : GasLimits)
    (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell) (mdd gv steps : Nat)
    (mll : Option Nat) : VmState :=
  { stack := (#[].push (.int (.num bal))).push (.slice sender),
    regs := { c0 := .ordinary { cell := storageCode.refs[0]!.refs[0]!.refs[0]!.refs[0]!.refs[3]!, bitPos := 920, refPos := 3 }
                (.quit 0) ({ c0 := some (.quit 0) } : OrdCregs) OrdCdata.empty,
              c1 := .quit 1, c2 := .excQuit,
              c3 := .ordinary (Slice.ofCell storageCode) (.quit 0) OrdCregs.empty OrdCdata.empty,
              c4 := c4, c5 := Cell.empty, c7 := c7 },
    cc := .plain { cell := storageCode.refs[0]!.refs[0]!.refs[0]!.refs[0]!.refs[3]!.refs[2]!, bitPos := 872, refPos := 0 },
    cp := 0, gas := g, chksgnCounter := 0, loadedCells := lc, libraries := libs, callStack := #[],
    cstate := CommittedState.empty, maxDataDepth := mdd, globalVersion := gv, steps := steps,
    maxLibraryLoads := mll, loadedLibraries := ll }

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The message back.** From the new data written (`Run.atStored`): the message to the sender
(`NEWC 6 STU STSLICER 111 STU ENDC`) is sent with mode 64 + 2 (`SENDRAWMSG`), `proof_storage`
and `recv_internal` return. A run that commits leaves the data `c4` and that one message: what
`h` says of them is the outcome. -/
theorem sendBack (d : Data) (val : Int) (bal : Int) (sender : Slice) (c4 : Cell) (c7 : Array Value)
    (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell)
    (mdd gv steps : Nat) (mll : Option Nat)
    (h : ∀ msg, Outcome d val c4 (OutAction.sendMsg 66 Cell.empty msg)) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel (atStored bal sender c4 c7 g lc ll libs mdd gv steps mll)) := by
  simp only [atStored]
  storage_run_to 100000 []
  all_goals first
    | storage_no_commit
    | storage_commit exact h _

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **After the proof is checked.** A run that commits writes the data with a new balance, next
byte to prove and time of the proof, and sends one message. -/
theorem checked (d : Data) (hwf : d.WF) (bal : Int) (sender : Slice) (flag : Int) (c7 : Value)
    (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell)
    (mdd gv steps : Nat) (mll : Option Nat) (val : Int) (ha : d.active = true) (fuel : Nat) :
    Post d val (VmState.runWith execInstr fuel
      (atChecked d bal sender flag c7 g lc ll libs mdd gv steps mll)) := by
  simp only [atChecked]
  storage_setup d hwf
  -- up to `NOW`, after `RAND`: the parameters of `c7` become any tuple
  storage_run_to 400 []
  all_goals try storage_no_commit
  all_goals try vm_forget_c7
  -- the data written: the stack's computed integers and `NOW`'s value become variables
  storage_run_to 632 []
  all_goals try storage_no_commit
  all_goals try vm_forget_stack
  storage_run_to 872 []
  all_goals first
    | storage_no_commit
    | (refine sendBack d val bal sender _ _ _ _ _ libs mdd gv _ mll (fun _ => ?_) _
       refine Outcome.proof_of _ _ _ _ _ ha ‹_› ‹_› ‹_› ?_
       simp only [Builder.finalize, Data.encode, Data.bits, coinsBits, coinsLen, Data.clientCell,
         Array.append_assoc, ha, Array.push_empty])

end TvmLean.Contracts.Storage.Run

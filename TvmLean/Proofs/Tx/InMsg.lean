import TvmLean.Proofs.Tx.Decompose
import TvmLean.Proofs.Tx.Compute

/-!
# The inbound message cell of a compute phase is ordinary

C++ reads the inbound message with `vm::load_cell_slice` before any phase
(`transaction_emulator_emulate_transaction`, emulator/emulator-extern.cpp:117;
`Transaction::unpack_input_msg`, crypto/block/transaction.cpp:887), which throws on a special cell
(crypto/vm/cells/CellSlice.cpp:1099-1139): no compute phase runs on a special message cell, and the
cell `prepare_vm_stack` pushes (transaction.cpp:1476) is that cell. The model refuses it at the same
places (`emulate`, `Tx.unpackInputMsg`: the emulator aborts, `unsupported`). Hence the state every
compute phase of a transaction of the model starts the VM from holds an ordinary message cell, if
any (`MsgOrd`), which `Ran` (TvmLean/Proofs/Tx/Effect.lean) records:

* `unpackInputMsg_ordinary`: the message of a transaction that unpacks is ordinary;
* the message cell through the phases (`*_inMsg`: no phase sets `Tx.inMsg`);
* `MsgOrd`, `VmStart.Facts.msgOrd`: the stack of the compute phase holds the transaction's message
  cell.
-/

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-- **The message of a transaction that unpacks is ordinary** (`Tx.unpackInputMsg` refuses a special
cell, as `vm::load_cell_slice` does: transaction.cpp:887). -/
theorem unpackInputMsg_ordinary {t t1 : Tx} {sl : SizeLimits} {fwd : MsgPrices}
    (h : t.unpackInputMsg sl fwd = some (.ok t1)) : t.inMsg.special = false := by
  cases hs : t.inMsg.special
  · rfl
  · unfold Tx.unpackInputMsg at h
    simp [hs] at h

/-! ## The message cell through the phases (no phase sets `Tx.inMsg`) -/

theorem newTx_inMsg (cfg : Config) (shardAccount inMsg : Cell) (kind : TxKind) (wc : Int)
    (addr addrBits : BitString) (lt now : Nat) (libs : Option Cell) :
    OKe (fun r : Tx × Array StoragePrices × SizeLimits × GasPrices × MsgPrices => r.1.inMsg = inMsg)
      (newTx cfg shardAccount inMsg kind wc addr addrBits lt now libs) := by
  unfold newTx
  tx_vcg
  all_goals first | rfl | tx_solve

theorem unpackInputMsg_inMsg (t : Tx) (sl : SizeLimits) (fwd : MsgPrices) :
    OKo (OKe fun u => u.inMsg = t.inMsg) (t.unpackInputMsg sl fwd) := by
  unfold Tx.unpackInputMsg
  tx_vcg
  all_goals rfl

theorem storagePhaseRun_inMsg (t : Tx) (pr : Array StoragePrices) (gas : GasPrices) (adj : Bool) :
    OKo (fun u => u.inMsg = t.inMsg) (t.storagePhaseRun pr gas adj) := by
  unfold Tx.storagePhaseRun
  tx_vcg
  all_goals rfl

theorem creditPhaseRun_inMsg (t : Tx) : OKe (OKo fun u => u.inMsg = t.inMsg) t.creditPhaseRun := by
  unfold Tx.creditPhaseRun
  tx_vcg
  all_goals rfl

theorem payGas_inMsg (t : Tx) (gas : GasPrices) (cp : ComputePhase) :
    OKe (fun r : Tx × ComputePhase => r.1.inMsg = t.inMsg) (t.payGas gas cp) := by
  unfold Tx.payGas
  tx_vcg
  all_goals rfl

theorem unpackMsgState_inMsg (t : Tx) (sl : SizeLimits) (libOnly : Bool) :
    OKp (fun r : Tx × Bool => r.1.inMsg = t.inMsg) (t.unpackMsgState sl libOnly) := by
  unfold Tx.unpackMsgState
  tx_vcg
  all_goals rfl

theorem checkInMsgStateHash_inMsg (t : Tx) : OKo (fun u => u.inMsg = t.inMsg) t.checkInMsgStateHash := by
  unfold Tx.checkInMsgStateHash
  tx_vcg
  all_goals rfl

/-- The message cell of `t₀` is that of `u`. -/
@[reducible] def KeepsMsg (t₀ u : Tx) : Prop := u.inMsg = t₀.inMsg

set_option maxHeartbeats 4000000 in
theorem computePhaseRun_inMsg (t₀ : Tx) (gas : GasPrices) (sl : SizeLimits) (seed : BitString) :
    OKe (OKo (fun u => u.inMsg = t₀.inMsg)) (t₀.computePhaseRun gas sl seed) := by
  unfold Tx.computePhaseRun
  tx_vcg keep_jps
  tx_jp_spec [KeepsMsg t₀]
  all_goals tx_vcg_inv [KeepsMsg t₀]
  all_goals try trivial
  all_goals tx_specs [payGas_inMsg, checkInMsgStateHash_inMsg, unpackMsgState_inMsg]
  all_goals tx_close [Tx.inMsg] [KeepsMsg]

/-- The storage and credit phases keep the message cell. -/
theorem StorageCredit.inMsg {pr : Array StoragePrices} {gas : GasPrices} {nc : Bool} {t1 t2 : Tx}
    (h : StorageCredit pr gas nc t1 t2) : t2.inMsg = t1.inMsg := by
  rcases h with ⟨ts, hs, h⟩ | ⟨tc, hs, h⟩
  · have e1 := OKo_of (storagePhaseRun_inMsg t1 pr gas false) hs
    rcases h with ⟨_, rfl⟩ | ⟨_, hc⟩
    · exact e1
    · exact (OKo_of (OKe_of (creditPhaseRun_inMsg ts) hc) rfl).trans e1
  · have e2 := OKo_of (storagePhaseRun_inMsg tc pr gas nc) hs
    rcases h with ⟨_, rfl⟩ | ⟨_, hc⟩
    · exact e2
    · exact e2.trans (OKo_of (OKe_of (creditPhaseRun_inMsg t1) hc) rfl)

/-! ## Runs from an ordinary message cell -/

/-- The message cell the state `st` starts with (in the stack of `computePhaseStack`), if any, is
ordinary. -/
def MsgOrd (st : VmState) : Prop :=
  ∀ bal val msg body ext, st.stack = computePhaseStack bal val msg body ext → msg.special = false

/-- The state the compute phase of `u` started the VM from (`VmStart.Facts`) has the message cell of
`u`, ordinary if `u`'s is. -/
theorem VmStart.Facts.msgOrd {gas : GasPrices} {seed : BitString} {u : Tx} {st : VmState}
    (h : VmStart.Facts gas seed u st) (hm : u.kind = .ord → u.inMsg.special = false) : MsgOrd st := by
  intro bal val msg body ext he
  by_cases hk : u.kind = .ord
  · rw [h.stack_ord hk] at he
    have e := congrArg (fun s : Stack => s[2]?) he
    simp only [computePhaseStack] at e
    simp at e
    rw [← e]
    exact hm hk
  · rw [h.stack_tickTock hk] at he
    have e := congrArg Array.size he
    simp [computePhaseStack] at e

end TvmLean.Tx

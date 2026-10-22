import TvmLean.Proofs.Tx.Phases

/-!
# What an action of the action phase keeps

The action phase (`Tx.actionPhaseRun`) runs the actions of the action list one after the other:
`Tx.actionSendMsg`, `Tx.actionReserve`, `Tx.actionChangeLibrary`, `Tx.actionSetCode` (C++
`try_action_send_msg`, `try_action_reserve_currency`, `try_action_change_library`,
`try_action_set_code`). Only `SETCODE` changes the code the action phase installs (`ap.newCode`);
no action changes the data, the status or the compute phase of the transaction (`ActKeep`). These
are the frame properties the proof of the action phase needs; `actionSendMsg` is long, and its
proof is run with `tx_vcg_close` (each join point proved once, in an auxiliary theorem).
-/

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-- What an action keeps of the transaction: everything but the balance, the messages and the
library. -/
@[reducible] def ActKeep (t u : Tx) : Prop :=
  t.Fixed u ∧ u.inMsgState = t.inMsgState ∧ u.useMsgState = t.useMsgState ∧
    u.wasActivated = t.wasActivated ∧ u.accStatus = t.accStatus ∧ u.newCode = t.newCode ∧
    u.newData = t.newData ∧ u.computePhase = t.computePhase

/-- The fields of a transaction `ActKeep` is about. -/
def ActKeep.view (t : Tx) :=
  (t.account, t.kind, t.cfg, t.gv, t.globalLibs, t.inMsgState, t.useMsgState, t.wasActivated, t.accStatus,
    t.newCode, t.newData, t.computePhase)

theorem ActKeep.congr {t₀ z x : Tx} (h : ActKeep t₀ z) (e : ActKeep.view x = ActKeep.view z) :
    ActKeep t₀ x := by
  simp only [ActKeep.view, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := e
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨⟨e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4, e5.trans h5⟩, e6.trans h6, e7.trans h7,
    e8.trans h8, e9.trans h9, e10.trans h10, e11.trans h11, e12.trans h12⟩

theorem ActKeep.of_view {t₀ x : Tx} (e : ActKeep.view x = ActKeep.view t₀) : ActKeep t₀ x :=
  ActKeep.congr (z := t₀) ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ e

theorem ActKeep.trans {t u v : Tx} (h1 : ActKeep t u) (h2 : ActKeep u v) : ActKeep t v := by
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, a6, a7, a8, a9, a10, a11, a12⟩ := h1
  obtain ⟨⟨b1, b2, b3, b4, b5⟩, b6, b7, b8, b9, b10, b11, b12⟩ := h2
  exact ⟨⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5⟩, b6.trans a6, b7.trans a7,
    b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11, b12.trans a12⟩

theorem newCode_congr {x z : ActionPhase} {c : Option Cell} (h : z.newCode = c) (e : x.newCode = z.newCode) :
    x.newCode = c := e.trans h

/-- `try_action_set_code`: the code to install. -/
theorem actionSetCode_spec (t : Tx) (ap : ActionPhase) (code : Cell) :
    OKp (fun r : Int × ActionPhase => r.1 = 0 ∧ r.2.newCode = some code) (t.actionSetCode ap code) :=
  ⟨rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- `try_action_change_library` changes the library only. -/
theorem actionChangeLibrary_spec (t₀ : Tx) (ap₀ : ActionPhase) (sl : SizeLimits) (mode : Nat)
    (lib : Sum BitString Cell) :
    OKp (fun r : Int × Tx × ActionPhase => ActKeep t₀ r.2.1 ∧ r.2.2.newCode = ap₀.newCode)
      (t₀.actionChangeLibrary ap₀ sl mode lib) := by
  unfold Tx.actionChangeLibrary
  tx_vcg_close [fun ap : ActionPhase => ap.newCode = ap₀.newCode, ActKeep t₀]
    (first
      | tx_frame [ActKeep.of_view, ActKeep.congr, newCode_congr]
      | (tx_subst_records; (try dsimp only);
          all_goals ((repeat' split) <;> tx_frame [ActKeep.of_view, ActKeep.congr, newCode_congr])))

set_option maxHeartbeats 4000000 in
/-- `try_action_reserve_currency` does not set the code. -/
theorem actionReserve_spec (t₀ : Tx) (ap₀ : ActionPhase) (mode : Nat) (value : Currencies) :
    OKe (fun r : Int × ActionPhase => r.2.newCode = ap₀.newCode) (t₀.actionReserve ap₀ mode value) := by
  unfold Tx.actionReserve
  tx_vcg_close [fun ap : ActionPhase => ap.newCode = ap₀.newCode]
    (first
      | tx_frame [newCode_congr]
      | (tx_subst_records; (try dsimp only); all_goals ((repeat' split) <;> tx_frame [newCode_congr])))

set_option maxHeartbeats 20000000 in
/-- `try_action_send_msg` changes the balance and the inbound message's remaining value only. -/
theorem actionSendMsg_spec (t₀ : Tx) (ap₀ : ActionPhase) (sl : SizeLimits) (mode : Nat) (msg : Cell)
    (redo : Nat) :
    OKe (fun r : Int × Tx × ActionPhase => ActKeep t₀ r.2.1 ∧ r.2.2.newCode = ap₀.newCode)
      (t₀.actionSendMsg ap₀ sl mode msg redo) := by
  unfold Tx.actionSendMsg
  tx_vcg_close [fun ap : ActionPhase => ap.newCode = ap₀.newCode, ActKeep t₀]
    (first
      | tx_frame [ActKeep.of_view, ActKeep.congr, newCode_congr]
      | (tx_subst_records; (try dsimp only);
          all_goals ((repeat' split) <;> tx_frame [ActKeep.of_view, ActKeep.congr, newCode_congr])))

end TvmLean.Tx

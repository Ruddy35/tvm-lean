import TvmLean.Transaction.Emulate
import TvmLean.Proofs.Tx.Tactic

/-!
# What each phase of a transaction keeps

Specifications of the phases of a transaction (`TvmLean/Transaction/`) and of the helpers of the
compute phase, in the form `OKo R (f ...)` / `OKe R (f ...)` (`TvmLean.Proofs.TxTac`): what a phase
returns, when it returns a transaction, satisfies `R`. Each is proved by running the phase
symbolically (`tx_vcg`). The facts are about what a phase leaves unchanged (`Tx.Fixed`,
`Tx.SameState`) and about the code and data of the account:
* the storage phase may freeze or delete the account (`StatusStep`) but keeps its code and data;
* the credit and bounce phases keep the state of the account;
* reading the inbound message keeps it too; `unpackMsgState` takes the code and data of the
  message's `StateInit` (`msgStateInit?`).
-/

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-- `==` on account statuses is equality (for `grind`). -/
instance : LawfulBEq AccStatus where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | cases h
  rfl {a} := by cases a <;> rfl

/-- The fields of a transaction that no phase changes. -/
@[reducible] def Tx.Fixed (t u : Tx) : Prop :=
  u.account = t.account ∧ u.kind = t.kind ∧ u.cfg = t.cfg ∧ u.gv = t.gv ∧ u.globalLibs = t.globalLibs

theorem Tx.Fixed.refl (t : Tx) : t.Fixed t := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Tx.Fixed.trans {t u v : Tx} (h1 : t.Fixed u) (h2 : u.Fixed v) : t.Fixed v :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.trans h1.2.2.2.2⟩

/-- The state of the account a phase may leave as it was: its code, data and library, its status
and whether the compute phase took them from the inbound message. -/
@[reducible] def Tx.SameState (t u : Tx) : Prop :=
  u.newCode = t.newCode ∧ u.newData = t.newData ∧ u.newLibrary = t.newLibrary ∧ u.accStatus = t.accStatus ∧
    u.useMsgState = t.useMsgState ∧ u.wasActivated = t.wasActivated ∧ u.wasFrozen = t.wasFrozen

theorem Tx.SameState.refl (t : Tx) : t.SameState t := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Tx.SameState.trans {t u v : Tx} (h1 : t.SameState u) (h2 : u.SameState v) : t.SameState v :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

/-! ## Helpers of the compute phase -/

theorem payGas_spec (t : Tx) (gas : GasPrices) (cp : ComputePhase) :
    OKe (fun r : Tx × ComputePhase => t.Fixed r.1 ∧ t.SameState r.1 ∧ r.1.inMsgState = t.inMsgState ∧
      r.1.computePhase = t.computePhase ∧ r.2.success = cp.success ∧ r.2.newData = cp.newData ∧
      r.2.actions = cp.actions) (t.payGas gas cp) := by
  unfold Tx.payGas
  tx_vcg
  all_goals exact ⟨Tx.Fixed.refl _, Tx.SameState.refl _, rfl, rfl, rfl, rfl, rfl⟩

/-- What the compute phase reads of the inbound message's `StateInit`. -/
def msgStateInit? (t : Tx) : Option Account.StateInit :=
  t.inMsgState.bind (Reader.runExact Account.Reader.stateInit)

theorem unpackMsgState_spec (t : Tx) (sl : SizeLimits) (libOnly : Bool) :
    OKp (fun r : Tx × Bool => t.Fixed r.1 ∧ r.1.inMsgState = t.inMsgState ∧ r.1.accStatus = t.accStatus ∧
        r.1.useMsgState = t.useMsgState ∧ r.1.wasActivated = t.wasActivated ∧ r.1.wasFrozen = t.wasFrozen ∧
        r.1.computePhase = t.computePhase ∧ r.1.myAddr = t.myAddr ∧ r.1.myAddrExact = t.myAddrExact ∧
        (r.2 = true → libOnly = false → ∃ si, msgStateInit? t = some si ∧ r.1.newCode = si.code ∧
          r.1.newData = si.data ∧ r.1.newFixedPrefixLength = si.fixedPrefixLength.getD 0) ∧
        (r.2 = false ∨ libOnly = true → r.1.newCode = t.newCode ∧ r.1.newData = t.newData))
      (t.unpackMsgState sl libOnly) := by
  unfold Tx.unpackMsgState
  tx_vcg
  all_goals refine ⟨Tx.Fixed.refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals intro h
  all_goals first
    | exact ⟨rfl, rfl⟩
    | (intro h'; exact ⟨_, ‹_›, rfl, rfl, rfl⟩)
    | simp_all

theorem eq_of_not_bne {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : ¬(a != b) = true) : a = b := by
  simpa using h

/-- The check of the hash of the inbound `StateInit` against the address (below the fixed prefix). -/
def stateHashMatches (t : Tx) (c : Cell) : Prop :=
  (bytesToBits c.hashBytes).extract t.newFixedPrefixLength 256 = t.account.addr.extract t.newFixedPrefixLength 256

theorem checkInMsgStateHash_spec (t : Tx) :
    OKo (fun u => t.Fixed u ∧ t.SameState u ∧ u.inMsgState = t.inMsgState ∧ u.computePhase = t.computePhase ∧
        u.newFixedPrefixLength = t.newFixedPrefixLength ∧ ∃ c, t.inMsgState = some c ∧ stateHashMatches t c)
      t.checkInMsgStateHash := by
  unfold Tx.checkInMsgStateHash
  tx_vcg
  all_goals exact ⟨Tx.Fixed.refl _, Tx.SameState.refl _, rfl, rfl, rfl, _, ‹_›, eq_of_not_bne ‹_›⟩

/-! ## The phases around the compute and action phases -/

/-- What a phase that is not the compute or the action phase keeps. -/
@[reducible] def Tx.Keep (t u : Tx) : Prop :=
  t.Fixed u ∧ u.inMsgState = t.inMsgState ∧ u.computePhase = t.computePhase ∧ u.myAddr = t.myAddr ∧
    u.myAddrExact = t.myAddrExact ∧ u.newFixedPrefixLength = t.newFixedPrefixLength

theorem Tx.Keep.refl (t : Tx) : t.Keep t := ⟨Tx.Fixed.refl t, rfl, rfl, rfl, rfl, rfl⟩

theorem Tx.Keep.trans {t u v : Tx} (h1 : t.Keep u) (h2 : u.Keep v) : t.Keep v :=
  ⟨h1.1.trans h2.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.trans h1.2.2.2.2.2⟩

/-- `Transaction::unpack_input_msg` changes neither the account's state nor the compute phase; it
records the message's `StateInit`. -/
theorem unpackInputMsg_spec (t : Tx) (sl : SizeLimits) (fwd : MsgPrices) :
    OKo (OKe fun u => t.Fixed u ∧ t.SameState u ∧ u.computePhase = t.computePhase ∧ u.myAddr = t.myAddr ∧
        u.myAddrExact = t.myAddrExact ∧ u.newFixedPrefixLength = t.newFixedPrefixLength)
      (t.unpackInputMsg sl fwd) := by
  unfold Tx.unpackInputMsg
  tx_vcg
  all_goals exact ⟨Tx.Fixed.refl _, Tx.SameState.refl _, rfl, rfl, rfl, rfl⟩

/-- How the storage phase may change the status: freeze an active account, delete one. -/
def StatusStep (t u : Tx) : Prop :=
  (u.accStatus = t.accStatus ∧ u.wasFrozen = t.wasFrozen) ∨
    (t.accStatus = .active ∧ u.accStatus = .frozen ∧ u.wasFrozen = true) ∨
    (u.accStatus = .deleted ∧ u.wasFrozen = t.wasFrozen)

theorem storagePhaseRun_spec (t : Tx) (pr : Array StoragePrices) (gas : GasPrices) (adj : Bool) :
    OKo (fun u => t.Keep u ∧ u.newCode = t.newCode ∧ u.newData = t.newData ∧ u.newLibrary = t.newLibrary ∧
        u.useMsgState = t.useMsgState ∧ u.wasActivated = t.wasActivated ∧ StatusStep t u)
      (t.storagePhaseRun pr gas adj) := by
  unfold Tx.storagePhaseRun
  tx_vcg
  all_goals first
    | exact ⟨Tx.Keep.refl _, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | exact ⟨Tx.Keep.refl _, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨‹_›, rfl, rfl⟩)⟩
    | exact ⟨Tx.Keep.refl _, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

theorem creditPhaseRun_spec (t : Tx) :
    OKe (OKo fun u => t.Keep u ∧ t.SameState u) t.creditPhaseRun := by
  unfold Tx.creditPhaseRun
  tx_vcg
  all_goals exact ⟨Tx.Keep.refl _, Tx.SameState.refl _⟩

theorem bouncePhaseRun_spec (t : Tx) :
    OKe (OKo fun u => t.Keep u ∧ t.SameState u) t.bouncePhaseRun := by
  unfold Tx.bouncePhaseRun
  tx_vcg
  all_goals exact ⟨Tx.Keep.refl _, Tx.SameState.refl _⟩

end TvmLean.Tx

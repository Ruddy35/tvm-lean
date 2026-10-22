import TvmLean.Proofs.Tx.Decompose
import TvmLean.Proofs.Tx.Compute
import TvmLean.Proofs.Tx.ActionPhase

/-!
# What a transaction does to the code and data of an account

`emulate_effect` and `emulateTickTock_effect` put together the decomposition of a transaction
(`emulate_final`, `emulateTickTock_final`) and the specifications of its phases: if the account is
active at the end of the transaction (before `Tx.computeState` writes it), its code and data are
* those it ran with (`Source`): its own, if it was active, or those of the inbound message's
  `StateInit` (an uninitialized or frozen account activated by the message), unchanged (the compute
  phase failed, did not commit, or the action phase failed); or
* the committed `c4` of a run of the compute phase from `VmStart` of that code and data (`Ran`),
  with the code given by the `SETCODE` actions of the committed action list `c5` (`NewCode`).
Everything else (storage, credit and bounce phases, rollback of a failed compute or action phase,
deployment by `StateInit`) is settled here once and for all.
-/

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-- The code and the data the account runs with in a transaction that starts from `t₀` and ends in
`tf`: its own (it was active), or those of the inbound message's `StateInit` (the compute phase took
them: `useMsgState`). -/
def Source (t₀ tf : Tx) (code data : Option Cell) : Prop :=
  (t₀.accStatus = .active ∧ code = t₀.newCode ∧ data = t₀.newData) ∨
    (∃ si, msgStateInit? tf = some si ∧ tf.useMsgState = true ∧ code = si.code ∧ data = si.data)

/-- A committed run of the compute phase: from a state of `VmStart` of the code `code` and the data
`data`, the run committed (with no gas credit left) the data `c4` and the action list `c5`. -/
def Ran (code : Cell) (data : Option Cell) (c4 c5 : Cell) : Prop :=
  ∃ st, VmStart code (data.getD Cell.empty) st ∧ (vmFinal st).cstate.committed = true ∧
    (vmFinal st).gas.gasCredit = 0 ∧ c4 = (vmFinal st).cstate.c4 ∧ c5 = (vmFinal st).cstate.c5

/-- What a transaction from `t₀` to `tf` does to the code and data of an account active at its end:
see the module docstring. -/
def Effect (t₀ tf : Tx) : Prop :=
  tf.accStatus = .active → ∃ code data, Source t₀ tf code data ∧
    ((tf.newCode = code ∧ tf.newData = data) ∨
      ∃ c c4 c5, code = some c ∧ Ran c data c4 c5 ∧ tf.newData = some c4 ∧ NewCode c5 code tf.newCode)

/-- The storage and credit phases keep the code, the data and the flags of the message's
`StateInit`, and change the status by `StatusStep`. -/
theorem StorageCredit.spec {pr : Array StoragePrices} {gas : GasPrices} {nc : Bool} {t1 t2 : Tx}
    (h : StorageCredit pr gas nc t1 t2) :
    t1.Keep t2 ∧ t2.newCode = t1.newCode ∧ t2.newData = t1.newData ∧ t2.useMsgState = t1.useMsgState ∧
      t2.wasActivated = t1.wasActivated ∧ StatusStep t1 t2 := by
  rcases h with ⟨ts, hs, h⟩ | ⟨tc, hs, h⟩
  · have ⟨k1, c1, d1, _, u1, w1, s1⟩ := OKo_of (storagePhaseRun_spec t1 pr gas false) hs
    rcases h with ⟨_, rfl⟩ | ⟨_, hc⟩
    · exact ⟨k1, c1, d1, u1, w1, s1⟩
    · have ⟨k2, c2, d2, _, a2, u2, w2, f2⟩ := OKo_of (OKe_of (creditPhaseRun_spec ts) hc) rfl
      refine ⟨k1.trans k2, c2.trans c1, d2.trans d1, u2.trans u1, w2.trans w1, ?_⟩
      rcases s1 with ⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨a2.trans e1, f2.trans e2⟩
      · exact Or.inr (Or.inl ⟨e1, a2.trans e2, f2.trans e3⟩)
      · exact Or.inr (Or.inr ⟨a2.trans e1, f2.trans e2⟩)
  · have ⟨k2, c2, d2, _, u2, w2, s2⟩ := OKo_of (storagePhaseRun_spec tc pr gas nc) hs
    rcases h with ⟨_, rfl⟩ | ⟨_, hc⟩
    · exact ⟨k2, c2, d2, u2, w2, s2⟩
    · have ⟨k1, c1, d1, _, a1, u1, w1, f1⟩ := OKo_of (OKe_of (creditPhaseRun_spec t1) hc) rfl
      refine ⟨k1.trans k2, c2.trans c1, d2.trans d1, u2.trans u1, w2.trans w1, ?_⟩
      rcases s2 with ⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1.trans a1, e2.trans f1⟩
      · exact Or.inr (Or.inl ⟨a1.symm.trans e1, e2, e3⟩)
      · exact Or.inr (Or.inr ⟨e1, e2.trans f1⟩)

/-- The phases from the compute phase on: from `t2` (before the compute phase) to `tf`. -/
theorem effect_of_phases {t₀ t2 t3 t4 tf : Tx} {gas : GasPrices} {sl : SizeLimits} {seed : BitString}
    (h0 : t₀.accStatus = .active → t2.accStatus = .active → t2.newCode = t₀.newCode ∧ t2.newData = t₀.newData ∧
      t₀.accStatus = .active)
    (h0' : t2.accStatus = .active → t₀.accStatus = .active)
    (hu : t2.useMsgState = false) (hw : t2.wasActivated = false) (hs : t2.computePhase.success = false)
    (hc : t2.computePhaseRun gas sl seed = .ok (some t3))
    (ha : (t3.computePhase.success = true ∧ t3.actionPhaseRun sl = .ok (some t4)) ∨
      (¬t3.computePhase.success = true ∧ t4 = t3))
    (hb : t4.accStatus = .active → tf.accStatus = .active ∧ tf.newCode = t4.newCode ∧
      tf.newData = t4.newData ∧ tf.inMsgState = t4.inMsgState ∧ tf.useMsgState = t4.useMsgState)
    (hb' : tf.accStatus = .active → t4.accStatus = .active) :
    Effect t₀ tf := by
  intro hact
  have hact4 := hb' hact
  obtain ⟨_, hcode, hdata, _, huse⟩ := hb hact4
  have ⟨⟨_, _, _, _, _⟩, hin3, hactive3, hrun3⟩ := OKo_of (OKe_of (computePhaseRun_spec t2 gas sl seed hu hw hs) hc) rfl
  -- the state after the compute phase
  have hact3 : t3.accStatus = .active := by
    rcases ha with ⟨hsucc, hap⟩ | ⟨_, rfl⟩
    · have ⟨_, _, _, _, _, hst, _⟩ := OKo_of (OKe_of (actionPhaseRun_spec t3 sl) hap) rfl
      rcases hst with e | e | e
      · rw [← e]; exact hact4
      · rw [e] at hact4; cases hact4
      · rw [e] at hact4; cases hact4
    · exact hact4
  -- where the code and data come from
  have hsrc : Source t₀ tf t3.newCode t3.newData := by
    rcases hactive3 hact3 with ⟨h2a, hc3, hd3⟩ | ⟨huse3, _, si, hsi, hc3, hd3⟩
    · have ⟨e1, e2, e3⟩ := h0 (h0' h2a) h2a
      exact Or.inl ⟨e3, hc3.trans e1, hd3.trans e2⟩
    · have hin4 : t4.inMsgState = t3.inMsgState ∧ t4.useMsgState = t3.useMsgState := by
        rcases ha with ⟨_, hap⟩ | ⟨_, rfl⟩
        · have := OKo_of (OKe_of (actionPhaseRun_spec t3 sl) hap) rfl
          exact ⟨this.2.2.1, this.2.2.2.1⟩
        · exact ⟨rfl, rfl⟩
      refine Or.inr ⟨si, ?_, huse.trans (hin4.2.trans huse3), hc3, hd3⟩
      have := (hb hact4).2.2.2.1
      unfold msgStateInit? at hsi ⊢
      rw [this, hin4.1, hin3]
      exact hsi
  refine ⟨t3.newCode, t3.newData, hsrc, ?_⟩
  rcases ha with ⟨hsucc, hap⟩ | ⟨_, rfl⟩
  · have ⟨_, _, _, _, _, _, hcd⟩ := OKo_of (OKe_of (actionPhaseRun_spec t3 sl) hap) rfl
    rcases hcd with ⟨e1, e2⟩ | ⟨c5, h5, hd, hnc⟩
    · exact Or.inl ⟨hcode.trans e1, hdata.trans e2⟩
    · obtain ⟨code, st, hcode3, hstart, hcomm, hcred, hnd, hact5⟩ := hrun3 hsucc
      rw [hact5] at h5
      cases h5
      refine Or.inr ⟨code, _, _, hcode3, ⟨st, hstart, hcomm, hcred, rfl, rfl⟩, ?_, ?_⟩
      · rw [hdata, hd, hnd]
      · rw [hcode]; exact hnc
  · exact Or.inl ⟨hcode, hdata⟩

/-- The state `tf` an ordinary transaction ends in (`EmulateFinal`) has `Effect t₀ tf` from the
state `t₀` read from the shard account. -/
theorem EmulateFinal.effect {configRoot shardAccount inMsg : Cell} {now lt : Nat} {randSeed : BitString}
    {libs : Option Cell} {tf : Tx} {sl : SizeLimits}
    (h : EmulateFinal configRoot shardAccount inMsg now lt randSeed libs tf sl) :
    ∃ cfg wc addr t₀, StartsFrom shardAccount cfg wc addr .ord t₀ ∧ Effect t₀ tf := by
  obtain ⟨cfg, wc, addr, addrBits, t0, pricing, gas, fwd, t1, t2, t3, t4, _, _, hnew, hin,
    ⟨nc, hsc⟩, hc, ha, hb⟩ := h
  have hstart := OKe_of (newTx_spec cfg shardAccount inMsg .ord wc addr addrBits lt now libs) hnew
  refine ⟨cfg, wc, addr, t0, hstart, ?_⟩
  obtain ⟨a, _, _, _, _, _, hu0, hw0, _, hs0, _, _, _⟩ := hstart
  have ⟨_, ⟨c1, d1, _, s1, u1, w1, _⟩, cp1, _⟩ := OKe_of (OKo_of (unpackInputMsg_spec t0 sl fwd) hin) rfl
  have ⟨⟨_, _, cp2, _⟩, c2, d2, u2, w2, st2⟩ := StorageCredit.spec hsc
  refine effect_of_phases (t2 := t2) (t3 := t3) (t4 := t4) (gas := gas) (sl := sl) (seed := randSeed)
    ?_ ?_ ?_ ?_ ?_ hc ha ?_ ?_
  · intro h0 h2
    exact ⟨c2.trans c1, d2.trans d1, h0⟩
  · intro h2
    rcases st2 with ⟨e1, _⟩ | ⟨_, e2, _⟩ | ⟨e1, _⟩
    · rw [← s1, ← e1]; exact h2
    · rw [e2] at h2; cases h2
    · rw [e1] at h2; cases h2
  · rw [u2, u1, hu0]
  · rw [w2, w1, hw0]
  · rw [cp2, cp1, hs0]
  · intro h4
    rcases hb with rfl | hb
    · exact ⟨h4, rfl, rfl, rfl, rfl⟩
    · have ⟨⟨_, e1, _⟩, c, d, _, s, u, _⟩ := OKo_of (OKe_of (bouncePhaseRun_spec t4) hb) rfl
      exact ⟨s.trans h4, c, d, e1, u⟩
  · intro h4
    rcases hb with rfl | hb
    · exact h4
    · have ⟨_, _, _, _, s, _⟩ := OKo_of (OKe_of (bouncePhaseRun_spec t4) hb) rfl
      rw [← s]; exact h4

/-- **What an ordinary transaction does** (`emulate`): the new account is `Tx.computeState` of a state
`tf` with `Effect t₀ tf`, `t₀` the state read from the shard account (`StartsFrom`). -/
theorem emulate_effect (configRoot shardAccount inMsg : Cell) (now lt : Nat) (randSeed : BitString)
    (libs : Option Cell) :
    OKp (OKout fun _ acc => ∃ tf sl t' cfg wc addr t₀, tf.computeState sl = some (t', acc) ∧
        StartsFrom shardAccount cfg wc addr .ord t₀ ∧ Effect t₀ tf)
      (emulate configRoot shardAccount inMsg now lt randSeed libs) := by
  have h := emulate_final configRoot shardAccount inMsg now lt randSeed libs
  unfold OKp at h ⊢
  revert h
  cases emulate configRoot shardAccount inMsg now lt randSeed libs with
  | ok tx acc =>
    intro h
    obtain ⟨tf, sl, t', hacc, hf⟩ := h
    obtain ⟨cfg, wc, addr, t₀, hs, he⟩ := hf.effect
    exact ⟨tf, sl, t', cfg, wc, addr, t₀, hacc, hs, he⟩
  | _ => intro _; trivial

/-- The state `tf` a tick-tock transaction ends in (`TickTockFinal`) has `Effect t₀ tf` from the
state `t₀` read from the shard account. -/
theorem TickTockFinal.effect {configRoot shardAccount : Cell} {isTock : Bool} {now lt : Nat}
    {randSeed : BitString} {libs : Option Cell} {tf : Tx} {sl : SizeLimits}
    (h : TickTockFinal configRoot shardAccount isTock now lt randSeed libs tf sl) :
    ∃ cfg wc addr kind t₀, StartsFrom shardAccount cfg wc addr kind t₀ ∧ Effect t₀ tf := by
  obtain ⟨cfg, kind, wc, addr, addrBits, t0, pricing, gas, fwd, t2, t3, _, _, hnew, _, hs, hc, ha⟩ := h
  have hstart := OKe_of (newTx_spec cfg shardAccount Cell.empty kind wc addr addrBits lt now libs) hnew
  refine ⟨cfg, wc, addr, kind, t0, hstart, ?_⟩
  obtain ⟨a, _, _, _, _, _, hu0, hw0, _, hs0, _, _, _⟩ := hstart
  have ⟨⟨_, _, cp2, _⟩, c2, d2, _, u2, w2, st2⟩ := OKo_of (storagePhaseRun_spec t0 pricing gas false) hs
  refine effect_of_phases (t2 := t2) (t3 := t3) (t4 := tf) (gas := gas) (sl := sl) (seed := randSeed)
    ?_ ?_ ?_ ?_ ?_ hc ha ?_ ?_
  · intro h0 _
    exact ⟨c2, d2, h0⟩
  · intro h2
    rcases st2 with ⟨e1, _⟩ | ⟨_, e2, _⟩ | ⟨e1, _⟩
    · rw [← e1]; exact h2
    · rw [e2] at h2; cases h2
    · rw [e1] at h2; cases h2
  · rw [u2, hu0]
  · rw [w2, hw0]
  · rw [cp2, hs0]
  · intro h4; exact ⟨h4, rfl, rfl, rfl, rfl⟩
  · intro h4; exact h4

/-- **What a tick-tock transaction does** (`emulateTickTock`). -/
theorem emulateTickTock_effect (configRoot shardAccount : Cell) (isTock : Bool) (now lt : Nat)
    (randSeed : BitString) (libs : Option Cell) :
    OKp (OKout fun _ acc => ∃ tf sl t' cfg wc addr kind t₀, tf.computeState sl = some (t', acc) ∧
        StartsFrom shardAccount cfg wc addr kind t₀ ∧ Effect t₀ tf)
      (emulateTickTock configRoot shardAccount isTock now lt randSeed libs) := by
  have h := emulateTickTock_final configRoot shardAccount isTock now lt randSeed libs
  unfold OKp at h ⊢
  revert h
  cases emulateTickTock configRoot shardAccount isTock now lt randSeed libs with
  | ok tx acc =>
    intro h
    obtain ⟨tf, sl, t', hacc, hf⟩ := h
    obtain ⟨cfg, wc, addr, kind, t₀, hs, he⟩ := hf.effect
    exact ⟨tf, sl, t', cfg, wc, addr, kind, t₀, hacc, hs, he⟩
  | _ => intro _; trivial

end TvmLean.Tx

import TvmLean.Proofs.Tx.Actions

/-!
# The action phase

`Tx.actionPhaseRun` (C++ `Transaction::prepare_action_phase`) reads the action list `c5` the compute
phase committed (`actionNode`: its nodes, from the last action; `Terminal`: the end of the list),
parses every action, then runs them from the first. `actionPhaseRun_spec`: what it returns keeps
the account, the configuration and the flags of the message's `StateInit`; the status stays, or
the account is deleted or left uninitialized (`SENDRAWMSG` with mode 32); and either the code and the
data stay (the phase failed, or the new state exceeded the limits), or the data is the committed
`c4` and the code is given by the `SETCODE` actions of the list (`NewCode`: the old code if the list
has none, else the code of one of them).

The proof follows the three loops with their invariants (`APInv1`, `APInv2`, `APInv3`,
`OKe_forIn_range`); the proof of each loop step is put in an auxiliary theorem (`tx_compact`).
-/

namespace TvmLean.Tx
open TvmLean.Proofs.TxTac


/-- The `i`-th node of the action list `c5` (`out_list$_ prev:^(OutList n) action:OutAction`): `c5`
itself is the last action, its first reference the list before it. -/
def actionNode (c5 : Cell) : Nat → Cell
  | 0 => c5
  | i + 1 => (actionNode c5 i).refs[0]!

/-- The end of an action list (`out_list_empty$_`): no bits, no references. -/
def Terminal (c : Cell) : Prop := c.bits.size = 0 ∧ c.refs.size = 0

/-- The action `a` is in the action list `c5`: some node before the end of the list parses as `a`. -/
def ActionIn (c5 : Cell) (a : OutAction) : Prop :=
  ∃ i, (∀ j ≤ i, ¬Terminal (actionNode c5 j)) ∧ parseOutAction (actionNode c5 i) = some a

/-- The code after the action phase of the action list `c5`, if the code before was `old`: `old` if
the list has no `SETCODE` action (`action_set_code`), else the code of one of them. -/
def NewCode (c5 : Cell) (old new : Option Cell) : Prop :=
  (new = old ∧ ∀ c, ¬ActionIn c5 (.setCode c)) ∨ ∃ c, new = some c ∧ ActionIn c5 (.setCode c)

/-- What the action phase leaves: see the module docstring. -/
def ActionResult (t₀ u : Tx) : Prop :=
  t₀.Fixed u ∧ t₀.AddrKeep u ∧ u.inMsgState = t₀.inMsgState ∧ u.useMsgState = t₀.useMsgState ∧
    u.wasActivated = t₀.wasActivated ∧
    (u.accStatus = t₀.accStatus ∨ u.accStatus = .deleted ∨ u.accStatus = .uninit) ∧
    ((u.newCode = t₀.newCode ∧ u.newData = t₀.newData) ∨
      (∃ c5, t₀.computePhase.actions = some c5 ∧ u.newData = t₀.computePhase.newData ∧
        NewCode c5 t₀.newCode u.newCode))

/-- The nodes of the action list read so far: the first `m` nodes. -/
def NodesOK (c5 : Cell) (nodes : Array Cell) (m : Nat) : Prop :=
  nodes.toList = (List.range m).map (actionNode c5)

/-- The state of the loop that reads the action list (do notation): the early return, whether the
end was reached, the current node, the number of actions, the nodes read. -/
abbrev APState1 := MProd (Option (Option Tx)) (MProd Bool (MProd Cell (MProd Nat (Array Cell))))

/-- Invariant of the loop that reads the action list. -/
def APInv1 (c5 : Cell) (i : Nat) (b : APState1) : Prop :=
  b.1 = none ∧
  (b.2.1 = false → b.2.2.2.1 = i ∧ i ≤ 255 ∧ b.2.2.1 = actionNode c5 i ∧ NodesOK c5 b.2.2.2.2 i ∧
      ∀ j < i, ¬Terminal (actionNode c5 j)) ∧
  (b.2.1 = true → b.2.2.2.1 ≤ 255 ∧ NodesOK c5 b.2.2.2.2 (b.2.2.2.1 + 1) ∧
      (∀ j < b.2.2.2.1, ¬Terminal (actionNode c5 j)) ∧ Terminal (actionNode c5 b.2.2.2.1))

theorem actionNode_succ (c5 : Cell) (i : Nat) : actionNode c5 (i + 1) = (actionNode c5 i).refs[0]! := rfl

theorem NodesOK_push {c5 : Cell} {nodes : Array Cell} {i : Nat} (h : NodesOK c5 nodes i) :
    NodesOK c5 (nodes.push (actionNode c5 i)) (i + 1) := by
  unfold NodesOK at *
  simp [h, List.range_succ]

theorem actionNode_zero (c5 : Cell) : actionNode c5 0 = c5 := rfl

theorem NodesOK_zero (c5 : Cell) : NodesOK c5 #[] 0 := rfl

theorem getElem!_set!_self {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  rw [getElem!_pos (a.set! i v) i (by simpa [Array.set!] using h)]
  simp [Array.set!]

theorem getElem!_set!_ne {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (v : α) (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.set! i v) j (by simpa [Array.set!] using hj), getElem!_pos a j hj]
    simp only [Array.set!]
    rw [Array.getElem_setIfInBounds]
    · simp [h]
    · exact hj
  · rw [getElem!_neg (a.set! i v) j (by simpa [Array.set!] using hj), getElem!_neg a j hj]

theorem size_set! {α : Type} (a : Array α) (i : Nat) (v : α) : (a.set! i v).size = a.size := by
  simp [Array.set!]

theorem getElem!_replicate_none {α : Type} (m i : Nat) : (Array.replicate m (none : Option α))[i]! = none := by
  by_cases h : i < m
  · rw [getElem!_pos _ i (by simpa using h)]; simp
  · rw [getElem!_neg _ i (by simpa using h)]; rfl

/-- The state of the loop that parses the actions: the early return, the actions, the phase. -/
abbrev APState2 := MProd (Option (Option Tx)) (MProd (Array (Option OutAction)) ActionPhase)

/-- Invariant of the loop that parses the actions (from the first, the last node). -/
def APInv2 (nodes : Array Cell) (m k : Nat) (b : APState2) : Prop :=
  b.1 = none ∧ b.2.1.size = m ∧ (∀ i < m, m - k ≤ i → b.2.1[i]! = parseOutAction nodes[i]!) ∧
    (∀ i < m, i < m - k → b.2.1[i]! = none) ∧ b.2.2.newCode = none

theorem nodes_get {c5 : Cell} {nds : Array Cell} {n i : Nat} (h : NodesOK c5 nds n) (hi : i < n) :
    nds[i]! = actionNode c5 i := by
  unfold NodesOK at h
  have hs : nds.size = n := by
    have := congrArg List.length h; simpa using this
  rw [getElem!_pos nds i (by omega)]
  rw [← Array.getElem_toList (h := by omega)]
  simp [h]

theorem actionIn_iff {c5 : Cell} {m : Nat} (hT : ∀ j < m, ¬Terminal (actionNode c5 j))
    (hTm : Terminal (actionNode c5 m)) (a : OutAction) :
    ActionIn c5 a ↔ ∃ i < m, parseOutAction (actionNode c5 i) = some a := by
  constructor
  · rintro ⟨i, hi, hp⟩
    refine ⟨i, ?_, hp⟩
    rcases Nat.lt_or_ge i m with h | h
    · exact h
    · exact absurd hTm (hi m h)
  · rintro ⟨i, hi, hp⟩
    exact ⟨i, fun j hj => hT j (by omega), hp⟩

/-- The fields of a transaction `ActionResult` keeps as they were. -/
def ARview (t : Tx) :=
  (t.account, t.kind, t.cfg, t.gv, t.globalLibs, t.inMsgState, t.useMsgState, t.wasActivated, t.myAddr,
    t.myAddrExact, t.newFixedPrefixLength)

theorem AR_fail {t₀ T u : Tx} (hT : ActKeep t₀ T) (e : ARview u = ARview T) (hs : u.accStatus = T.accStatus)
    (hc : u.newCode = t₀.newCode) (hd : u.newData = t₀.newData) : ActionResult t₀ u := by
  simp only [ARview, Prod.mk.injEq] at e
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hT
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := e
  exact ⟨⟨e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4, e5.trans h5⟩,
    ⟨e9.trans h13, e10.trans h14, e11.trans h15⟩, e6.trans h6, e7.trans h7,
    e8.trans h8, Or.inl (hs.trans h9), Or.inl ⟨hc, hd⟩⟩

theorem AR_success {t₀ T u : Tx} {c5 : Cell} (hT : ActKeep t₀ T) (e : ARview u = ARview T)
    (hs : u.accStatus = T.accStatus ∨ u.accStatus = .deleted ∨ u.accStatus = .uninit)
    (h5 : t₀.computePhase.actions = some c5) (hd : u.newData = T.computePhase.newData)
    (hnc : NewCode c5 t₀.newCode u.newCode) : ActionResult t₀ u := by
  simp only [ARview, Prod.mk.injEq] at e
  obtain ⟨⟨h1, h2, h3, h4, h5'⟩, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hT
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := e
  refine ⟨⟨e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4, e5.trans h5'⟩,
    ⟨e9.trans h13, e10.trans h14, e11.trans h15⟩, e6.trans h6, e7.trans h7,
    e8.trans h8, ?_, Or.inr ⟨c5, h5, by rw [hd, h12], hnc⟩⟩
  rcases hs with hs | hs
  · exact Or.inl (hs.trans h9)
  · exact Or.inr hs

theorem NewCode_some {c5 : Cell} {old : Option Cell} {c : Cell} (h : ActionIn c5 (.setCode c)) :
    NewCode c5 old (some c) := Or.inr ⟨c, rfl, h⟩

theorem NewCode_none {c5 : Cell} {old new : Option Cell} (h1 : new = old) (h2 : ∀ c, ¬ActionIn c5 (.setCode c)) :
    NewCode c5 old new := Or.inl ⟨h1, h2⟩

theorem none_of_forall {α : Type} {x : Option α} (h : ∀ c, x = some c → False) : x = none := by
  cases x with
  | none => rfl
  | some c => exact (h c rfl).elim

/-- The status of an account deleted by the action phase. -/
theorem status_cases (c : Bool) {T : Tx} :
    (if c then AccStatus.deleted else AccStatus.uninit) = T.accStatus ∨
      (if c then AccStatus.deleted else AccStatus.uninit) = .deleted ∨
      (if c then AccStatus.deleted else AccStatus.uninit) = .uninit := by
  cases c <;> simp

/-- The state of the loop that runs the actions: the early return, the phase, the transaction. -/
abbrev APState3 := MProd (Option (Option Tx)) (MProd ActionPhase Tx)

/-- Invariant of the loop that runs the actions (from the first, the last node). -/
def APInv3 (t₀ : Tx) (acts : Array (Option OutAction)) (m k : Nat) (b : APState3) : Prop :=
  b.1 = none ∧ ActKeep t₀ b.2.2 ∧
    (b.2.1.newCode = none → ∀ i < m, m - k ≤ i → ∀ c, acts[i]! ≠ some (.setCode c)) ∧
    (∀ c, b.2.1.newCode = some c → ∃ i < m, acts[i]! = some (.setCode c))

set_option maxHeartbeats 4000000 in
/-- **The action phase**: see the module docstring. -/
theorem actionPhaseRun_spec (t₀ : Tx) (sl : SizeLimits) :
    OKe (OKo (ActionResult t₀)) (t₀.actionPhaseRun sl) := by
  unfold Tx.actionPhaseRun
  tx_vcg
  rename_i lib c5 hc5
  refine OKe_forIn_range 257 _ _ _ _ (APInv1 c5) (fun b => ∃ r, b.1 = some r ∧ OKo (ActionResult t₀) r) ?_ ?_ ?_
  · tx_clear_values; tx_unfold [APInv1, Terminal]; (try dsimp only at *); grind [NodesOK_zero, actionNode_zero]
  · tx_compact
    intro i b hi hI
    tx_vcg
    all_goals first
      | tx_solve
      | (tx_clear_values; tx_unfold [APInv1, Terminal]; (try dsimp only at *); grind [NodesOK_push, actionNode_succ])
  intro b hb
  tx_vcg
  rotate_left
  · tx_clear_values; tx_unfold [APInv1]; grind
  rename_i _ dn ls m nds hsnd _ hfst
  have hL : NodesOK c5 nds (m + 1) ∧ (∀ j < m, ¬Terminal (actionNode c5 j)) ∧ Terminal (actionNode c5 m) := by
    tx_clear_values; tx_unfold [APInv1]; grind
  clear hb
  refine OKe_forIn_range m _ _ _ _ (APInv2 nds m) (fun b => ∃ r, b.1 = some r ∧ OKo (ActionResult t₀) r) ?_ ?_ ?_
  · tx_prep [ActionPhase.newCode] [APInv2]; (try dsimp only at *); grind [getElem!_replicate_none]
  · tx_compact
    intro k b hk hI
    tx_vcg
    all_goals first
      | tx_solve
      | (tx_prep [ActionPhase.newCode] [APInv2]; (try dsimp only at *); grind [getElem!_set!_self, getElem!_set!_ne, size_set!])
  intro b hb
  tx_vcg
  rotate_left
  · tx_clear_values; tx_unfold [APInv2]; grind
  rename_i _ hfst
  have hA : p.1.size = m ∧ (∀ i < m, p.1[i]! = parseOutAction nds[i]!) ∧ p.2.newCode = none := by
    tx_clear_values; tx_unfold [APInv2]; grind
  clear hb
  refine OKe_forIn_range m _ _ _ _ (APInv3 t₀ p.1 m) (fun b => ∃ r, b.1 = some r ∧ OKo (ActionResult t₀) r)
    ?_ ?_ ?_
  · tx_prep [ActionPhase.newCode] [APInv3, ActKeep, Tx.Fixed, Tx.AddrKeep]; (try dsimp only at *); grind
  · tx_compact
    intro k b hk hI
    tx_vcg
    all_goals try tx_specs [actionSetCode_spec, actionChangeLibrary_spec, actionReserve_spec, actionSendMsg_spec]
    all_goals
      tx_prep [ActionPhase.newCode, Tx.account, Tx.kind, Tx.cfg, Tx.gv, Tx.globalLibs, Tx.inMsgState,
        Tx.accStatus, Tx.newCode, Tx.newData, Tx.useMsgState, Tx.wasActivated, Tx.computePhase, Tx.myAddr,
        Tx.myAddrExact, Tx.newFixedPrefixLength]
        [APInv3, ActKeep, Tx.Fixed, Tx.AddrKeep, ActionResult, NewCode, OKo]
      (try dsimp only at *)
      grind
  intro b hb
  rcases hbn : b.1 with _ | r
  · have h3 : APInv3 t₀ p.1 m m b := by
      rcases hb with h | ⟨r, hr, _⟩
      · exact h
      · rw [hbn] at hr; cases hr
    obtain ⟨_, hK, hN, hS⟩ := h3
    obtain ⟨hNodes, hT, hTm⟩ := hL
    obtain ⟨_, hpa, _⟩ := hA
    have hN' : b.2.1.newCode = none → ∀ c, ¬ActionIn c5 (.setCode c) := by
      intro hn c hin
      rw [actionIn_iff hT hTm] at hin
      obtain ⟨i, hi, hp⟩ := hin
      exact hN hn i hi (by omega) c (by rw [hpa i hi, nodes_get hNodes (by omega)]; exact hp)
    have hS' : ∀ c, b.2.1.newCode = some c → ActionIn c5 (.setCode c) := by
      intro c hc
      obtain ⟨i, hi, hai⟩ := hS c hc
      rw [actionIn_iff hT hTm]
      exact ⟨i, hi, by rw [← nodes_get hNodes (by omega), ← hpa i hi]; exact hai⟩
    clear hb hN hS hpa hNodes hT hTm
    tx_vcg
    all_goals first
      | exact AR_fail hK rfl rfl rfl rfl
      | exact AR_success hK rfl (Or.inl rfl) hc5 rfl (NewCode_some (hS' _ ‹_›))
      | exact AR_success hK rfl (Or.inl rfl) hc5 rfl (NewCode_none hK.2.2.2.2.2.1 (hN' ‹_›))
      | exact AR_success hK rfl (status_cases _) hc5 rfl (NewCode_some (hS' _ ‹_›))
      | exact AR_success hK rfl (status_cases _) hc5 rfl (NewCode_none hK.2.2.2.2.2.1 (hN' ‹_›))
      | exact AR_success hK rfl (Or.inl rfl) hc5 rfl (NewCode_none hK.2.2.2.2.2.1 (hN' (none_of_forall ‹_›)))
      | exact AR_success hK rfl (status_cases _) hc5 rfl (NewCode_none hK.2.2.2.2.2.1 (hN' (none_of_forall ‹_›)))
  · rcases hb with h | ⟨r', hr', hok⟩
    · exact absurd (hbn.symm.trans h.1) (by simp)
    · rw [hbn] at hr'
      cases hr'
      simp only
      exact hok

end TvmLean.Tx

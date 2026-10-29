import TvmLean.Proofs.Exec.Spec.Actions

/-!
# Specification: `SENDMSG`

`SENDMSG` (C++ `exec_send_message`, tonops.cpp:2121-2357; the model's handler
`execInstrMsgSendMsg`, TvmLean/Semantics/Exec/Msg/SendMsg.lean) parses the message, reads the prices
and size limits of the configuration in `c7`, counts the cells below the message's root (loading
them), computes the forwarding and IHR fees (as `td::uint64`s, with the global-version branches of
the model), pushes their sum, and, unless the mode has the flag 1024 (estimate only), installs the
action `action_send_msg` (`OutAction.sendMsg mode c5 msg`, the cell of `SENDRAWMSG`). The fee is a
function of the message and of the configuration that symbolic execution does not evaluate:
`sendMsgRun st` is the handler's run from `st`, a term, and the fee `sendMsgFee st` the integer it
pushes.

`Spec.sendMsg` states the run on the stack `s msg mode` (the mode in `0..2047`): it succeeds or
raises an exception as `sendMsgRun st` does; on success the stack is `s` with the fee pushed and `c5`
is the action added to `c5` (the old `c5` with the flag 1024); on an exception the registers are
unchanged. All the other parts of the state but the gas and the loads (the loaded cells and
libraries, the refusals of libraries noted) are unchanged. This rests on the frame of the handler
(`sendMsg_end`): its steps before the result change only the gas and the loads
(`VM.KeepsLoads`), the last ones push the fee and install the action; proved a join point at a
time, as `execInstrMsgSendMsg_WF` (TvmLean/Proofs/WF/Exec/Msg.lean) proves that it keeps states
well-formed.
-/

namespace TvmLean

/-- The parts of the state that the steps of `SENDMSG` before its result change neither: all but
the stack, the registers, the gas and the loads (cells, libraries, refused libraries noted); the
refused libraries noted too without `max_library_loads` (none is refused then). -/
def VmState.sendMsgFixed (st : VmState) :=
  (st.cc, st.cp, st.chksgnCounter, st.libraries, st.callStack, st.cstate, st.maxDataDepth,
    st.globalVersion, st.freeGasConsumed, st.getExtraBalanceCounter, st.chainJumps, st.steps,
    st.maxLibraryLoads, st.librariesRefused,
    (match st.maxLibraryLoads with
      | none => some st.librariesMissed
      | some _ => none))

/-- The limit of library loads is among the fixed parts. -/
theorem VmState.maxLibraryLoads_of_sendMsgFixed {a b : VmState} (h : a.sendMsgFixed = b.sendMsgFixed) :
    a.maxLibraryLoads = b.maxLibraryLoads := by
  simp only [VmState.sendMsgFixed, Prod.mk.injEq] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `m` changes only the gas and the loads of the state: from any state, its run ends with the same
stack, registers and `VmState.sendMsgFixed`, normally or by an exception. -/
def VM.KeepsLoads {α : Type} (m : VM α) : Prop :=
  ∀ st, (ExceptT.run m st).2.stack = st.stack ∧ (ExceptT.run m st).2.regs = st.regs ∧
    (ExceptT.run m st).2.sendMsgFixed = st.sendMsgFixed

namespace VM.KeepsLoads

theorem bind {α β : Type} {x : VM α} {f : α → VM β} (hx : VM.KeepsLoads x) (hf : ∀ a, VM.KeepsLoads (f a)) :
    VM.KeepsLoads (x >>= f) := by
  intro st
  rw [VM.run_bind]
  obtain ⟨h1, h2, h3⟩ := hx st
  rcases hr : ExceptT.run x st with ⟨r, st1⟩
  rw [hr] at h1 h2 h3
  cases r with
  | ok a =>
    obtain ⟨g1, g2, g3⟩ := hf a st1
    simp only [VM.bindRes_ok]
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
  | error e =>
    simp only [VM.bindRes_error]
    exact ⟨h1, h2, h3⟩

theorem pure' {α : Type} (a : α) : VM.KeepsLoads (pure a : VM α) := fun _ => ⟨rfl, rfl, rfl⟩

theorem throw' {α : Type} (e : Excno) : VM.KeepsLoads (throw e : VM α) := fun _ => ⟨rfl, rfl, rfl⟩

theorem get' : VM.KeepsLoads (get : VM VmState) := fun _ => ⟨rfl, rfl, rfl⟩

theorem ite' {α : Type} {c : Prop} [Decidable c] {a b : VM α} (ha : VM.KeepsLoads a) (hb : VM.KeepsLoads b) :
    VM.KeepsLoads (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- A loop over a list whose every step keeps the loads. -/
theorem forIn_list {α β : Type} (l : List α) (init : β) {f : α → β → VM (ForInStep β)}
    (hf : ∀ a b, VM.KeepsLoads (f a b)) : VM.KeepsLoads (forIn l init f) := by
  induction l generalizing init with
  | nil => exact pure' _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine bind (hf a init) fun r => ?_
    cases r with
    | done b => exact pure' _
    | yield b => exact ih b

/-- A loop over an array whose every step keeps the loads. -/
theorem forIn_array {α β : Type} (a : Array α) (init : β) {f : α → β → VM (ForInStep β)}
    (hf : ∀ a b, VM.KeepsLoads (f a b)) : VM.KeepsLoads (forIn a init f) := by
  rw [← Array.forIn_toList]
  exact forIn_list _ _ hf

end VM.KeepsLoads

/-- `m` changes only the gas and the loads: by its binds, `if`s, `match`es and `let`s down to
`pure`, `throw`, `get` and the loads. -/
macro "keeps_loads" : tactic => `(tactic| repeat' (first
  | exact VM.KeepsLoads.pure' _
  | exact VM.KeepsLoads.throw' _
  | exact VM.KeepsLoads.get'
  | exact VM.registerCellLoad_keepsLoads _
  | exact VM.registerCellLoadSpecial_keepsLoads _
  | exact VM.loadCellSlice_keepsLoads _
  | apply_assumption
  | (refine VM.KeepsLoads.ite' ?_ ?_)
  | (refine VM.KeepsLoads.bind ?_ fun _ => ?_)
  | split
  | dsimp only))

/-! ## The loads keep the rest of the state -/

theorem VmState.registerCellLoad_keeps (st : VmState) (c : Cell) :
    (st.registerCellLoad c).stack = st.stack ∧ (st.registerCellLoad c).regs = st.regs ∧
      (st.registerCellLoad c).sendMsgFixed = st.sendMsgFixed := by
  cases h : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [VmState.registerCellLoad, VmState.consumeGas, h, VmState.sendMsgFixed]

theorem VmState.admitLibrary_keeps (st : VmState) (h : BitString) :
    (st.admitLibrary h).1.stack = st.stack ∧ (st.admitLibrary h).1.regs = st.regs ∧
      (st.admitLibrary h).1.sendMsgFixed = st.sendMsgFixed := by
  unfold VmState.admitLibrary
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩

theorem VmState.registerLibraryLoad_keeps (st : VmState) (h : BitString) :
    (st.registerLibraryLoad h).stack = st.stack ∧ (st.registerLibraryLoad h).regs = st.regs ∧
      (st.registerLibraryLoad h).sendMsgFixed = st.sendMsgFixed := by
  have hk := st.admitLibrary_keeps h
  have hn : st.maxLibraryLoads = none → (st.admitLibrary h).2 = false := by
    intro hm
    unfold VmState.admitLibrary
    rw [hm]
  unfold VmState.registerLibraryLoad
  generalize st.admitLibrary h = p at hk hn ⊢
  obtain ⟨st', b⟩ := p
  dsimp only at hk hn ⊢
  split
  · -- a refusal noted: `max_library_loads` is set
    rename_i hb
    obtain ⟨h1, h2, h3⟩ := hk
    refine ⟨h1, h2, ?_⟩
    rw [← h3]
    have hm : st'.maxLibraryLoads ≠ none := by
      rw [VmState.maxLibraryLoads_of_sendMsgFixed h3]
      intro hm
      rw [hn hm] at hb
      simp at hb
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hm
    simp only [VmState.sendMsgFixed, hk]
  · exact hk

theorem VmState.registerCellLoads_keeps (st : VmState) (l : List LibraryLoadStep) :
    (st.registerCellLoads l).1.stack = st.stack ∧ (st.registerCellLoads l).1.regs = st.regs ∧
      (st.registerCellLoads l).1.sendMsgFixed = st.sendMsgFixed := by
  induction l generalizing st with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x l ih =>
    cases x with
    | cell c =>
      simp only [VmState.registerCellLoads]
      obtain ⟨h1, h2, h3⟩ := st.registerCellLoad_keeps c
      split
      · exact ⟨h1, h2, h3⟩
      · obtain ⟨g1, g2, g3⟩ := ih (st.registerCellLoad c)
        exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
    | library h =>
      simp only [VmState.registerCellLoads]
      obtain ⟨h1, h2, h3⟩ := st.registerLibraryLoad_keeps h
      obtain ⟨g1, g2, g3⟩ := ih (st.registerLibraryLoad h)
      exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩

theorem VM.registerCellLoad_keepsLoads (c : Cell) : VM.KeepsLoads (VM.registerCellLoad c) := by
  intro st
  have hk := st.registerCellLoads_keeps (.cell c :: (st.libraryLoads c).toList)
  unfold VM.registerCellLoad
  simp only [VM.run_bind, VM.run_get, VM.bindRes_ok]
  generalize st.registerCellLoads (.cell c :: (st.libraryLoads c).toList) = p at hk ⊢
  obtain ⟨st', ex⟩ := p
  cases ex <;> simpa [VM.run_bind, VM.run_set, VM.bindRes_ok, VM.run_ite, VM.run_throw, VM.run_pure] using hk

theorem VM.registerCellLoadSpecial_keepsLoads (c : Cell) : VM.KeepsLoads (VM.registerCellLoadSpecial c) := by
  intro st
  have hk := st.registerCellLoad_keeps c
  unfold VM.registerCellLoadSpecial
  simp only [VM.run_bind, VM.run_modify, VM.bindRes_ok, VM.run_get]
  split <;> simpa [VM.run_throw, VM.run_pure] using hk

theorem VM.loadCellSlice_keepsLoads (c : Cell) : VM.KeepsLoads (VM.loadCellSlice c) := by
  unfold VM.loadCellSlice
  refine VM.KeepsLoads.bind (VM.registerCellLoad_keepsLoads c) fun _ => ?_
  keeps_loads

theorem VM.cellResolver_keepsLoads : VM.KeepsLoads VM.cellResolver := by
  unfold VM.cellResolver
  exact VM.KeepsLoads.bind VM.KeepsLoads.get' fun _ => VM.KeepsLoads.pure' _

theorem VM.getUnpackedConfigTuple_keepsLoads : VM.KeepsLoads VM.getUnpackedConfigTuple := by
  unfold VM.getUnpackedConfigTuple
  keeps_loads

/-- C++ `VmStorageStat::add_storage` on the cells of a message: only gas and loads change. -/
theorem VM.countMsgCells_keepsLoads (maxCells : Nat) (todo : Array Cell) (seen : Array (Array UInt8))
    (cells bits : Nat) : VM.KeepsLoads (VM.countMsgCells maxCells todo seen cells bits) := by
  induction todo, seen, cells, bits using VM.countMsgCells.induct maxCells with
  | case1 todo seen cells bits h c todo' hsh hnew ih =>
    rw [VM.countMsgCells, dif_pos h]
    dsimp only at hnew ih ⊢
    rw [if_pos hnew]
    exact VM.KeepsLoads.bind (VM.registerCellLoadSpecial_keepsLoads _) fun _ => ih
  | case2 todo seen cells bits h c todo' hsh hnew ih =>
    rw [VM.countMsgCells, dif_pos h]
    dsimp only at hnew ih ⊢
    rw [if_neg hnew]
    exact ih
  | case3 todo seen cells bits h =>
    rw [VM.countMsgCells, dif_neg h]
    exact VM.KeepsLoads.pure' _

/-! ## The run of `SENDMSG`, a join point at a time -/

/-- What `SENDMSG` leaves, from the state `st0` (its registers and fixed parts), the stack `s`
below the message and the mode: the fixed parts kept; on success the fee pushed on `s` and, if it
sends, the action `OutAction.sendMsg mode c5 msg` in `c5`; on an exception the registers. -/
def sendMsgEnd (msg : Cell) (mode : Nat) (send : Bool) (s : Stack) (st0 : VmState)
    (r : Except Excno Unit × VmState) : Prop :=
  r.2.sendMsgFixed = st0.sendMsgFixed ∧
  match r.1 with
  | .ok _ => (∃ fee : Int, r.2.stack = s.push (.int (.num fee))) ∧
      r.2.regs = { st0.regs with c5 := if send then OutAction.sendMsg mode st0.regs.c5 msg else st0.regs.c5 }
  | .error _ => r.2.regs = st0.regs

/-- From every state whose stack satisfies `pre`, the run of `m` ends as `SENDMSG` does
(`sendMsgEnd`, the registers and fixed parts those of the state). -/
def VM.EndsSendMsg (msg : Cell) (mode : Nat) (send : Bool) (s : Stack) (pre : Stack → Prop) (m : VM Unit) :
    Prop :=
  ∀ st, pre st.stack → sendMsgEnd msg mode send s st (ExceptT.run m st)

namespace VM.EndsSendMsg

variable {msg : Cell} {mode : Nat} {send : Bool} {s : Stack} {pre : Stack → Prop}

/-- A step that changes only the gas and the loads, then the rest. -/
theorem bind {α : Type} {x : VM α} {f : α → VM Unit} (hx : VM.KeepsLoads x)
    (hf : ∀ a, VM.EndsSendMsg msg mode send s pre (f a)) : VM.EndsSendMsg msg mode send s pre (x >>= f) := by
  intro st hp
  rw [VM.run_bind]
  obtain ⟨h1, h2, h3⟩ := hx st
  rcases hr : ExceptT.run x st with ⟨r, st1⟩
  rw [hr] at h1 h2 h3
  cases r with
  | ok a =>
    simp only [VM.bindRes_ok]
    have := hf a st1 (by rw [h1]; exact hp)
    unfold sendMsgEnd at this ⊢
    rw [h2, h3] at this
    exact this
  | error e =>
    simp only [VM.bindRes_error]
    exact ⟨h3, h2⟩

theorem throw' (e : Excno) : VM.EndsSendMsg msg mode send s pre (throw e) := fun _ _ => ⟨rfl, rfl⟩

/-- A jump to a join point after a value: `pure a >>= jp`. -/
theorem pure_bind {α : Type} (a : α) {f : α → VM Unit} (hf : VM.EndsSendMsg msg mode send s pre (f a)) :
    VM.EndsSendMsg msg mode send s pre (pure a >>= f) := by
  intro st hp
  rw [VM.run_bind, VM.run_pure, VM.bindRes_ok]
  exact hf st hp

/-- `VM.checkUnderflow 2` on a stack of two values or more. -/
theorem checkUnderflow2 {s' : Stack} {a b : Value} {f : PUnit → VM Unit}
    (hf : VM.EndsSendMsg msg mode send s (· = (s'.push a).push b) (f ())) :
    VM.EndsSendMsg msg mode send s (· = (s'.push a).push b) (VM.checkUnderflow 2 >>= f) := by
  intro st hp
  rw [VM.run_bind, VM.run_checkUnderflow]
  have : ¬ st.stack.size < 2 := by rw [hp]; simp
  rw [if_neg this, VM.bindRes_ok]
  exact hf st hp

/-- `VM.popNatUpTo 2047` of an integer in range on top of the stack. -/
theorem popNatUpTo2047 {s' : Stack} {m : Int} (hm : 0 ≤ m ∧ m ≤ 2047) {f : Nat → VM Unit}
    (hf : VM.EndsSendMsg msg mode send s (· = s') (f m.toNat)) :
    VM.EndsSendMsg msg mode send s (· = s'.push (.int (.num m))) (VM.popNatUpTo 2047 >>= f) := by
  intro st hp
  have h1 : ¬ m < 0 := by omega
  have h2 : ¬ m.toNat > 2047 := by omega
  have hrun : ExceptT.run (VM.popNatUpTo 2047) st = (.ok m.toNat, { st with stack := s' }) := by
    unfold VM.popNatUpTo
    simp only [VM.run_bind, VM.run_popInt, hp, Array.size_push, Nat.zero_lt_succ, dif_pos,
      VM.back_push, Array.pop_push, VM.bindRes_ok, h1, h2, if_false, VM.run_pure]
  rw [VM.run_bind, hrun, VM.bindRes_ok]
  exact hf _ rfl

/-- `VM.popCell` of a cell on top of the stack. -/
theorem popCell' {s' : Stack} {c : Cell} {f : Cell → VM Unit}
    (hf : VM.EndsSendMsg msg mode send s (· = s') (f c)) :
    VM.EndsSendMsg msg mode send s (· = s'.push (.cell c)) (VM.popCell >>= f) := by
  intro st hp
  have hrun : ExceptT.run VM.popCell st = (.ok c, { st with stack := s' }) := by
    simp only [VM.run_popCell, hp, Array.size_push, Nat.zero_lt_succ, dif_pos, VM.back_push, Array.pop_push]
  rw [VM.run_bind, hrun, VM.bindRes_ok]
  exact hf _ rfl

/-- A jump to a join point whose specification is `h`, or a `throw` (a leaf of the handler). -/
macro "ends_leaf " h:term : tactic => `(tactic|
  first
    | exact VM.EndsSendMsg.throw' _
    | exact VM.EndsSendMsg.bind (VM.KeepsLoads.throw' _) fun a => $h a
    | exact VM.EndsSendMsg.pure_bind _ ($h _)
    | exact $h _)

end VM.EndsSendMsg

set_option maxHeartbeats 4000000 in
/-- **The frame of `SENDMSG`** (C++ `exec_send_message`) on the stack `s msg m`, the mode `m` in
`0..2047`: a join point at a time, as `execInstrMsgSendMsg_WF`. Its steps before the result change
only the gas and the loads; then the fee is pushed and, if it sends, the action installed. -/
theorem sendMsg_end (next : VM Unit) (s : Stack) (msg : Cell) (m : Int) (hm : 0 ≤ m ∧ m ≤ 2047) :
    VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = (s.push (.cell msg)).push (.int (.num m))) (execInstrMsgSendMsg (.tonEnvOp .sendMsg) next) := by
  simp (config := { zeta := false }) only [execInstrMsgSendMsg]
  refine VM.EndsSendMsg.checkUnderflow2 ?_
  refine VM.EndsSendMsg.popNatUpTo2047 hm ?_
  dsimp (config := { zeta := false }) only
  extract_lets -underBinder +onlyGivenNames send mode jpA
  have hjpA : ∀ y, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s.push (.cell msg)) (jpA y) := ?jpA
  · clear_value jpA
    split <;> ends_leaf hjpA
  -- the message and its parse
  intro y
  unfold jpA
  refine VM.EndsSendMsg.popCell' ?_
  dsimp (config := { zeta := false }) only
  refine VM.EndsSendMsg.bind (VM.loadCellSlice_keepsLoads _) fun _ => ?_
  extract_lets -underBinder +onlyGivenNames msgRoot getParam parseAddrWorkchain jpB
  have hgp : ∀ idx, VM.KeepsLoads (getParam idx) := by
    intro idx
    unfold getParam
    keeps_loads
  have hpaw : ∀ cs, VM.KeepsLoads (parseAddrWorkchain cs) := by
    intro cs
    unfold parseAddrWorkchain
    keeps_loads
  have hjpB : ∀ p, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s) (jpB p) := ?jpB
  · clear_value jpB
    split <;> ends_leaf hjpB
  -- its addresses
  intro parsedMsg
  unfold jpB
  refine VM.EndsSendMsg.bind (hgp 8) fun _ => ?_
  extract_lets -underBinder +onlyGivenNames jpC
  have hjpC : ∀ myAddr, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s) (jpC myAddr) := ?jpC
  · clear_value jpC
    split <;> ends_leaf hjpC
  intro myAddr
  unfold jpC
  refine VM.EndsSendMsg.bind (hpaw myAddr) fun _ => ?_
  extract_lets -underBinder +onlyGivenNames jpD
  have hjpD : ∀ destWc, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s) (jpD destWc) := ?jpD
  · clear_value jpD
    split
    · ends_leaf hjpD
    · exact VM.EndsSendMsg.bind (hpaw _) fun a => hjpD a
  -- the prices
  intro destWc
  unfold jpD
  extract_lets -underBinder +onlyGivenNames isMasterchain
  refine VM.EndsSendMsg.bind VM.KeepsLoads.get' fun _ => ?_
  extract_lets -underBinder +onlyGivenNames gv jpE
  have hjpE : ∀ pricesCs, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s) (jpE pricesCs) := ?jpE
  · clear_value jpE
    split
    · refine VM.EndsSendMsg.bind VM.getUnpackedConfigTuple_keepsLoads fun _ => ?_
      extract_lets -underBinder +onlyGivenNames pricesIdx
      split <;> ends_leaf hjpE
    · refine VM.EndsSendMsg.bind (hgp 9) fun _ => ?_
      extract_lets -underBinder +onlyGivenNames configRoot keyBits
      refine VM.EndsSendMsg.bind VM.cellResolver_keepsLoads fun _ => ?_
      extract_lets -underBinder +onlyGivenNames jpE'
      have hjpE' : ∀ p, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
          (· = s) (jpE' p) := ?jpE'
      · clear_value jpE'
        have hloads : ∀ cells : Array Cell, VM.KeepsLoads (forIn cells PUnit.unit fun c _ => do
            VM.registerCellLoad c
            pure (ForInStep.yield PUnit.unit)) := by
          intro cells
          exact VM.KeepsLoads.forIn_array _ _ fun c _ =>
            VM.KeepsLoads.bind (VM.registerCellLoad_keepsLoads c) fun _ => VM.KeepsLoads.pure' _
        split
        · refine VM.EndsSendMsg.bind VM.cellResolver_keepsLoads fun _ => ?_
          refine VM.EndsSendMsg.bind (hloads _) fun _ => ?_
          ends_leaf hjpE'
        · refine VM.EndsSendMsg.bind (hloads _) fun _ => ?_
          ends_leaf hjpE'
        · refine VM.EndsSendMsg.bind (hloads _) fun _ => ?_
          split <;> ends_leaf hjpE'
      intro p
      unfold jpE'
      split
      · exact VM.EndsSendMsg.bind (VM.loadCellSlice_keepsLoads _) fun a => hjpE a
      · ends_leaf hjpE
  intro pricesCs
  unfold jpE
  extract_lets -underBinder +onlyGivenNames jpF
  have hjpF : ∀ p, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s) (jpF p) := ?jpF
  · clear_value jpF
    split <;> ends_leaf hjpF
  -- the size limits and the cells of the message
  intro p
  unfold jpF
  extract_lets -underBinder +onlyGivenNames jpG
  have hjpG : ∀ maxCells, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s) (jpG maxCells) := ?jpG
  · clear_value jpG
    split
    · refine VM.EndsSendMsg.bind VM.getUnpackedConfigTuple_keepsLoads fun _ => ?_
      split
      · ends_leaf hjpG
      · split <;> ends_leaf hjpG
      · ends_leaf hjpG
    · ends_leaf hjpG
  intro maxCells
  unfold jpG
  refine VM.EndsSendMsg.bind (VM.loadCellSlice_keepsLoads _) fun _ => ?_
  extract_lets -underBinder +onlyGivenNames msgRoot' refStart todo0
  refine VM.EndsSendMsg.bind (VM.countMsgCells_keepsLoads _ _ _ _ _) fun _ => ?_
  extract_lets -underBinder +onlyGivenNames extraOf jpH
  have hextraOf : ∀ t, VM.KeepsLoads (extraOf t) := by
    intro t
    unfold extraOf
    keeps_loads
  have hjpH : ∀ ve, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s) (jpH ve) := ?jpH
  · clear_value jpH
    split
    · ends_leaf hjpH
    · split
      · refine VM.EndsSendMsg.bind (hgp 7) fun _ => ?_
        split
        · split
          · split
            · exact VM.EndsSendMsg.bind (hextraOf _) fun _ =>
                VM.EndsSendMsg.pure_bind _ (hjpH _)
            · ends_leaf hjpH
            · ends_leaf hjpH
          · ends_leaf hjpH
        · ends_leaf hjpH
      · split
        · refine VM.EndsSendMsg.bind (hgp 11) fun _ => ?_
          split
          · split
            · split
              · exact VM.EndsSendMsg.bind (hextraOf _) fun _ =>
                  VM.EndsSendMsg.pure_bind _ (hjpH _)
              · ends_leaf hjpH
              · ends_leaf hjpH
            · ends_leaf hjpH
          · ends_leaf hjpH
        · ends_leaf hjpH
  -- the fees and the root of the message
  intro ve
  unfold jpH
  extract_lets -underBinder +onlyGivenNames storedGramsLenBits ihrDisabled computeFees cellsI bitsI
  have hsgl : ∀ x, VM.KeepsLoads (storedGramsLenBits x) := by
    intro x
    unfold storedGramsLenBits
    keeps_loads
  extract_lets -underBinder +onlyGivenNames fwdFee ihrFee msgRootBits msgRootRefs initRef bodyRef jpI
  have hmrb : ∀ a b c d, VM.KeepsLoads (msgRootBits a b c d) := by
    intro a b c d
    unfold msgRootBits
    keeps_loads
  have hjpI : ∀ a b c d e f y, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s) (jpI a b c d e f y) := ?jpI
  · clear_value jpI
    split
    · refine VM.EndsSendMsg.bind (hmrb _ _ _ _) fun _ => ?_
      extract_lets -underBinder +onlyGivenNames rr
      split
      · extract_lets -underBinder +onlyGivenNames initRef' cellsI' bitsI'
        extract_lets -underBinder +onlyGivenNames fwdFee' ihrFee'
        ends_leaf (hjpI _ _ _ _ _ _)
      · ends_leaf (hjpI _ _ _ _ _ _)
    · ends_leaf (hjpI _ _ _ _ _ _)
  intro a b c d e f y
  unfold jpI
  extract_lets -underBinder +onlyGivenNames jpJ
  have hjpJ : ∀ a b c d e y, VM.EndsSendMsg msg (m.toNat &&& 0x3ff) (decide ((m.toNat &&& 1024) = 0)) s
      (· = s) (jpJ a b c d e y) := ?jpJ
  · clear_value jpJ
    split
    · refine VM.EndsSendMsg.bind (hmrb _ _ _ _) fun _ => ?_
      extract_lets -underBinder +onlyGivenNames rr
      split
      · extract_lets -underBinder +onlyGivenNames bodyRef' cellsI' bitsI'
        extract_lets -underBinder +onlyGivenNames fwdFee' ihrFee'
        ends_leaf (hjpJ _ _ _ _ _)
      · ends_leaf (hjpJ _ _ _ _ _)
    · ends_leaf (hjpJ _ _ _ _ _)
  -- the fee pushed and the action installed
  intro a b c d e y
  unfold jpJ
  intro st hp
  rw [VM.run_bind, VM.run_pushIntQuiet]
  by_cases hfit : (IntVal.num (d + e)).signedFits257 = true
  · rw [if_pos hfit, VM.bindRes_ok]
    by_cases hs : send = true
    · have hs' : decide ((m.toNat &&& 1024) = 0) = true := hs
      rw [if_pos hs]
      simp only [VM.run_bind, VM.run_modify, VM.bindRes_ok, VM.run_get, VM.checkNewCellDepth, VM.run_ite,
        VM.run_throw, VM.run_pure]
      split
      · exact ⟨rfl, rfl⟩
      · simp only [VM.bindRes_ok, VM.run_set]
        refine ⟨rfl, ⟨⟨d + e, by simp only [VmState.consumeGas, hp]⟩, ?_⟩⟩
        simp only [hs', if_true]
        rfl
    · have hs' : decide ((m.toNat &&& 1024) = 0) = false := Bool.eq_false_iff.mpr hs
      rw [if_neg hs]
      simp only [VM.run_pure]
      refine ⟨rfl, ⟨⟨d + e, by simp only [hp]⟩, ?_⟩⟩
      simp only [hs', Bool.false_eq_true, if_false]
  · rw [if_neg hfit]
    simp only [Bool.false_eq_true, if_false, VM.bindRes_error]
    exact ⟨rfl, rfl⟩

/-! ## The specification -/

/-- A state is `st` but for its stack, registers, gas and loads if their fixed parts agree. -/
theorem VmState.eq_of_sendMsgFixed {st st' : VmState} (h : st'.sendMsgFixed = st.sendMsgFixed) :
    st' =
      { st with stack := st'.stack, regs := st'.regs, gas := st'.gas, loadedCells := st'.loadedCells,
                loadedLibraries := st'.loadedLibraries, librariesMissed := st'.librariesMissed } := by
  cases st
  cases st'
  simp only [VmState.sendMsgFixed, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := h
  rfl

/-- The run of the handler of `SENDMSG` from `st` (C++ `exec_send_message`): a term, which symbolic
execution does not compute. -/
@[irreducible] def sendMsgRun (st : VmState) : Except Excno Unit × VmState :=
  ExceptT.run (execInstrMsgSendMsg (.tonEnvOp .sendMsg) (pure ())) st

/-- The fee `SENDMSG` pushes from `st` (the forwarding and IHR fees, `sendMsgFwdFee`, `sendMsgIhrFee`
of the model's handler): the integer on top of the stack its run leaves. -/
def sendMsgFee (st : VmState) : Int :=
  match (sendMsgRun st).2.stack.back? with
  | some (.int (.num f)) => f
  | _ => 0

/-- `SENDMSG` runs its handler (the chain of dispatchers of `execInstr` passes it on). -/
theorem execInstr_sendMsg (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .sendMsg)) st = sendMsgRun st := by
  unfold sendMsgRun
  simp only [TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok]

/-- The result of `SENDMSG` from `st` on the stack `s msg m`, its run being `sendMsgRun st`, with
the refusals of libraries noted `missed`: on success the fee pushed on `s` and, without the flag 1024,
the action added to `c5`; on an exception the stack the run leaves; the gas and the loads the run
gives, the rest of `st` kept. -/
@[vm_run] def sendMsgResult (st : VmState) (s : Stack) (msg : Cell) (m : Int) (missed : Array BitString) :
    Except Excno Unit × VmState :=
  match (sendMsgRun st).1 with
  | .ok _ => (.ok (), { st with
      stack := s.push (.int (.num (sendMsgFee st)))
      regs := { st.regs with
        c5 := if (m.toNat &&& 1024) = 0 then OutAction.sendMsg (m.toNat &&& 1023) st.regs.c5 msg else st.regs.c5 }
      gas := (sendMsgRun st).2.gas
      loadedCells := (sendMsgRun st).2.loadedCells
      loadedLibraries := (sendMsgRun st).2.loadedLibraries
      librariesMissed := missed })
  | .error e => (.error e, { st with
      stack := (sendMsgRun st).2.stack
      gas := (sendMsgRun st).2.gas
      loadedCells := (sendMsgRun st).2.loadedCells
      loadedLibraries := (sendMsgRun st).2.loadedLibraries
      librariesMissed := missed })

namespace Spec

/-- **`SENDMSG`** (C++ `exec_send_message`, tonops.cpp:2121-2357) on the stack `s msg m`, the mode
`m` in `0..2047`: as its run (`sendMsgRun`) it succeeds or raises an exception (`sendMsgResult`); on
success the fee (`sendMsgFee`) is pushed on `s` and, without the flag 1024 (the fee only estimated),
the action `OutAction.sendMsg (m & 1023) c5 msg` becomes `c5` (with a mode of 256 or more the run
raises range_chk); on an exception the registers are kept. The rest of the state but the gas and the
loads (loaded cells and libraries), which the run gives, is kept; the refusals of libraries noted
too without `max_library_loads` (none is refused then), else the run notes them. -/
@[vm_spec] theorem sendMsg (st : VmState) (s : Stack) (msg : Cell) (m : Int) (hm : 0 ≤ m ∧ m ≤ 2047)
    (hs : st.stack = (s.push (.cell msg)).push (.int (.num m))) :
    ExceptT.run (execInstr (.tonEnvOp .sendMsg)) st =
      if st.maxLibraryLoads.isNone then sendMsgResult st s msg m st.librariesMissed
      else sendMsgResult st s msg m (sendMsgRun st).2.librariesMissed := by
  rw [execInstr_sendMsg]
  have hend := sendMsg_end (pure ()) s msg m hm st hs
  have hrun : ExceptT.run (execInstrMsgSendMsg (.tonEnvOp .sendMsg) (pure ())) st = sendMsgRun st := by
    unfold sendMsgRun; rfl
  rw [hrun] at hend
  have hmiss : (st.maxLibraryLoads.isNone = true) → (sendMsgRun st).2.librariesMissed = st.librariesMissed := by
    intro hn
    have hfix := hend.1
    have hmll : st.maxLibraryLoads = none := Option.isNone_iff_eq_none.mp hn
    have hmll' : (sendMsgRun st).2.maxLibraryLoads = none := by
      rw [VmState.maxLibraryLoads_of_sendMsgFixed hfix, hmll]
    simp only [VmState.sendMsgFixed, Prod.mk.injEq, hmll, hmll'] at hfix
    exact Option.some.inj hfix.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hgoal : sendMsgRun st = sendMsgResult st s msg m (sendMsgRun st).2.librariesMissed := by
    unfold sendMsgResult sendMsgFee
    generalize sendMsgRun st = r at hend ⊢
    obtain ⟨res, st'⟩ := r
    unfold sendMsgEnd at hend
    dsimp only at hend ⊢
    obtain ⟨hfix, hres⟩ := hend
    have heq := VmState.eq_of_sendMsgFixed hfix
    cases res with
    | ok u =>
      cases u
      dsimp only at hres ⊢
      obtain ⟨⟨fee, hstk⟩, hregs⟩ := hres
      conv => lhs; rw [heq]
      rw [hstk, hregs]
      simp only [Array.back?_push, decide_eq_true_eq]
    | error e =>
      dsimp only at hres ⊢
      conv => lhs; rw [heq]
      rw [hres]
  by_cases hn : st.maxLibraryLoads.isNone = true
  · rw [if_pos hn, ← hmiss hn]
    exact hgoal
  · rw [if_neg hn]
    exact hgoal

end Spec

end TvmLean

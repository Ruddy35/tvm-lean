import TvmLean.Proofs.Exec.Framed
import TvmLean.Proofs.Exec.Spec.DictDel

/-!
# `DICT{I,U}GET` on any dictionary, framed

The lookup of a key in a dictionary whose cells a run does not know (a dictionary of an inbound
message: any cell, ordinary or exotic, well formed or not) is framed (`TvmLean.Framed.ExecFramed`,
`TvmLean/Proofs/Exec/Framed.lean`): it changes the stack, the gas, the loaded cells and libraries
only; it pushes the value found and `-1`, or `0`; it fails only with an exception of code 2 or
more (range_chk for the key length, cell_und or dict_err of the lookup, out of gas of the loads).

* `Framed.dictLookupWithCells_error`: the lookup of the model, with a resolver that fails only with
  cell_und (the VM's: `libraryResolveLoadsAux_error`), fails only with cell_und or dict_err;
* `Framed.Steps`: a VM computation framed with a relation between the stacks before and after;
  closed under `bind` (`Steps.bind`), the loads (`Steps.registerCellLoad`, `Steps.registerCellLoadList`)
  and pushes;
* `Framed.dictGetInt_framed`: `DICT{I,U}GET` (not `REF`) on any root cell;
* `Framed.runWith_dictGetInt`, tactic `vm_dict_get_any`: the run from a state about to run it.
-/

namespace TvmLean.Framed

open TvmLean

/-! ## Errors of the lookup -/

/-- An `Except` failing only with cell_und or dict_err. -/
def ErrDict {α : Type} (r : Except Excno α) : Prop := ∀ e, r = .error e → e = .cellUnd ∨ e = .dictErr

theorem ErrDict.ok {α : Type} (a : α) : ErrDict (.ok a : Except Excno α) := by
  intro e h; cases h

theorem ErrDict.pure {α : Type} (a : α) : ErrDict (pure a : Except Excno α) := by
  intro e h; cases h

theorem ErrDict.throwCellUnd {α : Type} : ErrDict (throw .cellUnd : Except Excno α) := by
  intro e h; cases h; exact Or.inl rfl

theorem ErrDict.throwDictErr {α : Type} : ErrDict (throw .dictErr : Except Excno α) := by
  intro e h; cases h; exact Or.inr rfl

theorem ErrDict.bind {α β : Type} {x : Except Excno α} {f : α → Except Excno β} (hx : ErrDict x)
    (hf : ∀ a, ErrDict (f a)) : ErrDict (x >>= f) := by
  intro e h
  cases x with
  | error e' => cases h; exact hx _ rfl
  | ok a => exact hf a e h

theorem ErrDict.ite {α : Type} {c : Prop} [Decidable c] {x y : Except Excno α} (hx : ErrDict x)
    (hy : ErrDict y) : ErrDict (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem ErrDict.dite {α : Type} {c : Prop} [Decidable c] {x : c → Except Excno α} {y : ¬c → Except Excno α}
    (hx : ∀ h, ErrDict (x h)) (hy : ∀ h, ErrDict (y h)) : ErrDict (if h : c then x h else y h) := by
  split
  · exact hx _
  · exact hy _

/-- A resolver that fails only with cell_und (the VM's: `libraryResolveLoadsAux_error`). -/
def ResolverCellUnd (r : Cell → Except Excno Cell) : Prop := ∀ c, ErrDict (r c)

theorem resolverCellUnd_library (libs : Array Cell) (gv : Nat) (refused : Array BitString) :
    ResolverCellUnd (fun c => (libraryResolveLoads libs gv c refused).2) := by
  intro c e h
  exact Or.inl (libraryResolveLoadsAux_error libs gv refused _ c #[] e h)

theorem parseDictLabel_err (cell : Cell) (maxLen : Nat) (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) :
    ErrDict (parseDictLabel cell maxLen r) := by
  unfold parseDictLabel
  refine ErrDict.bind (hr cell) (fun c => ?_)
  repeat' (first
    | exact ErrDict.ok _ | exact ErrDict.pure _ | exact ErrDict.throwCellUnd
    | (refine ErrDict.bind ?_ (fun _ => ?_)) | (refine ErrDict.ite ?_ ?_) | split
    | (unfold Slice.takeBitsAsNatCellUnd) | (dsimp only))

theorem dictValidateNodeExt_err (lbl : DictLabel) (remaining : Nat) : ErrDict (dictValidateNodeExt lbl remaining) := by
  unfold dictValidateNodeExt
  repeat' (first
    | exact ErrDict.ok _ | exact ErrDict.pure _ | exact ErrDict.throwDictErr
    | (refine ErrDict.bind ?_ (fun _ => ?_)) | (refine ErrDict.ite ?_ ?_) | split | (dsimp only))

theorem dictLookupAuxWithCellsF_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) :
    ∀ (f : Nat) (cell : Cell) (key : BitString) (pos remaining : Nat),
      ErrDict (dictLookupAuxWithCellsF r f cell key pos remaining) := by
  intro f
  induction f with
  | zero => intro cell key pos remaining; exact ErrDict.ok _
  | succ f ih =>
    intro cell key pos remaining
    simp only [dictLookupAuxWithCellsF, dictLookupWithCellsStep]
    refine ErrDict.bind (parseDictLabel_err _ _ r hr) (fun lbl => ?_)
    refine ErrDict.bind (dictValidateNodeExt_err _ _) (fun rem0 => ?_)
    repeat' (first
      | exact ErrDict.ok _ | exact ErrDict.pure _
      | exact ih _ _ _ _
      | (refine ErrDict.bind ?_ (fun _ => ?_)) | (refine ErrDict.ite ?_ ?_) | (refine ErrDict.dite ?_ ?_)
      | (intro _) | split | (dsimp only))

/-- **The lookup fails only with cell_und or dict_err** (with a resolver failing only with cell_und). -/
theorem dictLookupWithCells_err (root : Option Cell) (key : BitString) (r : Cell → Except Excno Cell)
    (hr : ResolverCellUnd r) : ErrDict (dictLookupWithCells root key r) := by
  unfold dictLookupWithCells
  split
  · exact ErrDict.pure _
  · exact dictLookupAuxWithCellsF_err r hr _ _ _ _ _

/-! ## Framed computations -/

theorem Frame.refl (st : VmState) : Frame st st := rfl

theorem Frame.trans {a b c : VmState} (h1 : Frame a b) (h2 : Frame b c) : Frame a c := by
  unfold Frame at *
  conv => lhs; rw [h2, h1]

theorem Frame.of_load {a b : VmState} (h : LoadFrame a b) : Frame a b := by
  unfold Frame
  have hs := h.stack
  unfold LoadFrame at h
  conv => lhs; rw [h]
  rw [hs]

theorem Frame.regs {a b : VmState} (h : Frame a b) : b.regs = a.regs := by rw [h]
theorem Frame.maxLibraryLoads {a b : VmState} (h : Frame a b) : b.maxLibraryLoads = a.maxLibraryLoads := by rw [h]
theorem Frame.libraries {a b : VmState} (h : Frame a b) : b.libraries = a.libraries := by rw [h]
theorem Frame.globalVersion {a b : VmState} (h : Frame a b) : b.globalVersion = a.globalVersion := by rw [h]
theorem Frame.librariesRefused {a b : VmState} (h : Frame a b) : b.librariesRefused = a.librariesRefused := by rw [h]

/-- A VM computation framed (`Frame`), with the relation `P a s s'` between its result, the stack
before and the stack after, failing only with an exception of code 2 or more, noting no refused
library without `max_library_loads`. -/
def Steps {α : Type} (m : VM α) (P : α → Stack → Stack → Prop) : Prop :=
  ∀ st : VmState, Frame st (ExceptT.run m st).2 ∧
    (∀ a, (ExceptT.run m st).1 = .ok a → P a st.stack (ExceptT.run m st).2.stack) ∧
    (∀ e, (ExceptT.run m st).1 = .error e → 2 ≤ e.toInt) ∧
    (st.maxLibraryLoads = none → (ExceptT.run m st).2.librariesMissed = st.librariesMissed)

theorem Steps.pure {α : Type} (a : α) : Steps (pure a : VM α) (fun b s s' => b = a ∧ s' = s) := by
  intro st
  rw [VM.run_pure]
  refine ⟨Frame.refl _, ?_, ?_, fun _ => rfl⟩
  · intro b h; cases h; exact ⟨rfl, rfl⟩
  · intro e h; cases h

theorem Steps.throw {α : Type} (e : Excno) (he : 2 ≤ e.toInt) (P : α → Stack → Stack → Prop) :
    Steps (throw e : VM α) P := by
  intro st
  rw [VM.run_throw]
  refine ⟨Frame.refl _, ?_, ?_, fun _ => rfl⟩
  · intro b h; cases h
  · intro e' h; cases h; exact he

theorem Steps.push (v : Value) : Steps (VM.push v) (fun _ s s' => s' = s.push v) := by
  intro st
  rw [VM.run_push]
  refine ⟨rfl, fun _ _ => rfl, ?_, fun _ => rfl⟩
  intro e h; cases h

theorem Steps.mono {α : Type} {m : VM α} {P Q : α → Stack → Stack → Prop} (h : Steps m P)
    (hPQ : ∀ a s s', P a s s' → Q a s s') : Steps m Q := by
  intro st
  obtain ⟨h1, h2, h3, h4⟩ := h st
  exact ⟨h1, fun a ha => hPQ _ _ _ (h2 a ha), h3, h4⟩

theorem Steps.bind {α β : Type} {m : VM α} {f : α → VM β} {P : α → Stack → Stack → Prop}
    {Q : α → β → Stack → Stack → Prop} (hm : Steps m P) (hf : ∀ a, Steps (f a) (Q a)) :
    Steps (m >>= f) (fun b s s'' => ∃ a s', P a s s' ∧ Q a b s' s'') := by
  intro st
  obtain ⟨h1, h2, h3, h4⟩ := hm st
  rw [VM.run_bind]
  generalize hX : ExceptT.run m st = X at h1 h2 h3 h4
  obtain ⟨r, st1⟩ := X
  simp only at h1 h2 h3 h4
  cases r with
  | error e =>
    rw [VM.bindRes_error]
    refine ⟨h1, ?_, ?_, h4⟩
    · intro b h; cases h
    · intro e' h; cases h; exact h3 e rfl
  | ok a =>
    rw [VM.bindRes_ok]
    obtain ⟨g1, g2, g3, g4⟩ := hf a st1
    refine ⟨h1.trans g1, fun b hb => ⟨a, st1.stack, h2 a rfl, g2 b hb⟩, g3, fun hn => ?_⟩
    rw [g4 (by rw [h1.maxLibraryLoads]; exact hn), h4 hn]

/-- The loads of the step (`VM.registerCellLoad`, a library cell followed) are framed. -/
theorem Steps.registerCellLoad (c : Cell) : Steps (VM.registerCellLoad c) (fun _ s s' => s' = s) := by
  intro st
  obtain ⟨hF, hN⟩ := LoadFrame.registerCellLoads st (.cell c :: (st.libraryLoads c).toList)
  simp only [VM.registerCellLoad, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_set]
  generalize st.registerCellLoads (.cell c :: (st.libraryLoads c).toList) = R at hF hN ⊢
  obtain ⟨st', ex⟩ := R
  simp only at hF hN ⊢
  cases ex with
  | true =>
    simp only [if_true, VM.run_throw]
    refine ⟨Frame.of_load hF, ?_, ?_, hN⟩
    · intro _ h; cases h
    · intro e h; cases h; decide
  | false =>
    simp only [Bool.false_eq_true, if_false, VM.run_pure]
    refine ⟨Frame.of_load hF, fun _ _ => hF.stack, ?_, hN⟩
    intro e h; cases h

theorem Steps.registerCellLoadList : ∀ l : List Cell, Steps (VM.registerCellLoadList l) (fun _ s s' => s' = s)
  | [] => by
    intro st
    rw [VM.run_registerCellLoadList_nil]
    refine ⟨Frame.refl _, fun _ _ => rfl, ?_, fun _ => rfl⟩
    intro e h; cases h
  | c :: cs => by
    have h := Steps.bind (Steps.registerCellLoad c) (fun _ => Steps.registerCellLoadList cs)
    refine (Steps.mono h ?_)
    rintro _ s s'' ⟨_, s', h1, h2⟩
    rw [h2, h1]

/-! ## `DICT{I,U}GET` -/

/-- What `DICT{I,U}GET` leaves on the stack `s` under its arguments: the value found and `-1`, or
`0`. -/
def DictOk (s : Stack) (s' : Stack) : Prop :=
  (∃ v, s' = (s.push (.slice v)).push (.int (.num (-1)))) ∨ s' = s.push (.int (.num 0))

theorem Steps.get : Steps (get : VM VmState) (fun _ s s' => s' = s) := by
  intro st
  rw [VM.run_get]
  refine ⟨Frame.refl _, fun _ _ => rfl, ?_, fun _ => rfl⟩
  intro e h; cases h

/-- The loads of the cells a lookup visited (a `for` loop of `VM.registerCellLoad`). -/
theorem Steps.forLoads (cells : Array Cell) :
    Steps (forIn cells PUnit.unit fun c _ => do VM.registerCellLoad c; Pure.pure (ForInStep.yield PUnit.unit) : VM PUnit)
      (fun _ s s' => s' = s) := by
  rw [VM.forIn_registerCellLoad]
  refine Steps.mono (Steps.bind (Steps.registerCellLoadList _) (fun _ => Steps.pure _)) ?_
  rintro _ s s'' ⟨_, s', h1, h2⟩
  rw [h2.2, h1]

/-- The tail of `DICTGET` (`DictTail.getTail`, not `REF`) on any root is framed. -/
theorem Steps.getTail (root : Cell) (key : BitString) :
    Steps (DictTail.getTail (some root) key false) (fun _ s s' => DictOk s s') := by
  unfold DictTail.getTail
  simp only [VM.cellResolver, bind_assoc, pure_bind]
  refine Steps.mono (Steps.bind (Steps.registerCellLoad root) (fun _ => Steps.bind Steps.get
    (fun x => (?_ : Steps _ (fun _ s s' => DictOk s s'))))) ?_
  · split
    · rename_i e he
      have he2 : 2 ≤ e.toInt := by
        rcases dictLookupWithCells_err _ _ _ (resolverCellUnd_library _ _ _) e he with h | h <;> (subst h; decide)
      refine Steps.mono (Steps.bind Steps.get (fun _ => Steps.bind (Steps.forLoads _) (fun _ =>
        Steps.throw e he2 (fun _ s s' => DictOk s s')))) ?_
      rintro _ s s'' ⟨_, s1, h1, _, s2, h2, h3⟩
      rw [h1] at h2; rw [h2] at h3; exact h3
    · refine Steps.mono (Steps.bind (Steps.forLoads _) (fun _ => Steps.push (.int (.num 0)))) ?_
      rintro _ s s'' ⟨_, s1, h1, h2⟩
      exact Or.inr (by rw [h2, h1])
    · simp only [Bool.false_eq_true, if_false]
      refine Steps.mono (Steps.bind (Steps.forLoads _) (fun _ => Steps.bind (Steps.push _)
        (fun _ => Steps.push (.int (.num (-1)))))) ?_
      rintro _ s s'' ⟨_, s1, h1, _, s2, h2, h3⟩
      exact Or.inl ⟨_, by rw [h3, h2, h1]⟩
  · rintro _ s s'' ⟨_, s1, h1, _, s2, h2, h3⟩
    rw [h1] at h2; rw [h2] at h3; exact h3

/-- `DICT{I,U}GET` (not `REF`) on the stack `s idx root n`: range_chk for a key length outside
`0..1023`, `0` for a key out of the range of `n`-bit keys, else the tail. -/
theorem run_dictGetInt (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int) (unsigned : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n))) :
    ExceptT.run (execInstr (.dictGet true unsigned false)) st =
      if 0 ≤ n ∧ n ≤ 1023 then
        match dictKeyBits? idx n.toNat unsigned with
        | none => (.ok (), { st with stack := s.push (.int (.num 0)) })
        | some key => ExceptT.run (DictTail.getTail (some root) key false) { st with stack := s }
      else (.error .rangeChk, { st with stack := (s.push (.int (.num idx))).push (.cell root) }) := by
  rw [DictTail.getHandler_eq]
  by_cases hn : 0 ≤ n ∧ n ≤ 1023
  · have hn1 : ¬ n < 0 := by omega
    have hn' : ¬ n.toNat > 1023 := by omega
    rw [if_pos hn]
    cases hk : dictKeyBits? idx n.toNat unsigned with
    | none => vm_simp [DictTail.dictGet, hs, hk, hn1, hn', VM.popMaybeCell]
    | some key => vm_simp [DictTail.dictGet, hs, hk, hn1, hn', VM.popMaybeCell]
  · rw [if_neg hn]
    by_cases h1 : n < 0
    · vm_simp [DictTail.dictGet, hs, h1]
    · have h2 : n.toNat > 1023 := by omega
      vm_simp [DictTail.dictGet, hs, h1, h2]

/-- **`DICT{I,U}GET` (not `REF`) on any root cell is framed**: the value found and `-1`, or `0`, or
an exception of code 2 or more. -/
theorem dictGetInt_framed (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int) (unsigned : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n))) :
    ExecFramed (.dictGet true unsigned false) (DictOk s) st := by
  have e := run_dictGetInt st s idx root n unsigned hs
  have hframe : ∀ s0, Frame st { st with stack := s0 } := fun _ => rfl
  split at e
  · split at e
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e]
      · exact hframe _
      · exact fun _ => Or.inr rfl
      · intro e' h; cases h
      · exact fun _ => rfl
    · obtain ⟨g1, g2, g3, g4⟩ := Steps.getTail root _ { st with stack := s }
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e]
      · exact (hframe s).trans g1
      · exact fun h => g2 () h
      · exact g3
      · exact g4
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e]
    · exact hframe _
    · intro h; cases h
    · intro e' h; cases h; decide
    · exact fun _ => rfl

/-- **A run from `DICT{I,U}GET` on any dictionary.** `st` is about to run it (decoded from `code`,
the code after it `rest`) on the stack `s idx root n`: if `P` holds of every result that commits
nothing and of every run from the state after it with a value found (`v`, `-1`) or not (`0`), any
gas, loaded cells and libraries (`after`), it holds of the run. -/
theorem runWith_dictGetInt {st : VmState} {code rest : Slice} {s : Stack} {idx : Int} {root : Cell} {n : Int}
    {unsigned : Bool} (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (.dictGet true unsigned false, k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hfound : ∀ (v : Slice) g lc ll k, k < fuel →
      P (VmState.runWith execInstr k (after st rest ((s.push (.slice v)).push (.int (.num (-1)))) g lc ll)))
    (hnone : ∀ g lc ll k, k < fuel →
      P (VmState.runWith execInstr k (after st rest (s.push (.int (.num 0))) g lc ll))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := DictOk s)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom,
      fun st0 h1 _ => dictGetInt_framed st0 s idx root n unsigned (h1.trans hs)⟩ hr hm P hP fuel
    (fun s' g lc ll k hk h => by
      rcases h with ⟨v, rfl⟩ | rfl
      · exact hfound v g lc ll k hk
      · exact hnone g lc ll k hk)

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_dict_get_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S` written out)
is about to run `DICT{I,U}GET` (not `REF`) on a dictionary it does not know: by
`Framed.runWith_dictGetInt`, three goals: `P` of a result that commits nothing, and `P` of the runs
from the state after it with a value found (`v`, `-1`) and with none (`0`), any gas, loaded cells
and libraries. -/
elab "vm_dict_get_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_dict_get_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  let iE ← whnfR iE
  unless iE.isAppOfArity ``Instr.dictGet 3 do throwError "vm_dict_get_any: the instruction is {iE}, not DICTGET"
  unless (iE.getArg! 0).isConstOf ``Bool.true && (iE.getArg! 2).isConstOf ``Bool.false do
    throwError "vm_dict_get_any: not DICTIGET or DICTUGET"
  let stk ← whnfR (← mkAppM ``VmState.stack #[S])
  unless stk.isAppOfArity ``Array.push 3 do throwError "vm_dict_get_any: the stack is not written out"
  let s1 ← whnfR (stk.getArg! 1)
  unless s1.isAppOfArity ``Array.push 3 do throwError "vm_dict_get_any: the stack is not written out"
  let s2 ← whnfR (s1.getArg! 1)
  unless s2.isAppOfArity ``Array.push 3 do throwError "vm_dict_get_any: the stack is not written out"
  let vn ← whnfR (stk.getArg! 2)
  let vroot ← whnfR (s1.getArg! 2)
  let vidx ← whnfR (s2.getArg! 2)
  unless vroot.isAppOfArity ``Value.cell 1 do throwError "vm_dict_get_any: no cell under the key length"
  let intOf (v : Expr) : MetaM Expr := do
    unless v.isAppOfArity ``Value.int 1 do throwError "vm_dict_get_any: not an integer"
    let iv ← whnfR v.appArg!
    unless iv.isAppOfArity ``IntVal.num 1 do throwError "vm_dict_get_any: not a finite integer"
    return iv.appArg!
  let n ← intOf vn
  let idx ← intOf vidx
  let motive ← withLocalDeclD `r (mkConst ``StepResult) fun rv => do
    mkLambdaFVars #[rv] ((← kabstract t r).instantiate1 rv)
  let refl (e : Expr) : MetaM Expr := mkEqRefl e
  let hcc ← refl (← mkAppM ``VmState.cc #[S])
  let hcp ← refl (← mkAppM ``VmState.cp #[S])
  let hchain ← Exec.decideProof (← mkAppM ``LT.lt #[← whnfCore (← whnfR (← mkAppM ``VmState.chainJumps #[S])),
    mkConst ``freeNestedContJump])
  let hc2 ← refl (← mkAppM ``Regs.c2 #[← mkAppM ``VmState.regs #[S]])
  let hcom ← refl (← mkAppM ``CommittedState.committed #[← mkAppM ``VmState.cstate #[S]])
  let hr ← refl (← mkAppM ``VmState.librariesRefused #[S])
  let hm ← refl (← mkAppM ``VmState.librariesMissed #[S])
  let hs ← refl (← mkAppM ``VmState.stack #[S])
  let f ← mkAppOptM ``Framed.runWith_dictGetInt #[S, none, none, s2.getArg! 1, idx, vroot.appArg!, n,
    iE.getArg! 1, hcc, hcp, hbitsNe, hverLe, hdecEx, hchain, hc2, hcom, hr, hm, hs, motive]
  let (f1, goals1) ← Exec.applyRest f 1 #[fuel]
  let (pf, goals2) ← Exec.applyRest f1 2 #[]
  let goals := goals1 ++ goals2
  unless ← isDefEq (← inferType pf) t do throwError "vm_dict_get_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

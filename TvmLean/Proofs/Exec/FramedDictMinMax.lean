import TvmLean.Proofs.Exec.FramedStdAddr

/-!
# `DICT{,I,U}{,REM}{MIN,MAX}{,REF}` on any dictionary, framed

The minimum or maximum of a dictionary whose cells a run does not know (a dictionary of an inbound
message, of the data without an invariant on it) is framed (`TvmLean.Framed.ExecFramed`,
`TvmLean/Proofs/Exec/Framed.lean`): the instruction changes the stack, the gas, the loaded cells
and libraries only; it pushes (the new root for `REM`, null or a cell, then) the value (a slice, or
a cell for `REF`), the key (an integer for the `I`/`U` forms, a slice else) and `-1`, or (the root
and) `0`; it fails only with an exception of code 2 or more.

* `dictMinMaxWithCells_err`, `dictDeleteWithLoads_err`: the walk to the minimum or maximum and the
  delete of `REM` fail only with cell_und, dict_err (and cell_ov for the delete's new cells);
* `DictTail.minMax`: the handler (TvmLean/Semantics/Exec/Dict/DictGetMinMax.lean) with the part
  after the pops named (`DictTail.minMaxTail`), the same code (`DictTail.minMaxHandler_eq`);
* the combinators `Steps.keep_bind`, `Steps.push_bind`, `Steps.push_end`, ... of a framed
  computation whose relation is fixed in advance (`MinMaxOk`), and the tactic `steps_auto` that
  follows a handler with them (its leaves `steps_close`, `steps_err`, which other modules extend);
* `Framed.minMax_framed`, `Framed.runWith_minMax`, tactic `vm_dict_minmax_any`.
-/

namespace TvmLean.Framed

open TvmLean

/-! ## Errors of the walks -/

/-- An `Except` failing only with an exception of code 2 or more. -/
def ErrReal {α : Type} (r : Except Excno α) : Prop := ∀ e, r = .error e → 2 ≤ e.toInt

theorem ErrDict.real {α : Type} {r : Except Excno α} (h : ErrDict r) : ErrReal r := by
  intro e he
  rcases h e he with h | h <;> (subst h; decide)

theorem dictValidateNodeExtLe_err (lbl : DictLabel) (remaining : Nat) :
    ErrDict (dictValidateNodeExtLe lbl remaining) := by
  unfold dictValidateNodeExtLe
  repeat' (first
    | exact ErrDict.ok _ | exact ErrDict.pure _ | exact ErrDict.throwDictErr
    | (refine ErrDict.bind ?_ (fun _ => ?_)) | (refine ErrDict.ite ?_ ?_) | split | (dsimp only))

/-- The walk to the minimum or maximum below a node fails only with cell_und or dict_err. -/
theorem dictMinMaxAuxWithCells_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) (n : Nat) :
    ∀ (cell : Cell) (pos : Nat) (firstBit restBit : Bool),
      ErrDict (dictMinMaxAuxWithCells cell n pos firstBit restBit r) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro cell pos firstBit restBit
    rw [dictMinMaxAuxWithCells]
    refine ErrDict.bind (parseDictLabel_err _ _ r hr) (fun lbl => ?_)
    refine ErrDict.bind (dictValidateNodeExtLe_err _ _) (fun x => ?_)
    obtain ⟨rem0, hle⟩ := x
    dsimp only
    refine ErrDict.dite (fun _ => ErrDict.pure _) (fun h0 => ?_)
    refine ErrDict.bind (ih (rem0 - 1) (by omega) _ _ _ _) (fun y => ?_)
    repeat' (first | exact ErrDict.pure _ | exact ErrDict.ok _ | split | (dsimp only))

/-- **The walk to the minimum or maximum fails only with cell_und or dict_err** (with a resolver
failing only with cell_und). -/
theorem dictMinMaxWithCells_err (root : Option Cell) (n : Nat) (fetchMax invertFirst : Bool)
    (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) :
    ErrDict (dictMinMaxWithCells root n fetchMax invertFirst r) := by
  unfold dictMinMaxWithCells
  split
  · exact ErrDict.pure _
  · refine ErrDict.bind (dictMinMaxAuxWithCells_err r hr _ _ _ _ _) (fun y => ?_)
    repeat' (first | exact ErrDict.pure _ | exact ErrDict.ok _ | split | (dsimp only))

/-- The walk with the VM's resolver: its exception has code 2 or more. -/
theorem dictMinMaxWithCells_real {root : Option Cell} {n : Nat} {fetchMax invertFirst : Bool}
    {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno}
    (h : dictMinMaxWithCells root n fetchMax invertFirst
      (fun c => (libraryResolveLoads libs gv c refused).2) = .error e) : 2 ≤ e.toInt :=
  ErrDict.real (dictMinMaxWithCells_err _ _ _ _ _ (resolverCellUnd_library _ _ _)) e h

/-- An `Except` with the cells loaded failing only with an exception of code 2 or more. -/
def ErrDel {α : Type} (r : Except (Excno × Array Cell) α) : Prop := ∀ e l, r = .error (e, l) → 2 ≤ e.toInt

theorem ErrDel.ok {α : Type} (a : α) : ErrDel (.ok a : Except (Excno × Array Cell) α) := by
  intro e l h; cases h

theorem ErrDel.pure {α : Type} (a : α) : ErrDel (pure a : Except (Excno × Array Cell) α) := by
  intro e l h; cases h

theorem ErrDel.bind {α β : Type} {x : Except (Excno × Array Cell) α} {f : α → Except (Excno × Array Cell) β}
    (hx : ErrDel x) (hf : ∀ a, ErrDel (f a)) : ErrDel (x >>= f) := by
  intro e l h
  cases x with
  | error p => cases h; exact hx _ _ rfl
  | ok a => exact hf a e l h

theorem ErrDel.ite {α : Type} {c : Prop} [Decidable c] {x y : Except (Excno × Array Cell) α}
    (hx : ErrDel x) (hy : ErrDel y) : ErrDel (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem ErrDel.dite {α : Type} {c : Prop} [Decidable c] {x : c → Except (Excno × Array Cell) α}
    {y : ¬c → Except (Excno × Array Cell) α} (hx : ∀ h, ErrDel (x h)) (hy : ∀ h, ErrDel (y h)) :
    ErrDel (if h : c then x h else y h) := by
  split
  · exact hx _
  · exact hy _

theorem ErrDel.withLoads {α : Type} {x : Except Excno α} (hx : ErrReal x) (l : Array Cell) :
    ErrDel (withLoads l x) := by
  intro e l' h
  cases x with
  | error e' =>
    have h' : (Except.error (e', l) : Except (Excno × Array Cell) α) = .error (e, l') := h
    injection h' with h''
    injection h'' with h1 _
    subst h1
    exact hx e' rfl
  | ok a =>
    have h' : (Except.ok a : Except (Excno × Array Cell) α) = .error (e, l') := h
    cases h'

theorem ErrDel.underCell {α : Type} {x : Except (Excno × Array Cell) α} (hx : ErrDel x) (c : Cell) :
    ErrDel (underCell c x) := by
  intro e l h
  cases x with
  | error p =>
    obtain ⟨e', l'⟩ := p
    have h' : (Except.error (e', #[c] ++ l') : Except (Excno × Array Cell) α) = .error (e, l) := h
    injection h' with h''
    injection h'' with h1 _
    subst h1
    exact hx e' l' rfl
  | ok a =>
    have h' : (Except.ok a : Except (Excno × Array Cell) α) = .error (e, l) := h
    cases h'

theorem builderStoreBitsChecked_real (b : Builder) (bs : BitString) : ErrReal (builderStoreBitsChecked b bs) := by
  intro e h
  unfold builderStoreBitsChecked at h
  split at h
  · cases h
  · cases h; decide

theorem builderAppendCellChecked_real (b : Builder) (c : Cell) : ErrReal (builderAppendCellChecked b c) := by
  intro e h
  unfold builderAppendCellChecked at h
  split at h
  · cases h
  · cases h; decide

/-- The delete below a node fails only with an exception of code 2 or more (cell_und, dict_err,
cell_ov). -/
theorem dictDeleteAuxWithLoads_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) (remaining : Nat) :
    ∀ (cell : Cell) (key : BitString) (pos : Nat),
      ErrDel (dictDeleteAuxWithLoads cell key pos remaining r) := by
  induction remaining using Nat.strongRecOn with
  | ind m ih =>
    intro cell key pos
    rw [dictDeleteAuxWithLoads]
    refine ErrDel.bind (ErrDel.withLoads (ErrDict.real (parseDictLabel_err _ _ r hr)) _) (fun lbl => ?_)
    refine ErrDel.bind (ErrDel.withLoads (ErrDict.real (dictValidateNodeExtLe_err _ _)) _) (fun x => ?_)
    obtain ⟨rem0, hle⟩ := x
    dsimp only
    repeat' (first
      | exact ErrDel.pure _ | exact ErrDel.ok _
      | exact ErrDel.underCell (ih _ (by omega) _ _ _) _
      | exact ErrDel.withLoads (ErrDict.real (parseDictLabel_err _ _ r hr)) _
      | exact ErrDel.withLoads (ErrDict.real (dictValidateNodeExt_err _ _)) _
      | exact ErrDel.withLoads (builderStoreBitsChecked_real _ _) _
      | exact ErrDel.withLoads (builderAppendCellChecked_real _ _) _
      | (refine ErrDel.bind ?_ (fun _ => ?_))
      | (refine ErrDel.dite (fun _ => ?_) (fun _ => ?_)) | (refine ErrDel.ite ?_ ?_) | split
      | (dsimp only))

/-- **The delete fails only with an exception of code 2 or more.** -/
theorem dictDeleteWithLoads_err (root : Option Cell) (key : BitString) (r : Cell → Except Excno Cell)
    (hr : ResolverCellUnd r) : ErrDel (dictDeleteWithLoads root key r) := by
  unfold dictDeleteWithLoads
  split
  · exact ErrDel.pure _
  · exact dictDeleteAuxWithLoads_err r hr _ _ _ _

/-- The delete with the VM's resolver: its exception has code 2 or more. -/
theorem dictDeleteWithLoads_real {root : Option Cell} {key : BitString} {libs : Array Cell} {gv : Nat}
    {refused : Array BitString} {e : Excno} {l : Array Cell}
    (h : dictDeleteWithLoads root key (fun c => (libraryResolveLoads libs gv c refused).2) = .error (e, l)) :
    2 ≤ e.toInt :=
  dictDeleteWithLoads_err _ _ _ (resolverCellUnd_library _ _ _) e l h

end TvmLean.Framed

/-! ## The handler, with its tail named -/

namespace DictTail

open TvmLean

/-- The tail of `DICT*MIN`/`MAX` after the pops (`execInstrDictDictGetMinMax`,
TvmLean/Semantics/Exec/Dict/DictGetMinMax.lean): the same code. -/
def minMaxTail (dictCell? : Option Cell) (n : Nat) (fetchMax invertFirst remove byRef intKey : Bool) :
    VM Unit := do
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()
  match dictMinMaxWithCells (resolve := (← VM.cellResolver)) dictCell? n fetchMax invertFirst with
  | .error e =>
      let loaded := dropFirstRootLoad dictCell? (dictMinMaxVisitedCells (resolve := (← VM.cellResolver)) dictCell? n fetchMax invertFirst)
      for c in loaded do
        VM.registerCellLoad c
      throw e
  | .ok (none, loaded) =>
      let loaded := dropFirstRootLoad dictCell? loaded
      for c in loaded do
        VM.registerCellLoad c
      if remove then
        match dictCell? with
        | none => VM.push .null
        | some c => VM.push (.cell c)
      VM.pushSmallInt 0
  | .ok (some (val0, keyBits), loaded0) =>
      let loaded0 := dropFirstRootLoad dictCell? loaded0
      for c in loaded0 do
        VM.registerCellLoad c
      let mut val := val0
      let mut dictOut? : Option Cell := dictCell?
      let mut created : Nat := 0
      let mut loaded1 : Array Cell := #[]
      if remove then
        match dictDeleteWithLoads (resolve := (← VM.cellResolver)) dictCell? keyBits with
        | .error (e, loadedDel) =>
            for c in loadedDel do
              VM.registerCellLoad c
            throw e
        | .ok (oldVal?, newRoot?, created1, loadedDel) =>
            match oldVal? with
            | none => throw .dictErr
            | some oldVal =>
                val := oldVal
                dictOut? := newRoot?
                created := created1
                loaded1 := loadedDel
      for c in loaded1 do
        VM.registerCellLoad c
      if created > 0 then
        VM.chargeCellCreates created

      if remove then
        match dictOut? with
        | none => VM.push .null
        | some c => VM.push (.cell c)

      if byRef then
        if val.bitsRemaining == 0 && val.refsRemaining == 1 then
          let c := val.cell.refs[val.refPos]!
          VM.push (.cell c)
        else
          throw .dictErr
      else
        VM.push (.slice val)

      if intKey then
        let keyOut : Int :=
          if invertFirst then
            bitsToIntSignedTwos keyBits
          else
            Int.ofNat (bitsToNat keyBits)
        VM.pushIntQuiet (.num keyOut) false
      else
        VM.consumeGas cellCreateGasPrice
        let keyCell : Cell := Cell.mkOrdinary keyBits #[]
        VM.push (.slice (Slice.ofCell keyCell))

      VM.pushSmallInt (-1)

/-- The handler of `DICT*MIN`/`MAX` with its tail named. -/
def minMax (args5 : Nat) : VM Unit := do
  VM.checkUnderflow 2
  let byRef : Bool := (args5 &&& 1) = 1
  let unsigned : Bool := (args5 &&& 2) = 2
  let intKey : Bool := (args5 &&& 4) = 4
  let fetchMax : Bool := (args5 &&& 8) = 8
  let remove : Bool := (args5 &&& 16) = 16
  let invertFirst : Bool := !unsigned
  let maxN : Nat := if intKey then (if unsigned then 256 else 257) else 1023
  let n ← VM.popNatUpTo maxN
  let dictCell? ← VM.popMaybeCell
  minMaxTail dictCell? n fetchMax invertFirst remove byRef intKey

end DictTail

namespace TvmLean

/-- `DICT*MIN`/`MAX` runs as `DictTail.minMax` (the same code). -/
theorem DictTail.minMaxHandler_eq (args5 : Nat) (st : VmState) :
    ExceptT.run (execInstr (.dictGetMinMax args5)) st = ExceptT.run (DictTail.minMax args5) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

end TvmLean

namespace TvmLean.Framed

open TvmLean

/-! ## Framed computations with a fixed relation -/

theorem Steps.keep_bind {α β : Type} {m : VM α} {f : α → VM β} {R : Stack → Stack → Prop}
    (hm : Steps m (fun _ s s' => s' = s)) (hf : ∀ a, Steps (f a) (fun _ s s' => R s s')) :
    Steps (m >>= f) (fun _ s s' => R s s') :=
  Steps.mono (Steps.bind hm hf) (by
    rintro _ s s'' ⟨_, s1, h1, h2⟩
    rw [h1] at h2
    exact h2)

theorem Steps.push_bind {β : Type} {v : Value} {f : Unit → VM β} {R : Stack → Stack → Prop}
    (hf : ∀ a, Steps (f a) (fun _ s1 s' => ∀ s, s1 = s.push v → R s s')) :
    Steps (VM.push v >>= f) (fun _ s s' => R s s') :=
  Steps.mono (Steps.bind (Steps.push v) hf) (by
    rintro _ s s'' ⟨_, s1, h1, h2⟩
    exact h2 s h1)

theorem Steps.push_end {v : Value} {R : Stack → Stack → Prop} (h : ∀ s, R s (s.push v)) :
    Steps (VM.push v) (fun _ s s' => R s s') :=
  Steps.mono (Steps.push v) (fun _ s s' h' => by rw [h']; exact h s)

theorem Steps.pushIntQuiet_bind {β : Type} {x : Int} {f : Unit → VM β} {R : Stack → Stack → Prop}
    (hf : ∀ a, Steps (f a) (fun _ s1 s' => ∀ s, s1 = s.push (.int (.num x)) → R s s')) :
    Steps (VM.pushIntQuiet (.num x) false >>= f) (fun _ s s' => R s s') :=
  Steps.mono (Steps.bind (Steps.pushIntQuiet_num x) hf) (by
    rintro _ s s'' ⟨_, s1, h1, h2⟩
    exact h2 s h1)

theorem Steps.pushIntQuiet_end {x : Int} {R : Stack → Stack → Prop} (h : ∀ s, R s (s.push (.int (.num x)))) :
    Steps (VM.pushIntQuiet (.num x) false) (fun _ s s' => R s s') :=
  Steps.mono (Steps.pushIntQuiet_num x) (fun _ s s' h' => by rw [h']; exact h s)

theorem Steps.pure_end {α : Type} {a : α} {R : Stack → Stack → Prop} (h : ∀ s, R s s) :
    Steps (Pure.pure a : VM α) (fun _ s s' => R s s') :=
  Steps.mono (Steps.pure a) (fun _ s s' h' => by rw [h'.2]; exact h s)

theorem Steps.keep_end {α : Type} {m : VM α} {R : Stack → Stack → Prop}
    (hm : Steps m (fun _ s s' => s' = s)) (h : ∀ s, R s s) : Steps m (fun _ s s' => R s s') :=
  Steps.mono hm (fun _ s s' h' => by rw [h']; exact h s)

theorem Steps.throw_R {α : Type} {e : Excno} (he : 2 ≤ e.toInt) {R : Stack → Stack → Prop} :
    Steps (MonadExcept.throw e : VM α) (fun _ s s' => R s s') :=
  Steps.throw e he _

theorem Steps.throw_bind {α β : Type} {e : Excno} (he : 2 ≤ e.toInt) {f : α → VM β}
    {R : Stack → Stack → Prop} : Steps ((MonadExcept.throw e : VM α) >>= f) (fun _ s s' => R s s') := by
  intro st
  have h := Steps.throw (α := β) e he (fun _ s s' => R s s') st
  rw [VM.run_throw] at h
  rw [VM.run_bind, VM.run_throw, VM.bindRes_error]
  exact h

theorem Steps.ite_R {α : Type} {c : Prop} [Decidable c] {x y : VM α} {R : Stack → Stack → Prop}
    (hx : c → Steps x (fun _ s s' => R s s')) (hy : ¬c → Steps y (fun _ s s' => R s s')) :
    Steps (if c then x else y) (fun _ s s' => R s s') := by
  by_cases h : c
  · rw [if_pos h]; exact hx h
  · rw [if_neg h]; exact hy h

theorem Steps.ite_bind {α β : Type} {c : Prop} [Decidable c] {x y : VM α} {f : α → VM β}
    {R : Stack → Stack → Prop} (hx : c → Steps (x >>= f) (fun _ s s' => R s s'))
    (hy : ¬c → Steps (y >>= f) (fun _ s s' => R s s')) :
    Steps ((if c then x else y) >>= f) (fun _ s s' => R s s') := by
  by_cases h : c
  · rw [if_pos h]; exact hx h
  · rw [if_neg h]; exact hy h

theorem Steps.consumeGas (amount : Int) : Steps (VM.consumeGas amount) (fun _ s s' => s' = s) := by
  intro st
  rw [VM.run_consumeGas]
  split
  · refine ⟨rfl, ?_, ?_, fun _ => rfl⟩
    · intro a h; cases h
    · intro e h; cases h; decide
  · refine ⟨rfl, fun _ _ => rfl, ?_, fun _ => rfl⟩
    intro e h; cases h

theorem Steps.checkUnderflow (n : Nat) : Steps (VM.checkUnderflow n) (fun _ s s' => s' = s) := by
  intro st
  rw [VM.run_checkUnderflow]
  split
  · refine ⟨Frame.refl _, ?_, ?_, fun _ => rfl⟩
    · intro a h; cases h
    · intro e h; cases h; decide
  · refine ⟨Frame.refl _, fun _ _ => rfl, ?_, fun _ => rfl⟩
    intro e h; cases h

/-! ## `DICT*MIN`/`MAX` -/

/-- What `DICT*MIN`/`MAX` (the flags `remove`, `byRef`, `intKey` of its opcode) leave on the stack
`s` under the key length and the dictionary: (for `REM`, the new root, null or a cell, then) the
value (a cell for `REF`, a slice else), the key (an integer for the `I`/`U` forms, a slice else) and
`-1`; or (the root and) `0`. -/
def MinMaxOk : Bool → Bool → Bool → Stack → Stack → Prop
  | false, false, false, s, s' =>
      (∃ (v : Slice) (k : Slice), s' = ((s.push (.slice v)).push (.slice k)).push (.int (.num (-1)))) ∨
      s' = s.push (.int (.num 0))
  | false, false, true, s, s' =>
      (∃ (v : Slice) (k : Int), s' = ((s.push (.slice v)).push (.int (.num k))).push (.int (.num (-1)))) ∨
      s' = s.push (.int (.num 0))
  | false, true, false, s, s' =>
      (∃ (v : Cell) (k : Slice), s' = ((s.push (.cell v)).push (.slice k)).push (.int (.num (-1)))) ∨
      s' = s.push (.int (.num 0))
  | false, true, true, s, s' =>
      (∃ (v : Cell) (k : Int), s' = ((s.push (.cell v)).push (.int (.num k))).push (.int (.num (-1)))) ∨
      s' = s.push (.int (.num 0))
  | true, false, false, s, s' =>
      (∃ (v : Slice) (k : Slice), s' = (((s.push .null).push (.slice v)).push (.slice k)).push (.int (.num (-1)))) ∨
      (∃ (r : Cell) (v : Slice) (k : Slice),
        s' = (((s.push (.cell r)).push (.slice v)).push (.slice k)).push (.int (.num (-1)))) ∨
      s' = (s.push .null).push (.int (.num 0)) ∨
      (∃ r : Cell, s' = (s.push (.cell r)).push (.int (.num 0)))
  | true, false, true, s, s' =>
      (∃ (v : Slice) (k : Int), s' = (((s.push .null).push (.slice v)).push (.int (.num k))).push (.int (.num (-1)))) ∨
      (∃ (r : Cell) (v : Slice) (k : Int),
        s' = (((s.push (.cell r)).push (.slice v)).push (.int (.num k))).push (.int (.num (-1)))) ∨
      s' = (s.push .null).push (.int (.num 0)) ∨
      (∃ r : Cell, s' = (s.push (.cell r)).push (.int (.num 0)))
  | true, true, false, s, s' =>
      (∃ (v : Cell) (k : Slice), s' = (((s.push .null).push (.cell v)).push (.slice k)).push (.int (.num (-1)))) ∨
      (∃ (r : Cell) (v : Cell) (k : Slice),
        s' = (((s.push (.cell r)).push (.cell v)).push (.slice k)).push (.int (.num (-1)))) ∨
      s' = (s.push .null).push (.int (.num 0)) ∨
      (∃ r : Cell, s' = (s.push (.cell r)).push (.int (.num 0)))
  | true, true, true, s, s' =>
      (∃ (v : Cell) (k : Int), s' = (((s.push .null).push (.cell v)).push (.int (.num k))).push (.int (.num (-1)))) ∨
      (∃ (r : Cell) (v : Cell) (k : Int),
        s' = (((s.push (.cell r)).push (.cell v)).push (.int (.num k))).push (.int (.num (-1)))) ∨
      s' = (s.push .null).push (.int (.num 0)) ∨
      (∃ r : Cell, s' = (s.push (.cell r)).push (.int (.num 0)))

/-- A pop (any value), then `f`: the relation of the whole from that of `f` on the stack under the
value popped. -/
theorem Steps.pop_bind {α β : Type} {m : VM α} {f : α → VM β} {R : Stack → Stack → Prop}
    (hm : Steps m (fun _ s s' => ∃ v, s = s'.push v)) (hf : ∀ a, Steps (f a) (fun _ s1 s' => ∀ v, R (s1.push v) s')) :
    Steps (m >>= f) (fun _ s s' => R s s') :=
  Steps.mono (Steps.bind hm hf) (by
    rintro _ s s'' ⟨_, s1, ⟨v, h1⟩, h2⟩
    rw [h1]
    exact h2 v)

theorem Steps.popInt' : Steps VM.popInt (fun _ s s' => ∃ v, s = s'.push v) :=
  Steps.mono Steps.popInt (fun i _ _ h => ⟨_, h⟩)

theorem Steps.popCell : Steps VM.popCell (fun _ s s' => ∃ v, s = s'.push v) := by
  intro st
  unfold VM.popCell
  rw [VM.run_bind, VM.run_pop]
  split
  · rename_i h
    rw [VM.bindRes_ok]
    have hst := stack_eq_pop_push_back st.stack h
    split
    · rw [VM.run_pure]
      refine ⟨rfl, fun _ _ => ⟨_, hst⟩, ?_, fun _ => rfl⟩
      intro e he; cases he
    · rw [VM.run_throw]
      refine ⟨rfl, ?_, ?_, fun _ => rfl⟩
      · intro a ha; cases ha
      · intro e he; cases he; decide
  · rw [VM.bindRes_error]
    steps_leaf

theorem Steps.popBuilder : Steps VM.popBuilder (fun _ s s' => ∃ v, s = s'.push v) := by
  intro st
  unfold VM.popBuilder
  rw [VM.run_bind, VM.run_pop]
  split
  · rename_i h
    rw [VM.bindRes_ok]
    have hst := stack_eq_pop_push_back st.stack h
    split
    · rw [VM.run_pure]
      refine ⟨rfl, fun _ _ => ⟨_, hst⟩, ?_, fun _ => rfl⟩
      intro e he; cases he
    · rw [VM.run_throw]
      refine ⟨rfl, ?_, ?_, fun _ => rfl⟩
      · intro a ha; cases ha
      · intro e he; cases he; decide
  · rw [VM.bindRes_error]
    steps_leaf

theorem Steps.popNatUpTo (max : Nat) : Steps (VM.popNatUpTo max) (fun _ s s' => ∃ v, s = s'.push v) := by
  unfold VM.popNatUpTo
  refine Steps.mono (Steps.bind Steps.popInt (fun v => (?_ : Steps _ (fun _ s s' => s' = s)))) ?_
  · split
    · exact Steps.throw _ (by decide) _
    · simp only [bind_assoc, pure_bind]
      repeat' (first
        | (refine Steps.ite_bind (fun _ => ?_) (fun _ => ?_))
        | (refine Steps.ite_R (fun _ => ?_) (fun _ => ?_))
        | exact Steps.throw_bind (by decide)
        | exact Steps.throw_R (by decide)
        | exact Steps.pure_end (fun _ => rfl)
        | (simp only [pure_bind, bind_assoc]))
  · rintro _ s s'' ⟨i, s1, h1, h2⟩
    exact ⟨.int i, by rw [h1, h2]⟩

/-- A computation that leaves the stack as it is (`Steps m (fun _ s s' => s' = s)`): loads, gas, reads
of the state. Other modules add cases (`macro_rules`). -/
macro "steps_keep" : tactic => `(tactic| first
  | exact Steps.forLoads _ | exact Steps.registerCellLoad _ | exact Steps.get | exact Steps.chargeCellCreates _
  | exact Steps.consumeGas _ | exact Steps.checkUnderflow _)

/-- A pop of one value (`Steps m (fun _ s s' => ∃ v, s = s'.push v)`). -/
macro "steps_pop" : tactic => `(tactic| first
  | exact Steps.popNatUpTo _ | exact Steps.popMaybeCell | exact Steps.popInt' | exact Steps.popSlice
  | exact Steps.popCell | exact Steps.popBuilder)

/-- An obligation of a stack written out (`MinMaxOk`, or the stack unchanged): the stacks named by
the combinators substituted, then the case it is. Other modules add cases (`macro_rules`). -/
macro "steps_close" : tactic => `(tactic| (intros; subst_vars; first
  | exact Or.inl ⟨_, _, rfl⟩
  | exact Or.inr rfl
  | exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
  | exact Or.inr (Or.inr (Or.inl rfl))
  | exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
  | rfl
  | trivial))

/-- The exception of a branch of a handler: of code 2 or more (a constant, or the error of a walk of
a dictionary). Other modules add cases (`macro_rules`). -/
macro "steps_err" : tactic => `(tactic| first
  | decide
  | exact dictMinMaxWithCells_real (by assumption)
  | exact dictDeleteWithLoads_real (by assumption))

/-- Follows a VM program of loads, gas, pushes and exceptions with the combinators of a fixed
relation, splitting its `if`s and `match`es; closes the obligations by `steps_close`, the exceptions
by `steps_err`. -/
macro "steps_auto" : tactic => `(tactic| repeat' (first
  | (refine Steps.keep_bind ?_ (fun _ => ?_); steps_keep)
  | (refine Steps.pop_bind ?_ (fun _ => ?_); steps_pop)
  | (refine Steps.push_bind (fun _ => ?_))
  | (refine Steps.pushIntQuiet_bind (fun _ => ?_))
  | (refine Steps.push_end ?_)
  | (refine Steps.pushIntQuiet_end ?_)
  | (refine Steps.pure_end ?_)
  | (refine Steps.keep_end ?_ ?_; steps_keep)
  | (refine Steps.throw_bind ?_ ; steps_err)
  | (refine Steps.throw_R ?_ ; steps_err)
  | (refine Steps.ite_bind (fun _ => ?_) (fun _ => ?_))
  | (refine Steps.ite_R (fun _ => ?_) (fun _ => ?_))
  | (simp only [pure_bind, bind_assoc])
  | steps_close
  | split))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The tail of `DICT*MIN`/`MAX` on any dictionary is framed**, with `MinMaxOk`. -/
theorem Steps.minMaxTail (d : Option Cell) (n : Nat) (fetchMax invertFirst remove byRef intKey : Bool) :
    Steps (DictTail.minMaxTail d n fetchMax invertFirst remove byRef intKey)
      (fun _ s s' => MinMaxOk remove byRef intKey s s') := by
  unfold DictTail.minMaxTail
  simp only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind]
  cases remove <;> cases byRef <;> cases intKey <;>
    (try simp only [eq_self_iff_true, Bool.false_eq_true, if_true, if_false]) <;> steps_auto

/-- **`DICT*MIN`/`MAX` on any stack is framed**: the stack under its key length and dictionary
`MinMaxOk` of its flags. -/
theorem Steps.minMax (args5 : Nat) :
    Steps (DictTail.minMax args5)
      (fun _ s s'' => ∃ s0 v1 v2, s = (s0.push v1).push v2 ∧
        MinMaxOk (decide ((args5 &&& 16) = 16)) (decide ((args5 &&& 1) = 1)) (decide ((args5 &&& 4) = 4)) s0 s'') := by
  unfold DictTail.minMax
  refine Steps.mono (Steps.bind (Steps.checkUnderflow 2) (fun _ => Steps.bind (Steps.popNatUpTo _)
    (fun n => Steps.bind Steps.popMaybeCell (fun d => Steps.minMaxTail d n _ _ _ _ _)))) ?_
  rintro _ s s'' ⟨_, s1, h1, _, s2, ⟨v2, h2⟩, _, s3, ⟨v1, h3⟩, h4⟩
  exact ⟨s3, v1, v2, by rw [← h1, h2, h3], h4⟩

/-- **`DICT*MIN`/`MAX` on any dictionary is framed**: from a stack `s root n` (or any two entries),
`MinMaxOk` of its flags, or an exception of code 2 or more. -/
theorem minMax_framed (args5 : Nat) (remove byRef intKey : Bool)
    (hrm : decide ((args5 &&& 16) = 16) = remove) (hbr : decide ((args5 &&& 1) = 1) = byRef)
    (hik : decide ((args5 &&& 4) = 4) = intKey) (st : VmState) (s : Stack) (a b : Value)
    (hs : st.stack = (s.push a).push b) :
    ExecFramed (.dictGetMinMax args5) (MinMaxOk remove byRef intKey s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.minMax args5 st
  rw [← DictTail.minMaxHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, v1, v2, e, hok⟩ := h2 () h
  rw [hs] at e
  obtain ⟨_, e1⟩ := Array.push_eq_push.mp e
  obtain ⟨_, hs0⟩ := Array.push_eq_push.mp e1
  subst hrm hbr hik
  rw [hs0]
  exact hok

/-- **A run from `DICT*MIN`/`MAX` on any dictionary.** `st` is about to run it (decoded from
`code`, the code after it `rest`) on the stack `s a b`: if `P` holds of every result that commits
nothing and of every run from the state after it with a stack `MinMaxOk remove byRef intKey s`, any
gas, loaded cells and libraries (`after`), it holds of the run. -/
theorem runWith_minMax {st : VmState} {code rest : Slice} {s : Stack} {a b : Value} {args5 : Nat}
    {remove byRef intKey : Bool}
    (hrm : decide ((args5 &&& 16) = 16) = remove) (hbr : decide ((args5 &&& 1) = 1) = byRef)
    (hik : decide ((args5 &&& 4) = 4) = intKey)
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (.dictGetMinMax args5, k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = (s.push a).push b)
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hok : ∀ s' g lc ll n, n < fuel → MinMaxOk remove byRef intKey s s' →
      P (VmState.runWith execInstr n (after st rest s' g lc ll))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := MinMaxOk remove byRef intKey s)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom,
      fun st0 h1 _ => minMax_framed args5 remove byRef intKey hrm hbr hik st0 s a b (h1.trans hs)⟩
    hr hm P hP fuel hok

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_dict_minmax_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S` written
out) is about to run `DICT*MIN`/`MAX` (any form) on a dictionary it does not know: by
`Framed.runWith_minMax`, two goals: `P` of a result that commits nothing, and `P` of the runs from the
state after it with a stack `Framed.MinMaxOk remove byRef intKey s` (the flags of the opcode), any
gas, loaded cells and libraries. -/
elab "vm_dict_minmax_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_dict_minmax_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  let iE ← whnfR iE
  unless iE.isAppOfArity ``Instr.dictGetMinMax 1 do throwError "vm_dict_minmax_any: the instruction is {iE}"
  let some args5 ← evalNat (← instantiateMVars iE.appArg!) |>.run
    | throwError "vm_dict_minmax_any: the opcode's flags are not a numeral"
  let stk ← whnfR (← mkAppM ``VmState.stack #[S])
  unless stk.isAppOfArity ``Array.push 3 do throwError "vm_dict_minmax_any: the stack is not written out"
  let s1 ← whnfR (stk.getArg! 1)
  unless s1.isAppOfArity ``Array.push 3 do throwError "vm_dict_minmax_any: the stack is not written out"
  let boolE (b : Bool) : Expr := if b then mkConst ``Bool.true else mkConst ``Bool.false
  let remove := boolE (args5 &&& 16 == 16)
  let byRef := boolE (args5 &&& 1 == 1)
  let intKey := boolE (args5 &&& 4 == 4)
  -- `decide ((args5 &&& bit) = bit) = flag` by `rfl`: the application checks it (`isDefEq`)
  let hrm ← mkEqRefl remove
  let hbr ← mkEqRefl byRef
  let hik ← mkEqRefl intKey
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
  let f ← mkAppOptM ``Framed.runWith_minMax #[S, none, none, s1.getArg! 1, s1.getArg! 2, stk.getArg! 2,
    iE.appArg!, remove, byRef, intKey, hrm, hbr, hik, hcc, hcp, hbitsNe, hverLe, hdecEx, hchain, hc2, hcom,
    hr, hm, hs, motive]
  let (f1, goals1) ← Exec.applyRest f 1 #[fuel]
  let (pf, goals2) ← Exec.applyRest f1 1 #[]
  let goals := goals1 ++ goals2
  unless ← isDefEq (← inferType pf) t do throwError "vm_dict_minmax_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

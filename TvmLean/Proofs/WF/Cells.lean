import TvmLean.Proofs.WF.Step

/-!
# Cells, slices and builders an instruction builds

Lemmas in the shape `wf_vc` (`grind`) uses them, for the instructions that read slices and build
cells and builders (the Cell and CellOp families, and later the dictionary and message families):
each concludes that a cell, slice or builder an instruction builds is well-formed from the checks
the instruction makes (`haveBits`, `haveRefs`, `canExtendBy`) and the sizes of what it stores
(`intToBitsTwos_size`, `leBytesToBitString_size_le`, ...). `Builder.finalizeCopy_WF`: a cell
`ENDXC` finalizes, ordinary or special, is well-formed (a special one is returned only when its
level information computes; `Except.forIn_list_inv` is the invariant of its loop). `wf_cells` is
`wf_vc` with them (`wf_cells [h₁, h₂]` with more).

Dictionary lookups and message addresses: `dictLookupWithCells_WF` (the value the lookup that
records its cells finds in a well-formed dictionary is a well-formed slice),
`Slice.skipMessageAddr_WF`, `Slice.parseMessageAddr_WF` (C++ `skip_message_addr`,
`parse_message_addr`), with `Slice.takeBitsAsNatCellUnd_wfspec` for `mvcgen` in `Except`.

Tools for the handlers: `VM.spec_mono`, the rule of consequence, to bind the steps of a handler
by hand where `mvcgen` must not look (a hash); `VM.monadLift_except_spec`, the specification of a
value of `Except` lifted into the VM; `generalize_opaque x := t`, which makes a function `t` (a
hash, `IntVal.num`, a dictionary lookup) a variable in the goal so that neither `mvcgen` nor the
kernel computes with it.
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

/-- The rule of consequence for the triples of the VM monad with pure assertions: for a handler
whose hashes `mvcgen` must not see, the steps are bound by hand (`Triple.bind`). -/
theorem VM.spec_mono {α : Type} {m : VM α} {P P' : VmState → Prop} {Q Q' : α → VmState → Prop}
    {E E' : Excno → VmState → Prop}
    (h : ⦃fun st => ⌜P st⌝⦄ m ⦃post⟨fun a st => ⌜Q a st⌝, fun e st => ⌜E e st⌝⟩⦄)
    (hp : ∀ st, P' st → P st) (hq : ∀ a st, Q a st → Q' a st) (he : ∀ e st, E e st → E' e st) :
    ⦃fun st => ⌜P' st⌝⦄ m ⦃post⟨fun a st => ⌜Q' a st⌝, fun e st => ⌜E' e st⌝⟩⦄ := by
  apply VM.triple_of_run
  intro st hs
  have := VM.triple_run h st (hp st hs)
  revert this
  rcases m.run st with ⟨r, st'⟩
  cases r
  · exact he _ _
  · exact hq _ _

theorem intToBitsTwos_size {n : Int} {bits : Nat} {bs : BitString}
    (h : intToBitsTwos n bits = .ok bs) : bs.size = bits := by
  unfold intToBitsTwos at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h; simp_all
  · split at h
    · cases h
    · split at h <;> cases h <;> simp

theorem Slice.readBits_size {s : Slice} {n : Nat} (h : s.haveBits n = true) :
    (s.readBits n).size = n := by
  rw [Slice.haveBits_iff] at h
  simp [Slice.readBits]; omega

theorem Cell.mkOrdinary_readBits_WF {s : Slice} (h : s.WF) (n : Nat) :
    (Cell.mkOrdinary (s.readBits n) #[]).WF :=
  Cell.mkOrdinary_WF (Slice.readBits_size_le h n) (by simp) (by simp)

theorem Cell.mkOrdinary_extract_WF {s : Slice} (h : s.WF) (i j : Nat) :
    (Cell.mkOrdinary (s.cell.bits.extract i j) #[]).WF :=
  Cell.mkOrdinary_WF (by have := h.1.bits_le; simp; omega) (by simp) (by simp)

theorem Slice.incRefPos_WF {s : Slice} (h : s.WF) (hr : s.haveRefs 1 = true) :
    ({ s with refPos := s.refPos + 1 } : Slice).WF :=
  Slice.withRefPos_WF h ((Slice.haveRefs_iff s 1).mp hr)

theorem Builder.storeBits_WF_of {b : Builder} {bs : BitString} {n : Nat} (hb : b.WF)
    (hc : b.canExtendBy n = true) (hs : bs.size = n) : (b.storeBits bs).WF :=
  Builder.storeBits_WF b bs hb (hs ▸ hc)

theorem Builder.pushRef_WF_of {b : Builder} {c : Cell} (hb : b.WF) (hc : c.WF)
    (h : b.canExtendBy 0 1 = true) : ({ b with refs := b.refs.push c } : Builder).WF :=
  Builder.pushRef_WF b c hb hc h

theorem Cell.mkOrdinary_extract2_WF {s : Slice} (h : s.WF) (i j k l : Nat) :
    (Cell.mkOrdinary (s.cell.bits.extract i j) (s.cell.refs.extract k l)).WF :=
  Cell.mkOrdinary_WF (by have := h.1.bits_le; simp; omega) (by have := h.1.refs_le; simp; omega)
    (WF.forall_mem_extract h.1.refs_wf _ _)

/-- Appending the bits and references of a cell that fits keeps a builder well-formed. -/
theorem Builder.appendCell_WF {b : Builder} {c : Cell} (hb : b.WF) (hc : c.WF)
    (h : b.canExtendBy c.bits.size c.refs.size = true) :
    ({ bits := b.bits ++ c.bits, refs := b.refs ++ c.refs } : Builder).WF :=
  Builder.append_WF (c := { bits := c.bits, refs := c.refs }) hb ⟨hc.bits_le, hc.refs_le, hc.refs_wf⟩ h

/-- The cell of a part of a well-formed slice (`Slice.prefixCell`). -/
theorem Slice.prefixCell_WF {start : Slice} (h : start.WF) (stop : Slice) :
    (Slice.prefixCell start stop).WF :=
  Cell.mkOrdinary_extract2_WF h _ _ _ _

/-- Moving both positions within the slice keeps it well-formed. -/
theorem Slice.addPos_WF {s : Slice} (h : s.WF) {n m : Nat} (hn : s.haveBits n = true)
    (hm : s.haveRefs m = true) :
    ({ s with bitPos := s.bitPos + n, refPos := s.refPos + m } : Slice).WF :=
  ⟨h.1, (Slice.haveBits_iff s n).mp hn, (Slice.haveRefs_iff s m).mp hm⟩

theorem Slice.addBitPos_WF {s : Slice} (h : s.WF) {n : Nat} (hn : s.haveBits n = true) :
    ({ s with bitPos := s.bitPos + n } : Slice).WF :=
  ⟨h.1, (Slice.haveBits_iff s n).mp hn, h.2.2⟩

theorem Slice.countLeading_le (s : Slice) (b : Bool) :
    s.countLeading b ≤ s.cell.bits.size - s.bitPos := by
  have := countWhile_le (s.cell.bits.size - s.bitPos) (fun k => s.cell.bits[s.bitPos + k]! == b) 0
  unfold Slice.countLeading; omega

/-- Skipping the leading bits equal to `b` keeps a slice well-formed. -/
theorem Slice.advanceBits_countLeading_WF {s : Slice} (h : s.WF) (b : Bool) :
    (s.advanceBits (s.countLeading b)).WF :=
  Slice.advanceBits_WF h (by have := Slice.countLeading_le s b; have := h.2.1; omega)

theorem Builder.pushRef2_WF_of {b : Builder} {c d : Cell} (hb : b.WF) (hc : c.WF) (hd : d.WF)
    (h : b.canExtendBy 0 2 = true) : ({ b with refs := (b.refs.push c).push d } : Builder).WF := by
  rw [Builder.canExtendBy_iff] at h
  refine ⟨hb.1, by simp; omega, ?_⟩
  simp only [Array.forall_mem_push]
  exact ⟨hd, hc, hb.refs_wf⟩

/-- An invariant of the state of a loop over a list in `Except`, kept by every step. -/
theorem Except.forIn_list_inv {ε α β : Type} {P : β → Prop} (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b s, P b → f a b = .ok s → P s.value) :
    ∀ (l : List α) (init : β), P init → ∀ r, forIn l init f = .ok r → P r := by
  intro l
  induction l with
  | nil =>
    intro init h r hr
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hr
    exact hr ▸ h
  | cons a l ih =>
    intro init h r hr
    simp only [List.forIn_cons, bind, Except.bind] at hr
    cases hs : f a init with
    | error e => simp [hs] at hr
    | ok s =>
      have := hf a init s h hs
      cases s with
      | done b =>
        simp only [hs, pure, Except.pure, Except.ok.injEq] at hr
        exact hr ▸ this
      | yield b =>
        simp only [hs] at hr
        exact ih b this r hr

/-- A cell finalized from a well-formed builder, ordinary or special (`ENDXC`), is well-formed: a
special cell is returned only when its level information computes. -/
theorem Builder.finalizeCopy_WF {b : Builder} (hb : b.WF) {special : Bool} {c : Cell}
    (h : b.finalizeCopy special = .ok c) : c.WF := by
  unfold Builder.finalizeCopy at h
  split at h
  · cases hf : b.finalizeChecked with
    | error e => simp [hf, bind, Except.bind] at h
    | ok c' =>
      simp only [hf, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ b.finalizeChecked_WF hb c' hf
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp at h
    · rename_i r hr
      have key : ∀ c', r.1 = some c' → c'.WF := by
        rw [Std.Range.forIn_eq_forIn_range'] at hr
        refine Except.forIn_list_inv (P := fun r : MProd (Option Cell) PUnit =>
          ∀ c, r.1 = some c → c.WF) _ ?_ _ _ (by simp) r hr
        intro m r' s _ hs
        split at hs
        · rename_i info hinfo
          split at hs
          · simp only [Except.ok.injEq] at hs
            subst hs
            intro c hc
            simp only [ForInStep.value, Option.some.injEq] at hc
            exact hc ▸ Cell.WF_of_computeLevelInfo? _ info hinfo
          · cases hs
        · simp only [Except.ok.injEq] at hs
          subst hs
          simp
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i a ha
        simp only [Except.ok.injEq] at h
        exact h ▸ key a ha

theorem Builder.storeBits_WF_le {b : Builder} {bs : BitString} {n : Nat} (hb : b.WF)
    (hc : b.canExtendBy n = true) (hs : bs.size ≤ n) : (b.storeBits bs).WF := by
  rw [Builder.canExtendBy_iff] at hc
  exact Builder.storeBits_WF b bs hb (by rw [Builder.canExtendBy_iff]; omega)

theorem foldl_append_extract_size_le (bs : BitString) (g : Nat → Nat) :
    ∀ (l : List Nat) (init : BitString),
      (l.foldl (fun b a => b ++ bs.extract (g a) (g a + 8)) init).size ≤ init.size + 8 * l.length := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons a l ih =>
    intro init
    simp only [List.foldl_cons, List.length_cons]
    have := ih (init ++ bs.extract (g a) (g a + 8))
    simp only [Array.size_append, Array.size_extract] at this
    omega

/-- The little-endian reordering of `bytes` bytes (`STLE`) has at most `bytes * 8` bits. -/
theorem leBytesToBitString_size_le (bs : BitString) (bytes : Nat) :
    (leBytesToBitString bs bytes).size ≤ bytes * 8 := by
  simp only [leBytesToBitString, Id.run, Std.Range.forIn_eq_forIn_range']
  simp [List.forIn_pure_yield_eq_foldl]
  have := foldl_append_extract_size_le bs (fun a => bytes * 8 - (a + 1) * 8) (List.range' 0 bytes) #[]
  simp at this
  exact (Nat.mul_comm bytes 8).symm ▸ this

/-- A value of `Except` lifted into the VM (`LDVARINT` reads a length): the state does not
change. -/
@[spec] theorem VM.monadLift_except_spec {α : Type} (x : Except Excno α) :
    ⦃fun st => ⌜st.WF⌝⦄ (MonadLift.monadLift x : VM α)
      ⦃post⟨fun a st => ⌜st.WF ∧ x = .ok a⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  apply VM.triple_of_run
  intro st hs
  cases x <;> simp_all [MonadLift.monadLift, ExceptT.run, ExceptT.mk, pure, StateT.pure]

theorem Slice.takeBitsAsNatCellUnd_WF {s : Slice} {n v : Nat} {s' : Slice} (hs : s.WF)
    (h : s.takeBitsAsNatCellUnd n = .ok (v, s')) : s'.WF := by
  obtain ⟨h1, h2, h3, h4⟩ := Slice.takeBitsAsNatCellUnd_ok h
  exact ⟨h1 ▸ hs.1, by rw [h1, h2]; exact h4, by rw [h1, h3]; exact hs.2.2⟩

/-! The cells and slices an instruction carries (`Instr.WF`). -/

@[simp] theorem Instr.wf_stSliceConst (s : Slice) : (Instr.stSliceConst s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_sdBeginsConst (q : Bool) (s : Slice) :
    (Instr.sdBeginsConst q s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_pushSliceConst (s : Slice) : (Instr.pushSliceConst s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_pushCont (s : Slice) : (Instr.pushCont s).WF ↔ s.WF := Iff.rfl
@[simp] theorem Instr.wf_pushRef (c : Cell) : (Instr.pushRef c).WF ↔ c.WF := Iff.rfl
@[simp] theorem Instr.wf_pushRefSlice (c : Cell) : (Instr.pushRefSlice c).WF ↔ c.WF := Iff.rfl
@[simp] theorem Instr.wf_pushRefCont (c : Cell) : (Instr.pushRefCont c).WF ↔ c.WF := Iff.rfl
@[simp] theorem Instr.wf_dictPushConst (c : Cell) (n : Nat) :
    (Instr.dictPushConst c n).WF ↔ c.WF := Iff.rfl
@[simp] theorem Instr.wf_cellExt_stRefConst (c : Cell) :
    (Instr.cellExt (.stRefConst c)).WF ↔ c.WF := Iff.rfl
@[simp] theorem Instr.wf_cellExt_stRef2Const (c d : Cell) :
    (Instr.cellExt (.stRef2Const c d)).WF ↔ c.WF ∧ d.WF := Iff.rfl

/-- `wf_vc` with the lemmas on the cells, slices and builders instructions build; `wf_cells [h₁, h₂]`
gives it more lemmas. -/
syntax "wf_cells" (" [" Lean.Parser.Tactic.grindParam,* "]")? : tactic

macro_rules
  | `(tactic| wf_cells) => `(tactic| wf_cells [])
  | `(tactic| wf_cells [$ts,*]) => `(tactic|
    wf_vc [→ intToBitsTwos_size, Slice.readBits_size, Cell.mkOrdinary_readBits_WF,
      Cell.mkOrdinary_extract_WF, Cell.mkOrdinary_extract2_WF, Slice.incRefPos_WF,
      Builder.storeBits_WF_of, Builder.pushRef_WF_of, Builder.append_WF, Builder.appendCell_WF,
      Builder.empty_WF, Builder.finalize_WF, Slice.toCellRemaining_WF, Slice.advanceBits_WF',
      Slice.ofCell_WF_iff, Slice.WF.ref!, Cell.WF.ref!, natToBits_size, Instr.wf_stSliceConst,
      Instr.wf_sdBeginsConst, Instr.wf_pushSliceConst, Instr.wf_pushRef,
      Instr.wf_cellExt_stRefConst, Instr.wf_cellExt_stRef2Const, Slice.prefixCell_WF,
      Slice.addPos_WF, Slice.addBitPos_WF, Slice.advanceBits_countLeading_WF,
      Builder.pushRef2_WF_of, → Builder.finalizeCopy_WF, Builder.storeBits_WF_le,
      leBytesToBitString_size_le, → Slice.takeBitsAsNatCellUnd_WF, $ts,*])

/-! ## Dictionary lookups and message addresses -/

/-- A value the lookup that records its cells (`dictLookupWithCells`, for gas) finds in a
well-formed dictionary is a well-formed slice. -/
theorem dictLookupAuxWithCellsF_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve) :
    ∀ (f : Nat) (cell : Cell) (key : BitString) (pos remaining : Nat) (s : Slice)
      (cells : Array Cell), cell.WF →
      dictLookupAuxWithCellsF resolve f cell key pos remaining = .ok (some s, cells) → s.WF := by
  intro f
  induction f with
  | zero => intro cell key pos remaining s cells _ h; simp [dictLookupAuxWithCellsF] at h
  | succ f ih =>
    intro cell key pos remaining s cells hc h
    simp only [dictLookupAuxWithCellsF, dictLookupWithCellsStep] at h
    cases hl : parseDictLabel cell remaining resolve with
    | error e => simp [hl, bind, Except.bind] at h
    | ok lbl =>
      obtain ⟨hlw, hlb⟩ := parseDictLabel_WF hr hc hl
      simp only [hl, bind, Except.bind] at h
      cases hv : dictValidateNodeExt lbl remaining with
      | error e => simp [hv] at h
      | ok rem0 =>
        simp only [hv] at h
        by_cases hm : dictLabelMatches lbl key pos = true
        · simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h0 : rem0 = 0
          · simp only [h0, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
              Option.some.injEq] at h
            rw [← h.1]
            exact Slice.advanceBits_WF hlw hlb
          · simp only [h0, ↓reduceIte] at h
            by_cases hk : pos + lbl.len ≥ key.size
            · simp [hk, pure, Except.pure] at h
            · simp only [hk, ↓reduceDIte] at h
              repeat' split at h
              all_goals first
                | (simp at h; done)
                | (rename_i p hp
                   simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                   exact ih _ key _ _ s p.2 (hlw.ref! _) (by rw [hp, ← h.1]))
        · simp [hm, pure, Except.pure] at h

theorem dictLookupWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {key : BitString} {s : Slice}
    {cells : Array Cell} (h : dictLookupWithCells root key resolve = .ok (some s, cells)) : s.WF := by
  unfold dictLookupWithCells at h
  split at h
  · simp [pure, Except.pure] at h
  · exact dictLookupAuxWithCellsF_WF hr _ _ _ _ _ s cells (hroot _ rfl) h

/-- `Slice.takeBitsAsNatCellUnd` in the `Except` monad, for `mvcgen`: the rest of a well-formed
slice is well-formed. -/
theorem Slice.takeBitsAsNatCellUnd_wfspec (s : Slice) (n : Nat) (hs : s.WF) :
    ⦃⌜True⌝⦄ s.takeBitsAsNatCellUnd n ⦃post⟨fun r => ⌜r.2.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
  Except.triple_of fun ⟨_, _⟩ h => Slice.takeBitsAsNatCellUnd_WF hs h

/-- C++ `skip_message_addr`: the rest of a well-formed slice is well-formed. -/
theorem Slice.skipMessageAddr_WF {s s' : Slice} {gv : Nat} (hs : s.WF)
    (h : s.skipMessageAddr gv = .ok s') : s'.WF := by
  refine Except.of_triple (P := Slice.WF) ?_ h
  mvcgen [Slice.skipMessageAddr, Slice.skipMaybeAnycast, Slice.takeAnycastDepth,
    Slice.takeBitsAsNatCellUnd_wfspec]
  all_goals wf_cells

/-- C++ `parse_message_addr`: the parts of an address (integers and slices of new cells) and the
rest of a well-formed slice are well-formed. -/
theorem Slice.parseMessageAddr_WF {s : Slice} {gv : Nat} (hs : s.WF) {t : Array Value}
    {s' : Slice} (h : s.parseMessageAddr gv = .ok (t, s')) : (∀ v ∈ t, v.WF) ∧ s'.WF := by
  refine Except.of_triple (P := fun r : Array Value × Slice => (∀ v ∈ r.1, v.WF) ∧ r.2.WF) ?_ h
  mvcgen [Slice.parseMessageAddr, Slice.parseMaybeAnycast, Slice.takeAnycastDepth,
    Slice.takeBitsAsNatCellUnd_wfspec]
  all_goals wf_cells [List.not_mem_nil]

/-! ## Values `mvcgen` and the kernel must not compute -/

theorem WF.forall_inst {α : Sort u} {P : α → Prop} (h : ∀ x, P x) (a : α) : P a := h a

open Lean Elab Tactic Meta in
/-- `generalize_opaque x := t at h₁ h₂`: replaces `t` (a constant such as `IntVal.num` or a hash
function) by a new variable `x` in the goal and in the hypotheses `hᵢ`, like `generalize`, but so
that the proof stays abstract over `x`: it is `WF.forall_inst (fun x => proof) t`, not the proof
with `t` substituted back. With `generalize`, the kernel checks the proof with `t` in place and may
compute with it (a hash; an integer `Int.ofNat n` that `VM.pushIntQuiet` compares with `2 ^ 256`:
`(kernel) deep recursion detected`); with `generalize_opaque` neither `mvcgen` nor the kernel can.
Does nothing if `t` does not occur. -/
syntax (name := generalizeOpaque) "generalize_opaque " ident " := " term
  (" at" (ppSpace colGt ident)+)? : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| generalize_opaque $x:ident := $t:term $[at $hs:ident*]?) => do
    let hs := hs.getD #[]
    let fvars ← withMainContext <| hs.mapM fun h => getFVarId h
    let (_, g) ← (← getMainGoal).revert fvars (preserveOrder := true)
    setGoals [g]
    withMainContext do
      let e ← Tactic.elabTerm t none
      let e ← instantiateMVars e
      let ty ← inferType e
      let tgt ← instantiateMVars (← g.getType)
      let abst ← kabstract tgt e
      if !abst.hasLooseBVars then
        let (_, g') ← g.introNP fvars.size
        replaceMainGoal [g']
        return
      let P := Lean.mkLambda x.getId .default ty abst
      let ng ← mkFreshExprSyntheticOpaqueMVar (Lean.mkForall x.getId .default ty abst) (← g.getTag)
      g.assign (← mkAppOptM ``WF.forall_inst #[ty, P, ng, e])
      let (_, ng) ← ng.mvarId!.intro x.getId
      let (_, ng) ← ng.introNP fvars.size
      replaceMainGoal [ng]

end TvmLean

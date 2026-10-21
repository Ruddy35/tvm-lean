import TvmLean.Semantics

/-!
# Well-formed cells and builders

A TVM cell holds at most 1023 data bits and 4 references (C++ `CellBuilder` and `DataCell::create`);
`Cell.WF` states this of a cell and of every cell below it, `Builder.WF` of a builder. The lemmas show
that the builder primitives keep the bounds under the checks the instructions make before them
(`Builder.canExtendBy`, as C++ `CellBuilder::can_extend_by`), and that a cell whose level information
computes — every cell with a hash — is well-formed.
-/

namespace TvmLean

/-- At most 1023 bits and 4 references, here and in every cell below. -/
inductive Cell.WF : Cell → Prop
  | intro (c : Cell) : c.bits.size ≤ 1023 → c.refs.size ≤ 4 → (∀ r ∈ c.refs, Cell.WF r) → Cell.WF c

/-- A builder within the bounds of a cell, its references well-formed. -/
def Builder.WF (b : Builder) : Prop :=
  b.bits.size ≤ 1023 ∧ b.refs.size ≤ 4 ∧ ∀ r ∈ b.refs, Cell.WF r

theorem Builder.empty_WF : Builder.empty.WF := by
  simp [Builder.WF, Builder.empty]

theorem Builder.canExtendBy_iff (b : Builder) (n r : Nat) :
    b.canExtendBy n r = true ↔ b.bits.size + n ≤ 1023 ∧ b.refs.size + r ≤ 4 := by
  simp [Builder.canExtendBy]

/-- Storing bits that fit (`canExtendBy`) keeps a builder well-formed. -/
theorem Builder.storeBits_WF (b : Builder) (bs : BitString) (hb : b.WF)
    (h : b.canExtendBy bs.size = true) : (b.storeBits bs).WF := by
  rw [Builder.canExtendBy_iff] at h
  obtain ⟨_, hr, hc⟩ := hb
  refine ⟨?_, hr, hc⟩
  simp [Builder.storeBits]; omega

/-- Storing a well-formed reference that fits keeps a builder well-formed. -/
theorem Builder.pushRef_WF (b : Builder) (c : Cell) (hb : b.WF) (hc : c.WF)
    (h : b.canExtendBy 0 1 = true) : ({ b with refs := b.refs.push c } : Builder).WF := by
  rw [Builder.canExtendBy_iff] at h
  obtain ⟨hbits, _, hrefs⟩ := hb
  refine ⟨hbits, ?_, ?_⟩
  · simp; omega
  · intro r hr
    rcases Array.mem_push.mp hr with hr | hr
    · exact hrefs r hr
    · exact hr ▸ hc

/-- A well-formed builder finalizes to a well-formed cell. -/
theorem Builder.finalize_WF (b : Builder) (hb : b.WF) : b.finalize.WF := by
  obtain ⟨h1, h2, h3⟩ := hb
  exact .intro _ h1 h2 h3

theorem Builder.finalizeChecked_WF (b : Builder) (hb : b.WF) (c : Cell) (h : b.finalizeChecked = .ok c) :
    c.WF := by
  unfold Builder.finalizeChecked at h
  split at h
  · cases h; exact b.finalize_WF hb
  · cases h


/-- Every reference of a list whose level information computes has its level information. -/
theorem Cell.childLevelInfos?_ok (l : List Cell) (is : Array CellLevelInfo)
    (h : Cell.childLevelInfos? l = .ok is) : ∀ r ∈ l, ∃ i, Cell.computeLevelInfo? r = .ok i := by
  induction l generalizing is with
  | nil => simp
  | cons a l ih =>
    rw [Cell.childLevelInfos?] at h
    cases ha : Cell.computeLevelInfo? a with
    | error e => rw [ha] at h; cases h
    | ok ia =>
      cases hl : Cell.childLevelInfos? l with
      | error e => rw [ha] at h; simp [hl] at h; cases h
      | ok il =>
        intro r hr
        rcases List.mem_cons.mp hr with hr | hr
        · exact hr ▸ ⟨ia, ha⟩
        · exact ih il hl r hr

/-- A cell whose level information computes (every cell with a hash: `Cell.hashBytes`, a BOC, ...)
is well-formed: `computeLevelInfo?` rejects more than 4 references or 1023 bits, in every cell below. -/
theorem Cell.WF_of_computeLevelInfo? : ∀ (c : Cell) (i : CellLevelInfo), Cell.computeLevelInfo? c = .ok i → c.WF
  | ⟨bits, ⟨refs⟩, sp, lm⟩, i, h => by
    rw [Cell.computeLevelInfo?] at h
    split at h
    · cases h
    · rename_i hr
      split at h
      · cases h
      · rename_i hb
        cases hc : Cell.childLevelInfos? refs with
        | error e => rw [hc] at h; cases h
        | ok is =>
          have hall := Cell.childLevelInfos?_ok refs is hc
          refine .intro _ (by omega) (by simp at hr ⊢; omega) ?_
          intro r hmem
          have hmem' : r ∈ refs := by simpa using hmem
          obtain ⟨ir, hir⟩ := hall r hmem'
          have : sizeOf r < sizeOf (⟨bits, ⟨refs⟩, sp, lm⟩ : Cell) := by
            have := List.sizeOf_lt_of_mem hmem'
            simp; omega
          exact Cell.WF_of_computeLevelInfo? r ir hir
termination_by c => sizeOf c

end TvmLean

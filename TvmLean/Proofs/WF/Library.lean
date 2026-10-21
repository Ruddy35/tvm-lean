import TvmLean.Proofs.WF.Defs
import Std.Tactic.Do

/-!
# Library cells resolve to well-formed cells

A cell the VM loads as a slice may be a library cell, which it replaces by the root of its library,
looked up in the VM's library collections (`libraryResolveLoads`, C++ `load_cell_slice_impl` with
`VmState::load_library`). The root is a reference of the value a dictionary lookup finds in a
collection, so it is well-formed when the collections are:

* `parseDictLabel_WF`: the label of a dictionary node leaves a well-formed slice with the bits it
  stores within the cell;
* `dictLookupAuxF_WF`, `dictLookup_WF`: a value found in a well-formed dictionary is a well-formed
  slice (whatever resolver the lookup uses, if it keeps cells well-formed);
* `lookupLibraryIn?_WF`, `libraryResolveLoads_WF`: a library root found in well-formed collections is
  well-formed, and so is the cell a well-formed cell resolves to.
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

/-- A cell loader that maps well-formed cells to well-formed cells. -/
def ResolverWF (resolve : Cell → Except Excno Cell) : Prop :=
  ∀ c c', c.WF → resolve c = .ok c' → c'.WF

theorem Cell.rejectSpecial_WF : ResolverWF Cell.rejectSpecial := by
  intro c c' hc h
  unfold Cell.rejectSpecial at h
  split at h
  · cases h
  · cases h; exact hc

theorem Slice.takeBitsAsNatCellUnd_ok {s : Slice} {n v : Nat} {s' : Slice}
    (h : s.takeBitsAsNatCellUnd n = .ok (v, s')) :
    s'.cell = s.cell ∧ s'.bitPos = s.bitPos + n ∧ s'.refPos = s.refPos ∧
      s.bitPos + n ≤ s.cell.bits.size := by
  unfold Slice.takeBitsAsNatCellUnd at h
  split at h
  · rename_i hb
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, (Slice.haveBits_iff s n).mp hb⟩
  · cases h

/-- A triple of the `Except` monad as a statement about its value. -/
theorem Except.of_triple {ε α : Type} {x : Except ε α} {P : α → Prop}
    (h : ⦃⌜True⌝⦄ x ⦃post⟨fun a => ⌜P a⌝, fun _ => ⌜True⌝⟩⦄) {a : α} (hx : x = .ok a) : P a := by
  have := h trivial
  subst hx
  simpa [wp, SPred.down_pure] using this

theorem Except.triple_of {ε α : Type} {x : Except ε α} {P : α → Prop}
    (h : ∀ a, x = .ok a → P a) : ⦃⌜True⌝⦄ x ⦃post⟨fun a => ⌜P a⌝, fun _ => ⌜True⌝⟩⦄ := by
  intro _
  cases hx : x with
  | error e => simp [wp, Id.run]
  | ok a => simpa [wp, Id.run] using h a hx

theorem Slice.takeBitsAsNatCellUnd_spec (s : Slice) (n : Nat) :
    ⦃⌜True⌝⦄ s.takeBitsAsNatCellUnd n ⦃post⟨fun r => ⌜r.2.cell = s.cell ∧ r.2.bitPos = s.bitPos + n ∧
      r.2.refPos = s.refPos ∧ s.bitPos + n ≤ s.cell.bits.size⌝, fun _ => ⌜True⌝⟩⦄ :=
  Except.triple_of fun ⟨_, _⟩ h => Slice.takeBitsAsNatCellUnd_ok h

/-- The label of a node of a well-formed dictionary: the rest of the node is a well-formed slice,
the bits the label stores within it. -/
theorem parseDictLabel_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {cell : Cell} (hc : cell.WF) {maxLen : Nat} {lbl : DictLabel}
    (h : parseDictLabel cell maxLen resolve = .ok lbl) :
    lbl.remainder.WF ∧ lbl.remainder.bitPos + lbl.storedBits ≤ lbl.remainder.cell.bits.size := by
  unfold parseDictLabel at h
  cases hres : resolve cell with
  | error e => simp [hres, bind, Except.bind] at h
  | ok c' =>
    have hc' : c'.WF := hr cell c' hc hres
    simp only [hres, bind, Except.bind] at h
    refine Except.of_triple (P := fun lbl : DictLabel =>
      lbl.remainder.WF ∧ lbl.remainder.bitPos + lbl.storedBits ≤ lbl.remainder.cell.bits.size) ?_ h
    clear h
    have hb := hc'.bits_le
    mvcgen
    all_goals simp_all [Slice.WF, Slice.advanceBits, Slice.ofCell, Slice.haveBits]
    · omega
    · rename_i r _ _ _ _ ht _ _ _
      obtain ⟨h1, h2, h3, h4⟩ := Slice.takeBitsAsNatCellUnd_ok (v := r.1) (s' := r.2) ht
      simp only at h1 h2 h3 h4
      refine ⟨h1 ▸ hc', ?_, ?_⟩ <;> simp [h1] <;> omega
    · rename_i r r' _ _ _ _ ht ht' _ _
      obtain ⟨h1, h2, h3, h4⟩ := Slice.takeBitsAsNatCellUnd_ok (v := r.1) (s' := r.2) ht
      obtain ⟨h1', h2', h3', h4'⟩ := Slice.takeBitsAsNatCellUnd_ok (v := r'.1) (s' := r'.2) ht'
      simp only at h1 h2 h3 h4
      refine ⟨⟨by rw [h1', h1]; exact hc', ?_, ?_⟩, ?_⟩ <;> simp [h1', h1] at h4' ⊢ <;> omega

/-- A value found in a well-formed dictionary is a well-formed slice. -/
theorem dictLookupAuxF_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve) :
    ∀ (f : Nat) (cell : Cell) (key : BitString) (pos remaining : Nat) (s : Slice), cell.WF →
      dictLookupAuxF resolve f cell key pos remaining = .ok (some s) → s.WF := by
  intro f
  induction f with
  | zero => intro cell key pos remaining s _ h; simp [dictLookupAuxF] at h
  | succ f ih =>
    intro cell key pos remaining s hc h
    simp only [dictLookupAuxF, dictLookupStep] at h
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
          · simp only [h0, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
            rw [← h]
            exact Slice.advanceBits_WF hlw hlb
          · simp only [h0, ↓reduceIte] at h
            by_cases hk : pos + lbl.len ≥ key.size
            · simp [hk, pure, Except.pure] at h
            · simp only [hk, ↓reduceDIte] at h
              exact ih _ key _ _ s (hlw.ref! _) h
        · simp [hm, pure, Except.pure] at h

theorem dictLookup_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {key : BitString} {s : Slice}
    (h : dictLookup root key resolve = .ok (some s)) : s.WF := by
  unfold dictLookup at h
  split at h
  · simp [pure, Except.pure] at h
  · exact dictLookupAuxF_WF hr _ _ _ _ _ s (hroot _ rfl) h

/-- A library root found in a well-formed collection is well-formed. -/
theorem lookupLibraryIn?_WF {hash : BitString} {coll root : Cell} (hc : coll.WF)
    (h : lookupLibraryIn? hash coll = some root) : root.WF := by
  unfold lookupLibraryIn? at h
  split at h
  · cases h
  · cases h
  · rename_i val hv
    have hval : val.WF := dictLookup_WF Cell.rejectSpecial_WF (by intro c hc'; cases hc'; exact hc) hv
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h; exact hval.ref! _
      · cases h

/-- The second component of a fold stays a well-formed cell if every step keeps it one. -/
theorem foldl_snd_WF {β : Type} {l : Array Cell} {init : β × Option Cell}
    {step : β × Option Cell → Cell → β × Option Cell}
    (hinit : ∀ r, init.2 = some r → r.WF)
    (hstep : ∀ acc lib, lib ∈ l → (∀ r, acc.2 = some r → r.WF) → ∀ r, (step acc lib).2 = some r → r.WF) :
    ∀ r, (l.foldl step init).2 = some r → r.WF :=
  Array.foldl_induction (motive := fun _ acc => ∀ r, acc.2 = some r → r.WF) hinit
    (fun _ b hb => hstep b _ (Array.getElem_mem _) hb)

/-- A well-formed cell resolves to a well-formed cell, when the collections are well-formed. -/
theorem libraryResolveLoadsAux_WF {libs : Array Cell} (hl : ∀ c ∈ libs, c.WF) (gv : Nat)
    (refused : Array BitString) :
    ∀ (fuel : Nat) (c : Cell) (loads : Array LibraryLoadStep) (r : Cell), c.WF →
      (libraryResolveLoadsAux libs gv refused fuel c loads).2 = .ok r → r.WF := by
  intro fuel
  induction fuel with
  | zero => intro c loads r _ h; simp [libraryResolveLoadsAux] at h
  | succ fuel ih =>
    intro c loads r hc h
    simp only [libraryResolveLoadsAux] at h
    split at h
    · cases h; exact hc
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i root hroot
            have hrw : root.WF := by
              refine foldl_snd_WF (by intro r hr; cases hr) ?_ root hroot
              intro acc lib hlib hacc r hr
              obtain ⟨ls, found⟩ := acc
              cases found with
              | some x => exact hacc r hr
              | none => exact lookupLibraryIn?_WF (hl lib hlib) hr
            split at h
            · exact Cell.rejectSpecial_WF _ _ hrw h
            · exact ih _ _ r hrw h

theorem libraryResolveLoads_WF {libs : Array Cell} (hl : ∀ c ∈ libs, c.WF) {gv : Nat} {c r : Cell}
    {refused : Array BitString} (hc : c.WF) (h : (libraryResolveLoads libs gv c refused).2 = .ok r) :
    r.WF :=
  libraryResolveLoadsAux_WF hl gv refused _ c #[] r hc h

/-- The resolver of a VM whose collections are well-formed keeps cells well-formed. -/
theorem libraryResolver_WF {libs : Array Cell} (hl : ∀ c ∈ libs, c.WF) (gv : Nat)
    (refused : Array BitString) :
    ResolverWF fun c => (libraryResolveLoads libs gv c refused).2 :=
  fun _ _ hc h => libraryResolveLoads_WF hl hc h

end TvmLean

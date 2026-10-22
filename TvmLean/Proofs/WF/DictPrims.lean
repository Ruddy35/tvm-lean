import TvmLean.Proofs.WF.JoinPoints

/-!
# Dictionary primitives build and return well-formed cells and slices

The dictionary instructions (`TvmLean/Semantics/Exec/Dict/`) read and rebuild dictionaries with the
functions of `TvmLean/Model/Cell/Primitives.lean` and the private prefix-dictionary helpers of
`Exec/Dict/Ext.lean`. Given a well-formed dictionary (its root and every node below it, loaded by a
resolver that keeps cells well-formed, `ResolverWF`), this module shows that what they return is
well-formed:

* getters: the value found is a well-formed slice of a node (`dictMinMaxWithCells_WF`,
  `dictNearestWithCells_WF`, `pfxLookupPrefixWithCells_WF`; the plain lookup is
  `dictLookupWithCells_WF` of `Cells.lean`), and the key the minimum, maximum or nearest key
  lookups return is at most as long as the keys (`n`, or the hint), so that the cell `DICTGETMIN`
  and `DICTGETNEXT` make of it holds at most 1023 bits;
* setters (`dictSetGenAuxWithCells_spec`, `dictLookupSetGenAuxWithCells_spec`, the prefix
  dictionary's `pfxSetGenAuxWithCells_spec`, the subdictionary `dictExtractPrefixGo_spec`): every
  node built is finalized from a builder the model fills with `builderStoreBitsChecked`,
  `builderStoreRefChecked`, `builderAppendCellChecked` and the value's `storeVal` (`StoreValWF`),
  which raise cell_ov as C++ `CellBuilder` does, so it holds at most 1023 bits and 4 references;
* deleters (`dictDeleteAuxWithLoads_spec`, `pfxLookupDeleteWithCells_spec`): a fork that keeps both
  children is rebuilt with `Cell.mkOrdinary` and no check, its label written anew
  (`dictLabelEncode`, C++ `append_dict_label`) with its two references (and the constructor bit `1`
  in a prefix dictionary). It fits because the label written is the shortest encoding of the label
  read (`dictLabelEncode_size_le`, `dictLabelEncode_replicate_size_le`), so no longer than the bits
  it was read from in the old node (`parseDictLabel_len_enc`; `DictLabel.OK` collects what a label
  read from a well-formed node gives), and a fork has two references.

Each recursive function is proved by strong induction on its measure, `mvcgen` in `Except` with the
induction hypothesis as the specification of the recursive call, and `grind` on what is left.
`withLoads_triple` and `underCell_triple` lift a specification over the cells an error carries;
`Except.wp_of_triple` applies the specification of `storeVal`, a local function `mvcgen` does not
match. `private_eq% M f` is the unfolding equation of the private definition `f` of `M`, also of
a recursive one (`unfold_private` would unfold its fixpoint).
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

open Lean Elab Term Meta in
/-- `private_eq% M f`: the unfolding equation of the private definition `f` of the module `M`, also
of a recursive one (whose body `unfold_private` cannot show: it would unfold its fixpoint). -/
elab "private_eq% " m:ident n:ident : term => do
  let full := Name.mkNum (`_private ++ m.getId) 0 ++ n.getId
  unless (← getEnv).contains full do
    throwError "private_eq%: no private definition {n.getId} in {m.getId}"
  let some eqn ← getUnfoldEqnFor? full (nonRec := true)
    | throwError "private_eq%: no unfolding equation for {n.getId}"
  let ci ← getConstInfo eqn
  return mkConst eqn (ci.levelParams.map fun _ => levelZero)

attribute [local irreducible] natToBits Cell.mkOrdinary

/-! ## Specifications in `Except` -/

/-- A triple of `Except` with a pure precondition, read as a statement about its value. -/
theorem Except.of_triple' {ε α : Type} {x : Except ε α} {P : Prop} {Q : α → Prop}
    (h : ⦃⌜P⌝⦄ x ⦃post⟨fun a => ⌜Q a⌝, fun _ => ⌜True⌝⟩⦄) (hp : P) {a : α} (hx : x = .ok a) : Q a :=
  Except.of_triple (fun _ => h hp) hx

/-- The rule of consequence for a step of `Except` whose program `mvcgen` cannot match with its
specification (an application of a local function, `storeVal b`). -/
theorem Except.wp_of_triple {ε α : Type} {x : Except ε α} {P : Prop} {R : α → Prop}
    (h : ⦃⌜P⌝⦄ x ⦃post⟨fun a => ⌜R a⌝, fun _ => ⌜True⌝⟩⦄) (hp : P)
    {Q : PostCond α (.except ε .pure)} (hq : ∀ a, R a → (Q.1 a).down) (he : ∀ e, (Q.2.1 e).down) :
    (wp⟦x⟧ Q).down := by
  cases hx : x with
  | error e => simpa [wp] using he e
  | ok a => simpa [wp] using hq a (Except.of_triple' h hp hx)

/-- `withLoads` (the cells loaded before an error) changes only the error. -/
theorem withLoads_triple {α : Type} {P : Prop} {Q : α → Prop} (l : Array Cell) {x : Except Excno α}
    (h : ⦃⌜P⌝⦄ x ⦃post⟨fun a => ⌜Q a⌝, fun _ => ⌜True⌝⟩⦄) :
    ⦃⌜P⌝⦄ withLoads l x ⦃post⟨fun a => ⌜Q a⌝, fun _ => ⌜True⌝⟩⦄ := by
  intro hp
  refine Except.triple_of (fun a ha => ?_) trivial
  cases hx : x with
  | error e => simp [withLoads, hx, Except.mapError] at ha
  | ok b =>
    simp only [withLoads, hx, Except.mapError, Except.ok.injEq] at ha
    exact ha ▸ Except.of_triple' h hp hx

/-- `underCell` (the cell loaded above an error) changes only the error. -/
theorem underCell_triple {α : Type} {P : Prop} {Q : α → Prop} (c : Cell)
    {x : Except (Excno × Array Cell) α} (h : ⦃⌜P⌝⦄ x ⦃post⟨fun a => ⌜Q a⌝, fun _ => ⌜True⌝⟩⦄) :
    ⦃⌜P⌝⦄ underCell c x ⦃post⟨fun a => ⌜Q a⌝, fun _ => ⌜True⌝⟩⦄ := by
  intro hp
  refine Except.triple_of (fun a ha => ?_) trivial
  cases hx : x with
  | error e => simp [underCell, hx, Except.mapError] at ha
  | ok b =>
    simp only [underCell, hx, Except.mapError, Except.ok.injEq] at ha
    exact ha ▸ Except.of_triple' h hp hx

/-! ## Labels -/

theorem dictLabelBits_size_le (lbl : DictLabel) : (dictLabelBits lbl).size ≤ lbl.len := by
  unfold dictLabelBits
  split
  · simp
  · simp [Slice.readBits]; omega

theorem dictLabelEncodeSame_size_le (same : Bool) (len maxLen : Nat) :
    (dictLabelEncodeSame same len maxLen).size ≤ 2 * len + 2 ∧
    (dictLabelEncodeSame same len maxLen).size ≤ 2 + natLenBits maxLen + len ∧
    (0 < len → (dictLabelEncodeSame same len maxLen).size ≤ 3 + natLenBits maxLen) := by
  unfold dictLabelEncodeSame
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Array.size_append, natToBits_size]
    omega
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_lt] at h
    split
    · simp only [Array.size_append, natToBits_size, Array.size_replicate]
      omega
    · simp only [Array.size_append, Array.size_replicate, List.size_toArray, List.length_cons,
        List.length_nil]
      omega

theorem bitsAllSame?_replicate {len : Nat} (h : 0 < len) (b : Bool) :
    bitsAllSame? (Array.replicate len b) = some b := by
  unfold bitsAllSame?
  simp only [Array.size_replicate, h, ↓reduceIte, Id.run]
  have h0 : (Array.replicate len b)[0]! = b := by
    simp [h]
  rw [h0, Std.Range.forIn_eq_forIn_range']
  simp
  have key : ∀ l : List Nat, (∀ i ∈ l, i < len) →
      forIn (m := Id) l true (fun i r => if (Array.replicate len b)[i]! = b then
        pure (ForInStep.yield r) else pure (ForInStep.yield false)) = pure true := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.forIn_cons]
      have ha : (Array.replicate len b)[a]! = b := by simp [hl a (by simp)]
      simp only [ha, ↓reduceIte]
      exact ih (fun i hi => hl i (by simp [hi]))
  rw [key _ (fun i hi => by simp at hi; omega)]
  rfl

/-- The label `dictLabelEncode` writes (C++ `append_dict_label`) is the shortest of the encodings
`hml_short` (`2n+2` bits), `hml_long` (`2+k+n` bits, `k` the length of `maxLen`) and, for a label of
equal bits, `hml_same` (`3+k` bits). -/
theorem dictLabelEncode_size_le (bits : BitString) (len maxLen : Nat) :
    (dictLabelEncode bits len maxLen).size ≤ 2 * len + 2 ∧
    (dictLabelEncode bits len maxLen).size ≤ 2 + natLenBits maxLen + len := by
  unfold dictLabelEncode
  split
  · simp; omega
  · split
    · have := dictLabelEncodeSame_size_le ‹_› len maxLen
      omega
    · dsimp only
      split
      · simp only [Array.size_append, natToBits_size, Array.take_eq_extract, Array.size_extract]
        omega
      · simp only [Array.size_append, Array.size_replicate, List.size_toArray, List.length_cons,
          List.length_nil, Array.take_eq_extract, Array.size_extract]
        omega

theorem dictLabelEncode_replicate_size_le (b : Bool) (len maxLen : Nat) :
    (dictLabelEncode (Array.replicate len b) len maxLen).size ≤ 3 + natLenBits maxLen := by
  unfold dictLabelEncode
  split
  · simp; omega
  · rename_i h
    have h' : 0 < len := by omega
    have ht : (Array.replicate len b).take len = Array.replicate len b := by simp
    rw [ht, bitsAllSame?_replicate h' b]
    exact (dictLabelEncodeSame_size_le b len maxLen).2.2 h'

/-- A label read from a node is at most `maxLen` long, and the label `dictLabelEncode` writes for
it is no longer than the bits it was read from (the node's label and stored label bits). -/
theorem parseDictLabel_len_enc {resolve : Cell → Except Excno Cell} {cell : Cell} {maxLen : Nat}
    {lbl : DictLabel} (h : parseDictLabel cell maxLen resolve = .ok lbl) :
    lbl.len ≤ maxLen ∧
      (dictLabelEncode (dictLabelBits lbl) lbl.len maxLen).size ≤
        lbl.remainder.bitPos + lbl.storedBits := by
  unfold parseDictLabel at h
  cases hres : resolve cell with
  | error e => simp [hres, bind, Except.bind] at h
  | ok c' =>
    simp only [hres, bind, Except.bind] at h
    refine Except.of_triple (P := fun lbl : DictLabel => lbl.len ≤ maxLen ∧
      (dictLabelEncode (dictLabelBits lbl) lbl.len maxLen).size ≤
        lbl.remainder.bitPos + lbl.storedBits) ?_ h
    clear h
    mvcgen
    all_goals simp only [dictLabelBits]
    · -- `00`: the empty label
      simp [dictLabelEncode, Slice.advanceBits, Slice.ofCell]
    · -- `hml_short`
      rename_i hl _ _ _ _ _
      refine ⟨by omega, ?_⟩
      have := (dictLabelEncode_size_le (((Slice.ofCell c').advanceBits 1).advanceBits
        (((Slice.ofCell c').advanceBits 1).countLeading true + 1) |>.readBits
          (((Slice.ofCell c').advanceBits 1).countLeading true))
        (((Slice.ofCell c').advanceBits 1).countLeading true) maxLen).1
      simp only [Slice.advanceBits, Slice.ofCell] at this ⊢
      omega
    · -- `hml_long`
      rename_i r ht hl _ _ _ _ _
      obtain ⟨_, h2, _, _⟩ := Slice.takeBitsAsNatCellUnd_ok ht
      refine ⟨by omega, ?_⟩
      have := (dictLabelEncode_size_le (r.2.readBits r.1) r.1 maxLen).2
      simp only [Slice.advanceBits, Slice.ofCell] at h2
      omega
    · -- `hml_same`
      rename_i r3 ht3 r ht hl _ _
      obtain ⟨_, h2, _, _⟩ := Slice.takeBitsAsNatCellUnd_ok ht
      obtain ⟨_, h2', _, _⟩ := Slice.takeBitsAsNatCellUnd_ok ht3
      refine ⟨by omega, ?_⟩
      have := dictLabelEncode_replicate_size_le (decide (r3.1 &&& 1 = 1)) r.1 maxLen
      simp only [Slice.ofCell] at h2'
      omega

/-- What a label read from a node of a well-formed dictionary gives: the rest of the node is a
well-formed slice holding the stored label bits, the label is at most `maxLen` long, and the label
`dictLabelEncode` writes for it is no longer than the bits it was read from. -/
def DictLabel.OK (lbl : DictLabel) (maxLen : Nat) : Prop :=
  lbl.remainder.WF ∧ lbl.remainder.bitPos + lbl.storedBits ≤ lbl.remainder.cell.bits.size ∧
    lbl.len ≤ maxLen ∧
    (dictLabelEncode (dictLabelBits lbl) lbl.len maxLen).size ≤
      lbl.remainder.bitPos + lbl.storedBits

theorem parseDictLabel_spec (resolve : Cell → Except Excno Cell) (cell : Cell) (maxLen : Nat) :
    ⦃⌜ResolverWF resolve ∧ cell.WF⌝⦄ parseDictLabel cell maxLen resolve
      ⦃post⟨fun lbl => ⌜lbl.OK maxLen⌝, fun _ => ⌜True⌝⟩⦄ := by
  intro ⟨hr, hc⟩
  refine Except.triple_of (P := fun lbl : DictLabel => lbl.OK maxLen) (fun lbl h => ?_) trivial
  obtain ⟨h1, h2⟩ := parseDictLabel_WF hr hc h
  obtain ⟨h3, h4⟩ := parseDictLabel_len_enc h
  exact ⟨h1, h2, h3, h4⟩

theorem dictValidateNodeExtLe_spec (lbl : DictLabel) (remaining : Nat) :
    ⦃⌜True⌝⦄ dictValidateNodeExtLe lbl remaining
      ⦃post⟨fun r => ⌜r.val = remaining - lbl.len⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [dictValidateNodeExtLe]

theorem dictValidateNodeExt_spec (lbl : DictLabel) (remaining : Nat) :
    ⦃⌜True⌝⦄ dictValidateNodeExt lbl remaining
      ⦃post⟨fun r => ⌜r = remaining - lbl.len⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [dictValidateNodeExt]

/-! ## Getters -/

/-- The minimum or maximum of a well-formed dictionary with `n`-bit keys: a well-formed slice, and
a key of at most `n` bits. -/
theorem dictMinMaxAuxWithCells_spec {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    (n : Nat) (cell : Cell) (pos : Nat) (firstBit restBit : Bool) :
    ⦃⌜cell.WF⌝⦄ dictMinMaxAuxWithCells cell n pos firstBit restBit resolve
      ⦃post⟨fun r => ⌜r.1.WF ∧ r.2.1.size ≤ n⌝, fun _ => ⌜True⌝⟩⦄ := by
  induction n using Nat.strongRecOn generalizing cell pos with
  | _ n ih =>
  intro hc
  rw [dictMinMaxAuxWithCells]
  have ih' : ∀ m cell pos, ⦃⌜m < n ∧ cell.WF⌝⦄ dictMinMaxAuxWithCells cell m pos firstBit restBit
      resolve ⦃post⟨fun r => ⌜r.1.WF ∧ r.2.1.size ≤ m⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun m cell pos ⟨hm, hc⟩ => ih m hm cell pos hc
  mvcgen [ih', parseDictLabel_spec, dictValidateNodeExtLe_spec]
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals grind [Slice.advanceBits_WF, Slice.WF.ref!, dictLabelBits_size_le]

theorem dictMinMaxWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {n : Nat} {fetchMax invertFirst : Bool}
    {r : Option (Slice × BitString) × Array Cell}
    (h : dictMinMaxWithCells root n fetchMax invertFirst resolve = .ok r) :
    ∀ v k, r.1 = some (v, k) → v.WF ∧ k.size ≤ n := by
  refine Except.of_triple (P := fun r : Option (Slice × BitString) × Array Cell =>
    ∀ v k, r.1 = some (v, k) → v.WF ∧ k.size ≤ n) ?_ h
  clear h
  unfold dictMinMaxWithCells
  have hmm := dictMinMaxAuxWithCells_spec hr
  split
  · mvcgen; simp
  · mvcgen [hmm]
    · exact hroot _ rfl
    · grind

/-- The nearest key of a well-formed dictionary with keys of the size of the hint: a well-formed
slice, and a key no longer than the hint. -/
theorem dictNearestAuxWithCells_spec {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    (n : Nat) (cell : Cell) (hint : BitString) (pos : Nat) (allowEq firstBit restBit : Bool) :
    ⦃⌜cell.WF⌝⦄ dictNearestAuxWithCells cell hint n pos allowEq firstBit restBit resolve
      ⦃post⟨fun r => ⌜∀ v k, r.1 = some (v, k) → v.WF ∧ k.size ≤ n⌝, fun _ => ⌜True⌝⟩⦄ := by
  induction n using Nat.strongRecOn generalizing cell hint pos with
  | _ n ih =>
  intro hc
  rw [dictNearestAuxWithCells]
  have ih' : ∀ m cell hint pos, ⦃⌜m < n ∧ cell.WF⌝⦄
      dictNearestAuxWithCells cell hint m pos allowEq firstBit restBit resolve
      ⦃post⟨fun r => ⌜∀ v k, r.1 = some (v, k) → v.WF ∧ k.size ≤ m⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun m cell hint pos ⟨hm, hc⟩ => ih m hm cell hint pos hc
  have hmm := dictMinMaxAuxWithCells_spec hr
  mvcgen [ih', parseDictLabel_spec, dictValidateNodeExtLe_spec, hmm]
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals grind [Slice.advanceBits_WF, Slice.WF.ref!, dictLabelBits_size_le]

theorem dictNearestWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {hint : BitString}
    {fetchNext allowEq invertFirst : Bool} {r : Option (Slice × BitString) × Array Cell}
    (h : dictNearestWithCells root hint fetchNext allowEq invertFirst resolve = .ok r) :
    ∀ v k, r.1 = some (v, k) → v.WF ∧ k.size ≤ hint.size := by
  unfold dictNearestWithCells at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  · exact Except.of_triple (fun _ => dictNearestAuxWithCells_spec hr _ _ _ _ _ _ _ (hroot _ rfl)) h

/-! ## Builders -/

theorem builderStoreBitsChecked_spec (b : Builder) (bs : BitString) :
    ⦃⌜b.WF⌝⦄ builderStoreBitsChecked b bs ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [builderStoreBitsChecked]
  rename_i hb hc
  exact Builder.storeBits_WF b bs hc hb

theorem builderStoreRefChecked_spec (b : Builder) (c : Cell) :
    ⦃⌜b.WF ∧ c.WF⌝⦄ builderStoreRefChecked b c ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [builderStoreRefChecked]
  rename_i hb hc
  exact Builder.pushRef_WF b c hc.1 hc.2 hb

theorem builderAppendCellChecked_spec (b : Builder) (c : Cell) :
    ⦃⌜b.WF ∧ c.WF⌝⦄ builderAppendCellChecked b c ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [builderAppendCellChecked]
  rename_i hb hc
  exact Builder.appendCell_WF hc.1 hc.2 hb

theorem builderAppendBuilderChecked_spec (b v : Builder) :
    ⦃⌜b.WF ∧ v.WF⌝⦄ builderAppendBuilderChecked b v ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  mvcgen [builderAppendBuilderChecked]
  rename_i hb hc
  exact Builder.append_WF hc.1 hc.2 hb

/-- A function storing the value of a dictionary entry into a builder keeps builders
well-formed. -/
def StoreValWF (storeVal : Builder → Except Excno Builder) : Prop :=
  ∀ b, ⦃⌜b.WF⌝⦄ storeVal b ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄

/-! ## Setters -/

/-- C++ `dict_set`: the new root of a well-formed dictionary is well-formed: every node it builds
is finalized from a builder the checks of `builderStoreBitsChecked`, `builderStoreRefChecked` and
`storeVal` keep within a cell. -/
theorem dictSetGenAuxWithCells_spec {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {storeVal : Builder → Except Excno Builder} (hsv : StoreValWF storeVal) (mode : DictSetMode)
    (root : Option Cell) (key : BitString) :
    ⦃⌜∀ c, root = some c → c.WF⌝⦄ dictSetGenAuxWithCells root key storeVal mode resolve
      ⦃post⟨fun r => ⌜∀ c, r.1 = some c → c.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  suffices h : ∀ n (root : Option Cell) (key : BitString), key.size = n →
      ⦃⌜∀ c, root = some c → c.WF⌝⦄ dictSetGenAuxWithCells root key storeVal mode resolve
        ⦃post⟨fun r => ⌜∀ c, r.1 = some c → c.WF⌝, fun _ => ⌜True⌝⟩⦄ from h _ root key rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro root key hk
  have ih' : ∀ (root : Option Cell) (key : BitString),
      ⦃⌜key.size < n ∧ ∀ c, root = some c → c.WF⌝⦄ dictSetGenAuxWithCells root key storeVal mode
        resolve ⦃post⟨fun r => ⌜∀ c, r.1 = some c → c.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun root key ⟨hlt, hroot⟩ => ih _ (hk ▸ hlt) root key rfl hroot
  have hsv' : ∀ b, ⦃⌜b.WF⌝⦄ storeVal b ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ := hsv
  rw [dictSetGenAuxWithCells.eq_def]
  mvcgen [ih', parseDictLabel_spec, dictValidateNodeExtLe_spec, builderStoreBitsChecked_spec,
    builderStoreRefChecked_spec, builderAppendCellChecked_spec]
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals first
    | (refine Except.wp_of_triple (hsv _) (by assumption) ?_ (fun _ => trivial)
       intro b hb
       mvcgen [builderStoreBitsChecked_spec, builderAppendCellChecked_spec, builderStoreRefChecked_spec])
    | skip
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals grind [Builder.empty_WF, Builder.finalize_WF, Slice.toCellRemaining_WF,
    Slice.advanceBits_WF, Slice.WF.ref!]

theorem StoreValWF.storeRef {c : Cell} (hc : c.WF) :
    StoreValWF fun b => builderStoreRefChecked b c :=
  fun b hb => builderStoreRefChecked_spec b c ⟨hb, hc⟩

theorem StoreValWF.appendCell {c : Cell} (hc : c.WF) :
    StoreValWF fun b => builderAppendCellChecked b c :=
  fun b hb => builderAppendCellChecked_spec b c ⟨hb, hc⟩

theorem StoreValWF.appendBuilder {v : Builder} (hv : v.WF) :
    StoreValWF fun b => builderAppendBuilderChecked b v :=
  fun b hb => builderAppendBuilderChecked_spec b v ⟨hb, hv⟩

theorem dictSetRefWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {key : BitString} {valRef : Cell}
    (hv : valRef.WF) {mode : DictSetMode} {r : Option Cell × Bool × Nat × Array Cell}
    (h : dictSetRefWithCells root key valRef mode resolve = .ok r) : ∀ c, r.1 = some c → c.WF :=
  Except.of_triple' (dictSetGenAuxWithCells_spec hr (StoreValWF.storeRef hv) mode root key) hroot h

theorem dictSetSliceWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {key : BitString} {val : Slice}
    (hv : val.WF) {mode : DictSetMode} {r : Option Cell × Bool × Nat × Array Cell}
    (h : dictSetSliceWithCells root key val mode resolve = .ok r) : ∀ c, r.1 = some c → c.WF :=
  Except.of_triple' (dictSetGenAuxWithCells_spec hr
    (StoreValWF.appendCell (Slice.toCellRemaining_WF hv)) mode root key) hroot h

theorem dictSetBuilderWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {key : BitString} {val : Builder}
    (hv : val.WF) {mode : DictSetMode} {r : Option Cell × Bool × Nat × Array Cell}
    (h : dictSetBuilderWithCells root key val mode resolve = .ok r) : ∀ c, r.1 = some c → c.WF :=
  Except.of_triple' (dictSetGenAuxWithCells_spec hr (StoreValWF.appendBuilder hv) mode root key)
    hroot h

/-- C++ `dict_lookup_set`: the old value is a well-formed slice of the dictionary, and the new root
is well-formed, as for `dictSetGenAuxWithCells_spec`. -/
theorem dictLookupSetGenAuxWithCells_spec {resolve : Cell → Except Excno Cell}
    (hr : ResolverWF resolve) {storeVal : Builder → Except Excno Builder} (hsv : StoreValWF storeVal)
    (mode : DictSetMode) (root : Option Cell) (key : BitString) :
    ⦃⌜∀ c, root = some c → c.WF⌝⦄ dictLookupSetGenAuxWithCells root key storeVal mode resolve
      ⦃post⟨fun r => ⌜(∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF⌝,
        fun _ => ⌜True⌝⟩⦄ := by
  suffices h : ∀ n (root : Option Cell) (key : BitString), key.size = n →
      ⦃⌜∀ c, root = some c → c.WF⌝⦄ dictLookupSetGenAuxWithCells root key storeVal mode resolve
        ⦃post⟨fun r => ⌜(∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF⌝,
          fun _ => ⌜True⌝⟩⦄ from h _ root key rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro root key hk
  have ih' : ∀ (root : Option Cell) (key : BitString),
      ⦃⌜key.size < n ∧ ∀ c, root = some c → c.WF⌝⦄ dictLookupSetGenAuxWithCells root key storeVal
        mode resolve ⦃post⟨fun r => ⌜(∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF⌝,
          fun _ => ⌜True⌝⟩⦄ :=
    fun root key ⟨hlt, hroot⟩ => ih _ (hk ▸ hlt) root key rfl hroot
  rw [dictLookupSetGenAuxWithCells.eq_def]
  mvcgen [ih', parseDictLabel_spec, dictValidateNodeExtLe_spec, builderStoreBitsChecked_spec,
    builderStoreRefChecked_spec, builderAppendCellChecked_spec]
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals first
    | (refine Except.wp_of_triple (hsv _) (by assumption) ?_ (fun _ => trivial)
       intro b hb
       mvcgen [builderStoreBitsChecked_spec, builderAppendCellChecked_spec, builderStoreRefChecked_spec])
    | skip
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals grind [Builder.empty_WF, Builder.finalize_WF, Slice.toCellRemaining_WF,
    Slice.advanceBits_WF, Slice.WF.ref!]

theorem dictLookupSetRefWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {key : BitString} {valRef : Cell}
    (hv : valRef.WF) {mode : DictSetMode} {r : Option Slice × Option Cell × Bool × Nat × Array Cell}
    (h : dictLookupSetRefWithCells root key valRef mode resolve = .ok r) :
    (∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF :=
  Except.of_triple' (dictLookupSetGenAuxWithCells_spec hr (StoreValWF.storeRef hv) mode root key)
    hroot h

theorem dictLookupSetSliceWithCells_WF {resolve : Cell → Except Excno Cell}
    (hr : ResolverWF resolve) {root : Option Cell} (hroot : ∀ c, root = some c → c.WF)
    {key : BitString} {val : Slice} (hv : val.WF) {mode : DictSetMode}
    {r : Option Slice × Option Cell × Bool × Nat × Array Cell}
    (h : dictLookupSetSliceWithCells root key val mode resolve = .ok r) :
    (∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF :=
  Except.of_triple' (dictLookupSetGenAuxWithCells_spec hr
    (StoreValWF.appendCell (Slice.toCellRemaining_WF hv)) mode root key) hroot h

theorem dictLookupSetBuilderWithCells_WF {resolve : Cell → Except Excno Cell}
    (hr : ResolverWF resolve) {root : Option Cell} (hroot : ∀ c, root = some c → c.WF)
    {key : BitString} {val : Builder} (hv : val.WF) {mode : DictSetMode}
    {r : Option Slice × Option Cell × Bool × Nat × Array Cell}
    (h : dictLookupSetBuilderWithCells root key val mode resolve = .ok r) :
    (∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF :=
  Except.of_triple' (dictLookupSetGenAuxWithCells_spec hr (StoreValWF.appendBuilder hv) mode root
    key) hroot h

/-! ## Deletion -/

theorem Slice.WF.bits_le {s : Slice} (h : s.WF) : s.cell.bits.size ≤ 1023 := h.1.bits_le

/-- C++ `dict_lookup_delete`: the old value is a well-formed slice of the dictionary, and the new
root is well-formed. A fork keeping both children gets its label written anew
(`append_dict_label`), an encoding no longer than the one read (`parseDictLabel_len_enc`), so the
fork fits in a cell; a merged edge is built with the checks of the builders. -/
theorem dictDeleteAuxWithLoads_spec {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    (key : BitString) (remaining : Nat) (cell : Cell) (pos : Nat) :
    ⦃⌜cell.WF⌝⦄ dictDeleteAuxWithLoads cell key pos remaining resolve
      ⦃post⟨fun r => ⌜(∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF⌝,
        fun _ => ⌜True⌝⟩⦄ := by
  induction remaining using Nat.strongRecOn generalizing cell pos with
  | _ remaining ih =>
  intro hc
  have ih' : ∀ (m : Nat) (c cell : Cell) (pos : Nat), ⦃⌜m < remaining ∧ cell.WF⌝⦄
      underCell c (dictDeleteAuxWithLoads cell key pos m resolve)
      ⦃post⟨fun r => ⌜(∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF⌝,
        fun _ => ⌜True⌝⟩⦄ :=
    fun m c cell pos ⟨hm, hc⟩ => underCell_triple c (ih m hm cell pos) hc
  have hpl : ∀ l cell maxLen, ⦃⌜ResolverWF resolve ∧ cell.WF⌝⦄
      withLoads l (parseDictLabel cell maxLen resolve)
      ⦃post⟨fun lbl => ⌜lbl.OK maxLen⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l cell maxLen => withLoads_triple l (parseDictLabel_spec resolve cell maxLen)
  have hvl : ∀ l lbl remaining, ⦃⌜True⌝⦄ withLoads l (dictValidateNodeExtLe lbl remaining)
      ⦃post⟨fun r => ⌜r.val = remaining - lbl.len⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l lbl remaining => withLoads_triple l (dictValidateNodeExtLe_spec lbl remaining)
  have hv : ∀ l lbl remaining, ⦃⌜True⌝⦄ withLoads l (dictValidateNodeExt lbl remaining)
      ⦃post⟨fun r => ⌜r = remaining - lbl.len⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l lbl remaining => withLoads_triple l (dictValidateNodeExt_spec lbl remaining)
  have hsb : ∀ l b bs, ⦃⌜b.WF⌝⦄ withLoads l (builderStoreBitsChecked b bs)
      ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l b bs => withLoads_triple l (builderStoreBitsChecked_spec b bs)
  have hac : ∀ l b c, ⦃⌜b.WF ∧ c.WF⌝⦄ withLoads l (builderAppendCellChecked b c)
      ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l b c => withLoads_triple l (builderAppendCellChecked_spec b c)
  rw [dictDeleteAuxWithLoads]
  mvcgen [ih', hpl, hvl, hv, hsb, hac]
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals grind [Builder.empty_WF, Builder.finalize_WF, Slice.toCellRemaining_WF,
    Slice.advanceBits_WF, Slice.WF.ref!, Cell.mkOrdinary_WF, Slice.WF.bits_le]

theorem dictDeleteWithLoads_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {key : BitString}
    {r : Option Slice × Option Cell × Nat × Array Cell}
    (h : dictDeleteWithLoads root key resolve = .ok r) :
    (∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF := by
  unfold dictDeleteWithLoads at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  · exact Except.of_triple' (dictDeleteAuxWithLoads_spec hr key _ _ _) (hroot _ rfl) h

/-! ## Subdictionaries -/

/-- C++ `cut_prefix_subdict`: the root of the subdictionary is the root of the dictionary or a node
built with the checks of the builders. -/
theorem dictExtractPrefixGo_spec {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    (keyBits : Nat) (pfx : BitString) (prefixLen : Nat) (removePrefix : Bool) (rootCell : Cell)
    (cell : Cell) (m : Nat) (loaded : Array Cell) :
    ⦃⌜rootCell.WF ∧ cell.WF⌝⦄
      dictExtractPrefixGo keyBits pfx prefixLen removePrefix rootCell cell m loaded resolve
      ⦃post⟨fun r => ⌜∀ c, r.1 = some c → c.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  suffices h : ∀ k (cell : Cell) (m : Nat) (loaded : Array Cell), prefixLen - m = k →
      ⦃⌜rootCell.WF ∧ cell.WF⌝⦄
        dictExtractPrefixGo keyBits pfx prefixLen removePrefix rootCell cell m loaded resolve
        ⦃post⟨fun r => ⌜∀ c, r.1 = some c → c.WF⌝, fun _ => ⌜True⌝⟩⦄ from h _ cell m loaded rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro cell m loaded hk
  have ih' : ∀ (cell : Cell) (m : Nat) (loaded : Array Cell),
      ⦃⌜prefixLen - m < k ∧ rootCell.WF ∧ cell.WF⌝⦄
        dictExtractPrefixGo keyBits pfx prefixLen removePrefix rootCell cell m loaded resolve
        ⦃post⟨fun r => ⌜∀ c, r.1 = some c → c.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun cell m loaded ⟨hlt, h1, h2⟩ => ih _ hlt cell m loaded rfl ⟨h1, h2⟩
  rw [dictExtractPrefixGo]
  mvcgen [ih', parseDictLabel_spec, dictValidateNodeExt_spec, builderStoreBitsChecked_spec,
    builderAppendCellChecked_spec]
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals grind [Builder.empty_WF, Builder.finalize_WF, Slice.toCellRemaining_WF,
    Slice.advanceBits_WF, Slice.WF.ref!]

theorem dictExtractPrefixSubdictWithCells_WF {resolve : Cell → Except Excno Cell}
    (hr : ResolverWF resolve) {root : Option Cell} (hroot : ∀ c, root = some c → c.WF)
    {keyBits : Nat} {pfx : BitString} {prefixLen : Nat} {removePrefix : Bool}
    {r : Option Cell × Bool × Nat × Array Cell}
    (h : dictExtractPrefixSubdictWithCells root keyBits pfx prefixLen removePrefix resolve = .ok r) :
    ∀ c, r.1 = some c → c.WF := by
  refine Except.of_triple (P := fun r : Option Cell × Bool × Nat × Array Cell =>
    ∀ c, r.1 = some c → c.WF) ?_ h
  clear h
  unfold dictExtractPrefixSubdictWithCells
  have hgo := dictExtractPrefixGo_spec hr keyBits pfx prefixLen removePrefix
  mvcgen [hgo]
  all_goals grind

/-! ## Prefix dictionaries (`PFXDICT*`) -/

theorem WF.size_take {α : Type} (a : Array α) (n : Nat) : (a.take n).size = min n a.size := by
  simp [Array.take_eq_extract]

/-- The bits of a fork of a prefix dictionary rewritten with its label anew: the label, no longer
than the one read, and the constructor bit `1`, which the old node had after its label. -/
theorem pfxFork_bits_le {lbl : DictLabel} {n : Nat} (hw : lbl.remainder.WF)
    (he : (dictLabelEncode (dictLabelBits lbl) lbl.len n).size ≤
      lbl.remainder.bitPos + lbl.storedBits)
    (hb : (lbl.remainder.advanceBits lbl.storedBits).haveBits 1 = true) :
    (dictLabelEncode (dictLabelBits lbl) lbl.len n ++ #[true]).size ≤ 1023 := by
  have := hw.bits_le
  rw [Slice.haveBits_iff] at hb
  simp only [Slice.advanceBits] at hb
  simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
  omega

theorem parseDictLabel_OK {resolve : Cell → Except Excno Cell} {cell : Cell} {maxLen : Nat}
    {lbl : DictLabel} (h : parseDictLabel cell maxLen resolve = .ok lbl) (hr : ResolverWF resolve)
    (hc : cell.WF) : lbl.OK maxLen :=
  Except.of_triple' (parseDictLabel_spec resolve cell maxLen) ⟨hr, hc⟩ h

/-- C++ `PrefixDictionary::lookup_prefix`: the value found is a well-formed slice. -/
theorem pfxLookupPrefixGo_spec {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    (keyBits : BitString) (keyLen : Nat) (cell : Cell) (nRem m pos : Nat) (loaded : Array Cell) :
    ⦃⌜cell.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixGo) keyBits keyLen
        cell nRem m pos loaded resolve
      ⦃post⟨fun r => ⌜∀ s, r.1 = some s → s.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  induction m using Nat.strongRecOn generalizing cell nRem pos loaded with
  | _ m ih =>
  intro hc
  have ih' : ∀ (m' : Nat) (cell : Cell) (nRem pos : Nat) (loaded : Array Cell), ⦃⌜m' < m ∧ cell.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixGo) keyBits keyLen
        cell nRem m' pos loaded resolve
      ⦃post⟨fun r => ⌜∀ s, r.1 = some s → s.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun m' cell nRem pos loaded ⟨hlt, hc⟩ => ih m' hlt cell nRem pos loaded hc
  rw [private_eq% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixGo]
  mvcgen [ih']
  all_goals (try clear_local_functions)
  all_goals grind [→ parseDictLabel_OK, DictLabel.OK, Slice.advanceBits_WF, Slice.WF.ref!,
    Slice.addBitPos_WF]

theorem pfxLookupPrefixWithCells_spec {resolve : Cell → Except Excno Cell}
    (hr : ResolverWF resolve) (root : Option Cell) (keyBits : BitString) (keyLen n : Nat) :
    ⦃⌜∀ c, root = some c → c.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells) root
        keyBits keyLen n resolve
      ⦃post⟨fun r => ⌜∀ s, r.1 = some s → s.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells
  have hgo := pfxLookupPrefixGo_spec hr
  mvcgen [hgo]
  all_goals grind

set_option maxHeartbeats 4000000 in
/-- `PFXDICTSET`: the new root of a well-formed prefix dictionary is well-formed (every node it
builds is finalized from checked builders, the value stored by `storeVal`). -/
theorem pfxSetGenAuxWithCells_spec {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {storeVal : Builder → Except Excno Builder} (hsv : StoreValWF storeVal) (mode : DictSetMode)
    (root : Option Cell) (key : BitString) (n : Nat) :
    ⦃⌜∀ c, root = some c → c.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells) root key n
        storeVal mode resolve
      ⦃post⟨fun r => ⌜∀ c, r.1 = some c → c.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  suffices h : ∀ k (root : Option Cell) (key : BitString) (n : Nat), key.size = k →
      ⦃⌜∀ c, root = some c → c.WF⌝⦄
        (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells) root key n
          storeVal mode resolve
        ⦃post⟨fun r => ⌜∀ c, r.1 = some c → c.WF⌝, fun _ => ⌜True⌝⟩⦄ from h _ root key n rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro root key n hk
  have ih' : ∀ (c : Cell) (root : Option Cell) (key : BitString) (n : Nat),
      ⦃⌜key.size < k ∧ ∀ c, root = some c → c.WF⌝⦄
        underCell c ((private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells)
          root key n storeVal mode resolve)
        ⦃post⟨fun r => ⌜∀ c, r.1 = some c → c.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun c root key n ⟨hlt, hroot⟩ => underCell_triple c (ih _ hlt root key n rfl) hroot
  have hpl : ∀ l cell maxLen, ⦃⌜ResolverWF resolve ∧ cell.WF⌝⦄
      withLoads l (parseDictLabel cell maxLen resolve)
      ⦃post⟨fun lbl => ⌜lbl.OK maxLen⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l cell maxLen => withLoads_triple l (parseDictLabel_spec resolve cell maxLen)
  have hsb : ∀ l b bs, ⦃⌜b.WF⌝⦄ withLoads l (builderStoreBitsChecked b bs)
      ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l b bs => withLoads_triple l (builderStoreBitsChecked_spec b bs)
  have hsr : ∀ l b c, ⦃⌜b.WF ∧ c.WF⌝⦄ withLoads l (builderStoreRefChecked b c)
      ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l b c => withLoads_triple l (builderStoreRefChecked_spec b c)
  have hac : ∀ l b c, ⦃⌜b.WF ∧ c.WF⌝⦄ withLoads l (builderAppendCellChecked b c)
      ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l b c => withLoads_triple l (builderAppendCellChecked_spec b c)
  have hsv' : ∀ l b, ⦃⌜b.WF⌝⦄ withLoads l (storeVal b)
      ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l b => withLoads_triple l (hsv b)
  rw [private_eq% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells]
  mvcgen [ih', hpl, hsb, hsr, hac, hsv']
  all_goals (try clear_local_functions)
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals grind [Builder.empty_WF, Builder.finalize_WF, Slice.toCellRemaining_WF,
    Slice.advanceBits_WF, Slice.WF.ref!]

set_option maxHeartbeats 4000000 in
/-- C++ `pfx_dict_lookup_delete`: the value removed from a well-formed prefix dictionary and the
root left are well-formed. A fork keeping both children gets its label written anew, no longer
than the one read, before its constructor bit, so it fits where the old one did; a merged edge is
built with the checks of the builders. -/
theorem pfxLookupDeleteWithCells_spec {resolve : Cell → Except Excno Cell}
    (hr : ResolverWF resolve) (root : Option Cell) (key : BitString) (n : Nat) :
    ⦃⌜∀ c, root = some c → c.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupDeleteWithCells) root key
        n resolve
      ⦃post⟨fun r => ⌜(∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF⌝,
        fun _ => ⌜True⌝⟩⦄ := by
  suffices h : ∀ k (root : Option Cell) (key : BitString) (n : Nat), key.size = k →
      ⦃⌜∀ c, root = some c → c.WF⌝⦄
        (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupDeleteWithCells) root
          key n resolve
        ⦃post⟨fun r => ⌜(∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF⌝,
          fun _ => ⌜True⌝⟩⦄ from h _ root key n rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro root key n hk
  have ih' : ∀ (c : Cell) (root : Option Cell) (key : BitString) (n : Nat),
      ⦃⌜key.size < k ∧ ∀ c, root = some c → c.WF⌝⦄
        underCell c ((private% TvmLean.Semantics.Exec.Dict.Ext
          TvmLean.DictExt.pfxLookupDeleteWithCells) root key n resolve)
        ⦃post⟨fun r => ⌜(∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF⌝,
          fun _ => ⌜True⌝⟩⦄ :=
    fun c root key n ⟨hlt, hroot⟩ => underCell_triple c (ih _ hlt root key n rfl) hroot
  have hpl : ∀ l cell maxLen, ⦃⌜ResolverWF resolve ∧ cell.WF⌝⦄
      withLoads l (parseDictLabel cell maxLen resolve)
      ⦃post⟨fun lbl => ⌜lbl.OK maxLen⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l cell maxLen => withLoads_triple l (parseDictLabel_spec resolve cell maxLen)
  have hsb : ∀ l b bs, ⦃⌜b.WF⌝⦄ withLoads l (builderStoreBitsChecked b bs)
      ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l b bs => withLoads_triple l (builderStoreBitsChecked_spec b bs)
  have hac : ∀ l b c, ⦃⌜b.WF ∧ c.WF⌝⦄ withLoads l (builderAppendCellChecked b c)
      ⦃post⟨fun b' => ⌜b'.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
    fun l b c => withLoads_triple l (builderAppendCellChecked_spec b c)
  rw [private_eq% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupDeleteWithCells]
  mvcgen [ih', hpl, hsb, hac]
  all_goals (try clear_local_functions)
  all_goals (try simp only [DictLabel.OK] at *)
  all_goals (try split)
  all_goals grind [Builder.empty_WF, Builder.finalize_WF, Slice.toCellRemaining_WF,
    Slice.advanceBits_WF, Slice.WF.ref!, Cell.mkOrdinary_WF, Slice.WF.bits_le, Slice.haveBits_iff,
    Slice.addBitPos_WF, bitsCommonPrefixLen_le_right, WF.size_take, pfxFork_bits_le]

/-- The prefix `PFXDICTGET` cuts off a well-formed slice and the rest are well-formed slices. -/
theorem slicePrefix_spec (s : Slice) (bits refs : Nat) :
    ⦃⌜s.WF⌝⦄ (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix) s bits refs
      ⦃post⟨fun p => ⌜p.1.WF ∧ p.2.WF⌝, fun _ => ⌜True⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix
  mvcgen
  grind [Slice.prefixCell_WF, Slice.ofCell_WF_iff, Slice.addPos_WF]

/-! ## The results in the form the handlers use -/

theorem pfxLookupPrefixWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {keyBits : BitString} {keyLen n : Nat}
    {r : Option Slice × Nat × Array Cell}
    (h : (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells) root
      keyBits keyLen n resolve = .ok r) : ∀ s, r.1 = some s → s.WF :=
  Except.of_triple' (pfxLookupPrefixWithCells_spec hr root keyBits keyLen n) hroot h

theorem pfxSetGenAuxWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {key : BitString} {n : Nat}
    {v : Slice} (hv : v.WF) {mode : DictSetMode} {r : Option Cell × Bool × Nat × Array Cell}
    (h : (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells) root key
      n (fun b => builderAppendCellChecked b v.toCellRemaining) mode resolve = .ok r) :
    ∀ c, r.1 = some c → c.WF :=
  Except.of_triple' (pfxSetGenAuxWithCells_spec hr
    (StoreValWF.appendCell (Slice.toCellRemaining_WF hv)) mode root key n) hroot h

theorem pfxLookupDeleteWithCells_WF {resolve : Cell → Except Excno Cell} (hr : ResolverWF resolve)
    {root : Option Cell} (hroot : ∀ c, root = some c → c.WF) {key : BitString} {n : Nat}
    {r : Option Slice × Option Cell × Nat × Array Cell}
    (h : (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupDeleteWithCells) root
      key n resolve = .ok r) :
    (∀ s, r.1 = some s → s.WF) ∧ ∀ c, r.2.1 = some c → c.WF :=
  Except.of_triple' (pfxLookupDeleteWithCells_spec hr root key n) hroot h

theorem slicePrefix_WF {s : Slice} (hs : s.WF) {bits refs : Nat} {p : Slice × Slice}
    (h : (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix) s bits refs =
      .ok p) : p.1.WF ∧ p.2.WF :=
  Except.of_triple' (slicePrefix_spec s bits refs) hs h

end TvmLean

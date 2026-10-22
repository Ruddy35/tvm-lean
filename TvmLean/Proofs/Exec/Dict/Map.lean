import TvmLean.Proofs.Exec.Dict.Delete

/-!
# Dictionaries as maps: well-formed dictionaries, set and delete

A contract proof sees a dictionary through its map (`Dict.get`, `Proofs/Exec/Spec/Dict.lean`): the
value of each key, as the lookup of the model with the default resolver finds it. Here:

* `Dict.value root key`: the contents of that value (`Slice.toCellRemaining`: the bits and
  references after the label, what a set stores);
* `Dict.WF root n`: every lookup of an `n`-bit key succeeds (no ill-formed node, no exotic cell
  on any key's path). The instructions run the dictionary functions with the resolver of the VM
  (`VM.cellResolver`, a library cell loads as its library's root); on a well-formed dictionary it
  gives the same results as the default resolver (`set_resolve`, `delete_resolve`,
  `visited_resolve`, `lookup_resolve`);
* `Dict.value_set`, `Dict.value_delete`: the map after a set or a delete, from the map before
  (`val_set`, `val_deleteWithLoads`), and `Dict.WF.set`, `Dict.WF.delete`: the dictionary stays
  well-formed.
-/

namespace TvmLean

/-- The contents of the value of `key` in the dictionary `root`: the bits and references of the
value slice `Dict.get` finds (`none` if absent). -/
def Dict.value (root : Option Cell) (key : BitString) : Option Cell :=
  (Dict.get root key).map Slice.toCellRemaining

/-- A dictionary with `n`-bit keys every lookup of which succeeds (with the default resolver): no
node on the path of any key is ill-formed or exotic. -/
def Dict.WF (root : Option Cell) (n : Nat) : Prop :=
  ∀ key : BitString, key.size = n → ∃ x, dictLookupWithCells root key = .ok x

@[simp] theorem Dict.value_none (key : BitString) : Dict.value none key = none := rfl

/-- The empty dictionary is well-formed. -/
theorem Dict.WF.empty (n : Nat) : Dict.WF none n := fun _ _ => ⟨_, rfl⟩

namespace DictMap

theorem val_ok_iff (x : Except Excno (Option Slice × Array Cell)) :
    (∃ y, x = .ok y) ↔ ∃ w, val x = .ok w := by
  cases x with
  | error e => simp [val]
  | ok y => simp [val]

/-- What a successful lookup says, as `Dict.value`. -/
theorem value_of_val {root : Option Cell} {key : BitString} {w : Option Cell}
    (h : val (dictLookupWithCells root key) = .ok w) : Dict.value root key = w := by
  unfold Dict.value Dict.get
  cases hx : dictLookupWithCells root key with
  | error e => rw [hx] at h; cases h
  | ok y =>
    rw [hx] at h
    simp only [val, Except.ok.injEq] at h
    exact h

/-- On a well-formed dictionary, the lookup says `Dict.value`. -/
theorem val_eq_value {root : Option Cell} {n : Nat} (hwf : Dict.WF root n) {key : BitString}
    (hk : key.size = n) : val (dictLookupWithCells root key) = .ok (Dict.value root key) := by
  obtain ⟨y, hy⟩ := hwf key hk
  rw [hy]
  rcases y with ⟨v, cells⟩
  simp only [val, Dict.value, Dict.get, hy]

/-- The root of a well-formed non-empty dictionary reads as a label. -/
theorem WF_parse {c : Cell} {n : Nat} (hwf : Dict.WF (some c) n) :
    ∃ lbl, parseDictLabel c n Cell.rejectSpecial = .ok lbl ∧
      (n - lbl.len > 0 → lbl.remainder.bitsRemaining = lbl.storedBits ∧ lbl.remainder.refsRemaining = 2) := by
  obtain ⟨y, hy⟩ := hwf (Array.replicate n false) (by simp)
  rw [lookup_some, Array.size_replicate, dictLookupAuxWithCells_eq] at hy
  unfold dictLookupWithCellsStep at hy
  cases hp : parseDictLabel c n Cell.rejectSpecial with
  | error e => rw [hp] at hy; cases hy
  | ok lbl =>
    refine ⟨lbl, rfl, fun hpos => ?_⟩
    rw [hp] at hy
    dsimp only [bind, Except.bind] at hy
    rw [dictValidateNodeExt_eq] at hy
    by_cases hbad : n - lbl.len > 0 ∧
        (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)
    · rw [if_pos hbad] at hy; cases hy
    · simp only [not_and, not_or, Decidable.not_not] at hbad
      exact hbad hpos

/-- The children of a fork of a well-formed dictionary are well-formed dictionaries with the
keys shorter by the label and the bit. -/
theorem WF_child {c : Cell} {n : Nat} {lbl : DictLabel} (hwf : Dict.WF (some c) n)
    (hp : parseDictLabel c n Cell.rejectSpecial = .ok lbl) (hfork : n - lbl.len > 0) (b : Bool) :
    Dict.WF (some (lbl.remainder.cell.refs[if b then 1 else 0]!)) (n - lbl.len - 1) := by
  intro k hk
  obtain ⟨_, _, _, _, hlen, hsz, _⟩ := parseDictLabel_ok hp
  let K := dictLabelBits lbl ++ #[b] ++ k
  have hK : K.size = n := by
    simp only [K, Array.size_append, hsz, List.size_toArray, List.length_cons, List.length_nil]; omega
  obtain ⟨y, hy⟩ := hwf K hK
  have hv : ∃ w, val (dictLookupWithCells (some c) K) = .ok w := (val_ok_iff _).mp ⟨y, hy⟩
  rw [lookup_some, val_lookup_node Cell.rejectSpecial c K lbl (by rw [hK]; exact hp)] at hv
  have h3 := (extract_three_iff K (dictLabelBits lbl) #[] b lbl.len 0 hsz rfl (by omega))
  have hm : K.extract 0 lbl.len = dictLabelBits lbl := by
    have : K.extract 0 (lbl.len + 1 + 0) = dictLabelBits lbl ++ #[b] ++ #[] := by
      apply bits_ext (by simp [K, hsz] <;> omega)
      intro i hi
      simp only [Array.size_extract] at hi
      simp only [K, Array.append_empty]
      rw [bget_extract, if_pos (by simp [hsz]; omega), Nat.zero_add,
        bget_append_left (by simp [hsz]; omega)]
    exact (h3.mp this).1
  have hb : K[lbl.len]! = b := by
    simp only [K]
    rw [bget_append_left (by simp [hsz]), bget_append_right (by simp [hsz]), hsz, Nat.sub_self]; rfl
  have hrest : K.extract (lbl.len + 1) K.size = k := by
    simp only [K]
    rw [show (dictLabelBits lbl ++ #[b] ++ k).size = (dictLabelBits lbl ++ #[b]).size + k.size by simp,
      show lbl.len + 1 = (dictLabelBits lbl ++ #[b]).size by simp [hsz],
      extract_append_of_ge (Nat.le_refl _), Nat.sub_self, Nat.add_sub_cancel_left]
    exact extract_all (Nat.le_refl _)
  by_cases hbad : K.size - lbl.len > 0 ∧
      (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)
  · rw [if_pos hbad] at hv; obtain ⟨w, hw⟩ := hv; cases hw
  · rw [if_neg hbad, if_pos hm, if_neg (show ¬ K.size = lbl.len by omega), hb, hrest] at hv
    obtain ⟨y', hy'⟩ := (val_ok_iff _).mpr hv
    rw [hk] at hy'
    refine ⟨y', ?_⟩
    rw [lookup_some, hk]
    exact hy'

/-- **A set with any resolver of ordinary cells**, on a well-formed dictionary, is the set with the
default resolver: every node it reads is ordinary. -/
theorem set_resolve (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (sv : Builder → Except Excno Builder)
    (mode : DictSetMode) : ∀ (n : Nat) (root : Option Cell) (key : BitString), key.size = n → Dict.WF root n →
      dictSetGenAuxWithCells root key sv mode r = dictSetGenAuxWithCells root key sv mode := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro root key hk hwf
  subst hk
  rw [dictSetGenAuxWithCells.eq_def root key sv mode r,
    dictSetGenAuxWithCells.eq_def root key sv mode Cell.rejectSpecial]
  cases root with
  | none => rfl
  | some c =>
    obtain ⟨lbl, hp, _⟩ := WF_parse hwf
    have hpr := parseDictLabel_of_rejectSpecial c key.size r hr lbl hp
    dsimp only
    rw [hp, hpr]
    dsimp only [bind, Except.bind]
    cases hv : dictValidateNodeExtLe lbl key.size with
    | error e => rfl
    | ok v =>
      dsimp only
      obtain ⟨hv1, -⟩ := dictValidateNodeExtLe_ok hv
      by_cases hs : dictCommonPrefixLen lbl key < lbl.len
      · simp only [hs, if_true]
      · simp only [hs, if_false]
        by_cases h0 : v.val = 0
        · simp only [h0, dif_pos]
        · simp only [dif_neg h0]
          have hc1 : Dict.WF (some lbl.remainder.cell.refs[1]!) (key.size - lbl.len - 1) :=
            WF_child hwf hp (by omega) true
          have hc0 : Dict.WF (some lbl.remainder.cell.refs[0]!) (key.size - lbl.len - 1) :=
            WF_child hwf hp (by omega) false
          have hsz : (key.extract (lbl.len + 1) key.size).size = key.size - lbl.len - 1 := by simp; omega
          rw [ih _ (by omega) _ _ hsz hc1, ih _ (by omega) _ _ hsz hc0]

/-- A lookup with any resolver of ordinary cells, on a well-formed dictionary, is the lookup with
the default resolver. -/
theorem lookup_resolve (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) {root : Option Cell} {n : Nat}
    (hwf : Dict.WF root n) {key : BitString} (hk : key.size = n) :
    dictLookupWithCells root key r = dictLookupWithCells root key := by
  obtain ⟨y, hy⟩ := hwf key hk
  rw [hy]
  exact dictLookupWithCells_of_rejectSpecial r hr root key y hy

/-- **A delete with any resolver of ordinary cells**, on a well-formed dictionary, is the delete
with the default resolver: every node it reads (on the key's path, and the surviving child of a
fork it merges) is ordinary. -/
theorem delete_resolve (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) :
    ∀ (rem : Nat) (cell : Cell) (key : BitString) (pos : Nat), Dict.WF (some cell) rem →
      dictDeleteAuxWithLoads cell key pos rem r = dictDeleteAuxWithLoads cell key pos rem Cell.rejectSpecial := by
  intro rem
  induction rem using Nat.strongRecOn with
  | _ rem ih =>
  intro cell key pos hwf
  rw [dictDeleteAuxWithLoads.eq_def cell key pos rem r,
    dictDeleteAuxWithLoads.eq_def cell key pos rem Cell.rejectSpecial]
  obtain ⟨lbl, hp, _⟩ := WF_parse hwf
  have hpr := parseDictLabel_of_rejectSpecial cell rem r hr lbl hp
  rw [hp, hpr]
  simp only [withLoads, Except.mapError, bind, Except.bind]
  cases hv : dictValidateNodeExtLe lbl rem with
  | error e => rfl
  | ok v =>
    dsimp only
    obtain ⟨hv1, -⟩ := dictValidateNodeExtLe_ok hv
    by_cases hm : (!dictLabelMatches lbl key pos) = true
    · simp only [hm, if_true]
    · simp only [hm, if_false, Bool.false_eq_true]
      by_cases h0 : v.val = 0
      · simp only [h0, dif_pos]
      · simp only [dif_neg h0]
        have hc1 : Dict.WF (some lbl.remainder.cell.refs[1]!) (rem - lbl.len - 1) :=
          WF_child hwf hp (by omega) true
        have hc0 : Dict.WF (some lbl.remainder.cell.refs[0]!) (rem - lbl.len - 1) :=
          WF_child hwf hp (by omega) false
        obtain ⟨l1, hp1, _⟩ := WF_parse hc1
        obtain ⟨l0, hp0, _⟩ := WF_parse hc0
        rw [hv1] at *
        cases hb : key[pos + lbl.len]!
        · simp only [Bool.false_eq_true, if_false]
          rw [ih _ (by omega) _ _ _ hc0, hp1, parseDictLabel_of_rejectSpecial _ _ r hr l1 hp1]
        · simp only [if_true]
          rw [ih _ (by omega) _ _ _ hc1, hp0, parseDictLabel_of_rejectSpecial _ _ r hr l0 hp0]

/-- The cells a lookup visits (charged when a set fails), with any resolver of ordinary cells,
on a well-formed dictionary: as with the default resolver. -/
theorem visitedF_resolve (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (f : Nat) :
    ∀ (cell : Cell) (key : BitString) (pos rem : Nat), Dict.WF (some cell) rem →
      dictLookupVisitedCellsAuxF r f cell key pos rem =
        dictLookupVisitedCellsAuxF Cell.rejectSpecial f cell key pos rem := by
  induction f with
  | zero => intros; rfl
  | succ f ih =>
    intro cell key pos rem hwf
    simp only [dictLookupVisitedCellsAuxF]
    unfold dictLookupVisitedStep
    obtain ⟨lbl, hp, _⟩ := WF_parse hwf
    rw [hp, parseDictLabel_of_rejectSpecial cell rem r hr lbl hp]
    dsimp only
    by_cases h0 : rem - lbl.len = 0
    · simp only [h0, if_true]
    · simp only [h0, if_false]
      have hc1 : Dict.WF (some lbl.remainder.cell.refs[1]!) (rem - lbl.len - 1) :=
        WF_child hwf hp (by omega) true
      have hc0 : Dict.WF (some lbl.remainder.cell.refs[0]!) (rem - lbl.len - 1) :=
        WF_child hwf hp (by omega) false
      cases hb : key[pos + lbl.len]!
      · simp only [Bool.false_eq_true, if_false]
        rw [ih _ _ _ _ hc0]
      · simp only [if_true]
        rw [ih _ _ _ _ hc1]

theorem visited_resolve (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) {root : Option Cell}
    {key : BitString} (hwf : Dict.WF root key.size) :
    dictLookupVisitedCells root key r = dictLookupVisitedCells root key := by
  cases root with
  | none => rfl
  | some c =>
    simp only [dictLookupVisitedCells, dictLookupVisitedCellsAux]
    exact visitedF_resolve r hr _ c key 0 key.size hwf

/-- A set that does not change the dictionary (`ok = false`: an `ADD` of a present key, a
`REPLACE` of an absent one) returns the root unchanged. -/
theorem set_unchanged {r : Cell → Except Excno Cell} {sv : Builder → Except Excno Builder} {mode : DictSetMode}
    {root root' : Option Cell} {key : BitString} {created : Nat} {loaded : Array Cell}
    (h : dictSetGenAuxWithCells root key sv mode r = .ok (root', false, created, loaded)) : root' = root := by
  rw [dictSetGenAuxWithCells.eq_def] at h
  cases root with
  | none =>
    dsimp only [bind, Except.bind] at h
    repeat' (first | (cases h; done) | (simp [pure, Except.pure] at h; done) | split at h)
    all_goals (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h)
    all_goals first | exact h.1.symm | (simp at h)
  | some c =>
    dsimp only [bind, Except.bind] at h
    repeat' (first | (cases h; done) | (simp [pure, Except.pure] at h; done) | split at h)
    all_goals (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h)
    all_goals first | exact h.1.symm | (simp at h)

/-- A set in mode `.set` (`DICTSET`) that succeeds always changes the dictionary. -/
theorem set_set_changed {r : Cell → Except Excno Cell} {sv : Builder → Except Excno Builder} :
    ∀ (n : Nat) (root : Option Cell) (key : BitString), key.size = n →
      ∀ res, dictSetGenAuxWithCells root key sv .set r = .ok res → res.2.1 = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro root key hk res h
  subst hk
  rw [dictSetGenAuxWithCells.eq_def] at h
  have e1 : (DictSetMode.set == DictSetMode.replace) = false := rfl
  have e2 : (DictSetMode.set == DictSetMode.add) = false := rfl
  cases root with
  | none =>
    dsimp only [bind, Except.bind] at h
    simp only [e1, Bool.false_eq_true, if_false] at h
    repeat' (first | (cases h; done) | split at h)
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | some c =>
    dsimp only [bind, Except.bind] at h
    simp only [e1, e2, Bool.false_eq_true, if_false] at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · -- the split edge
      repeat' (first | (cases h; done) | split at h)
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
    · dsimp only [pure, Except.pure] at h
      split at h
      · -- the leaf replaced
        repeat' (first | (cases h; done) | split at h)
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; rfl
      · -- the fork: the child changed, so does the fork
        split at h
        all_goals
          split at h
          · cases h
          rename_i v hrec
          have hv := ih _ (by simp; omega) _ _ rfl v hrec
          split at h
          · rename_i hnok; simp [hv] at hnok
          repeat' (first | (cases h; done) | split at h)
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h; rfl

/-- **Get after set, on the map.** On a well-formed dictionary, a set that changes it (`ok`) makes
the value of `key` the stored one (`vb.finalize`: the bits and references stored) and leaves the
value of every other key of the same length. -/
theorem _root_.TvmLean.Dict.value_set {root root' : Option Cell} {key : BitString} {vb : Builder}
    {mode : DictSetMode} {created : Nat} {loaded : Array Cell} (hwf : Dict.WF root key.size)
    (h : dictSetGenAuxWithCells root key (storeB vb) mode = .ok (root', true, created, loaded))
    (key' : BitString) (hk' : key'.size = key.size) :
    Dict.value root' key' = if key' = key then some vb.finalize else Dict.value root key' := by
  have hv := val_set Cell.rejectSpecial resolvesOrdinary_rejectSpecial vb mode _ root key rfl root' created loaded h
    key' hk'
  rw [val_eq_value hwf hk'] at hv
  apply value_of_val
  rw [hv]
  split <;> rfl

/-- A set keeps a dictionary well-formed. -/
theorem _root_.TvmLean.Dict.WF.set {root root' : Option Cell} {key : BitString} {vb : Builder}
    {mode : DictSetMode} {ok : Bool} {created : Nat} {loaded : Array Cell} (hwf : Dict.WF root key.size)
    (h : dictSetGenAuxWithCells root key (storeB vb) mode = .ok (root', ok, created, loaded)) :
    Dict.WF root' key.size := by
  cases ok with
  | false => rw [set_unchanged h]; exact hwf
  | true =>
    intro key' hk'
    have hv := val_set Cell.rejectSpecial resolvesOrdinary_rejectSpecial vb mode _ root key rfl root' created loaded
      h key' hk'
    rw [val_eq_value hwf hk'] at hv
    apply (val_ok_iff _).mpr
    rw [hv]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- **Get after delete, on the map.** On a well-formed dictionary, a delete that removed a value
removed the value of `key`, makes `key` absent and leaves every other key. -/
theorem _root_.TvmLean.Dict.value_delete {root root' : Option Cell} {key : BitString} {oldV : Slice}
    {created : Nat} {loaded : Array Cell} (hwf : Dict.WF root key.size)
    (h : dictDeleteWithLoads root key = .ok (some oldV, root', created, loaded)) :
    Dict.value root key = some oldV.toCellRemaining ∧
      ∀ key' : BitString, key'.size = key.size →
        Dict.value root' key' = if key' = key then none else Dict.value root key' := by
  obtain ⟨h1, h2⟩ := val_deleteWithLoads Cell.rejectSpecial resolvesOrdinary_rejectSpecial root key oldV root'
    created loaded h
  refine ⟨value_of_val h1, fun key' hk' => ?_⟩
  have hv := h2 key' hk'
  rw [val_eq_value hwf hk'] at hv
  apply value_of_val
  rw [hv]
  split <;> rfl

/-- A delete keeps a dictionary well-formed. -/
theorem _root_.TvmLean.Dict.WF.delete {root root' : Option Cell} {key : BitString} {old : Option Slice}
    {created : Nat} {loaded : Array Cell} (hwf : Dict.WF root key.size)
    (h : dictDeleteWithLoads root key = .ok (old, root', created, loaded)) : Dict.WF root' key.size := by
  cases old with
  | none => rw [deleteWithLoads_none Cell.rejectSpecial root key root' created loaded h]; exact hwf
  | some oldV =>
    intro key' hk'
    obtain ⟨_, h2⟩ := val_deleteWithLoads Cell.rejectSpecial resolvesOrdinary_rejectSpecial root key oldV root'
      created loaded h
    have hv := h2 key' hk'
    rw [val_eq_value hwf hk'] at hv
    apply (val_ok_iff _).mpr
    rw [hv]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- **A delete that finds nothing**: the lookup of the key finds nothing either. -/
theorem val_delete_none (r : Cell → Except Excno Cell) :
    ∀ (rem : Nat) (cell : Cell) (key : BitString) (pos : Nat), key.size = pos + rem →
    ∀ (newCell : Option Cell) (created : Nat) (loaded : Array Cell),
      dictDeleteAuxWithLoads cell key pos rem r = .ok (none, newCell, created, loaded) →
      val (dictLookupAuxWithCells cell (key.extract pos key.size) 0 rem r) = .ok none := by
  intro rem
  induction rem using Nat.strongRecOn with
  | _ rem ih =>
  intro cell key pos hks newCell created loaded h
  rw [dictDeleteAuxWithLoads] at h
  dsimp only [bind, Except.bind] at h
  have hksz : (key.extract pos key.size).size = rem := by simp; omega
  split at h
  · cases h
  rename_i lbl hpl
  have hp := withLoads_ok hpl
  split at h
  · cases h
  rename_i v hvl
  obtain ⟨hv1, hv2⟩ := dictValidateNodeExtLe_ok (withLoads_ok hvl)
  obtain ⟨c', hrc, hcell, hrp, hlen, hsz, hst⟩ := parseDictLabel_ok hp
  have hpk : parseDictLabel cell (key.extract pos key.size).size r = .ok lbl := by rw [hksz]; exact hp
  have hnb : ∀ n : Nat, n = rem → ¬ (n - lbl.len > 0 ∧
      (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)) := by
    rintro n rfl ⟨h1, h2⟩
    obtain ⟨e1, e2⟩ := hv2 h1
    rcases h2 with h2 | h2 <;> contradiction
  rw [← hksz, val_lookup_node r cell _ lbl hpk, if_neg (hnb _ hksz)]
  split at h
  · rename_i hmis
    have hmatchB : dictLabelMatches lbl key pos = false := by simpa using hmis
    rw [dictLabelMatches_shift lbl key pos (by omega)] at hmatchB
    rw [if_neg]
    intro hm
    have := (dictLabelMatches_iff lbl (key.extract pos key.size) 0 hsz).mpr ⟨by omega, by simpa using hm⟩
    rw [hmatchB] at this
    cases this
  rename_i hmatch0
  have hmatchB : dictLabelMatches lbl key pos = true := by simpa using hmatch0
  rw [dictLabelMatches_shift lbl key pos (by omega)] at hmatchB
  have hmatch := ((dictLabelMatches_iff lbl _ 0 hsz).mp hmatchB).2
  simp only [Nat.zero_add] at hmatch
  rw [if_pos hmatch]
  dsimp only [pure, Except.pure] at h
  split at h
  · simp at h
  rename_i h0
  rw [if_neg (show ¬ (key.extract pos key.size).size = lbl.len by omega)]
  have hbit : (key.extract pos key.size)[lbl.len]! = key[pos + lbl.len]! := bget_suffix _ _ _
  have hrest : (key.extract pos key.size).extract (lbl.len + 1) (key.extract pos key.size).size =
      key.extract (pos + lbl.len + 1) key.size := by
    rw [extract_suffix_suffix, Nat.add_assoc]
  have hrsz : (key.extract (pos + lbl.len + 1) key.size).size = v.val - 1 := by simp; omega
  split at h
  · cases h
  rename_i res hres
  have hres' := underCell_ok hres
  split at h
  · rename_i hov
    have hres'' : dictDeleteAuxWithLoads (if key[pos + lbl.len]! = true then lbl.remainder.cell.refs[1]!
        else lbl.remainder.cell.refs[0]!) key (pos + lbl.len + 1) (v.val - 1) r =
        .ok (none, res.2.1, res.2.2.1, res.2.2.2) := by
      rw [hres', ← hov]
    have ih1 := ih (v.val - 1) (by omega) _ key (pos + lbl.len + 1) (by omega) _ _ _ hres''
    rw [ite_refs] at ih1
    rw [hbit, hrest, hrsz]
    exact ih1
  · repeat' (first | (cases h; done) | (simp at h; done) | split at h)
    all_goals (simp [pure, Except.pure] at h)

theorem deleteWithLoads_none_val (root : Option Cell) (key : BitString) (newRoot : Option Cell) (created : Nat)
    (loaded : Array Cell) (h : dictDeleteWithLoads root key = .ok (none, newRoot, created, loaded)) :
    val (dictLookupWithCells root key) = .ok none := by
  cases root with
  | none => rfl
  | some c =>
    simp only [dictDeleteWithLoads] at h
    have := val_delete_none Cell.rejectSpecial key.size c key 0 (by simp) _ _ _ h
    rw [extract_all (Nat.le_refl _)] at this
    exact this

/-- **Get after any delete, on the map**: the key is absent after it, every other key of the same
length as before; the delete found a value iff the key had one. -/
theorem _root_.TvmLean.Dict.value_deleteAny {root root' : Option Cell} {key : BitString} {old : Option Slice}
    {created : Nat} {loaded : Array Cell} (hwf : Dict.WF root key.size)
    (h : dictDeleteWithLoads root key = .ok (old, root', created, loaded)) :
    Dict.value root key = old.map Slice.toCellRemaining ∧
      ∀ key' : BitString, key'.size = key.size →
        Dict.value root' key' = if key' = key then none else Dict.value root key' := by
  cases old with
  | some oldV => exact Dict.value_delete hwf h
  | none =>
    have hnone := value_of_val (deleteWithLoads_none_val root key root' created loaded h)
    rw [deleteWithLoads_none Cell.rejectSpecial root key root' created loaded h]
    refine ⟨hnone, fun key' _ => ?_⟩
    by_cases hk : key' = key
    · rw [if_pos hk, hk, hnone]
    · rw [if_neg hk]

end DictMap

end TvmLean

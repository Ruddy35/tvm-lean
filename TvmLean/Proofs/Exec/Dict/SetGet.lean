import TvmLean.Proofs.Exec.Dict.Loaded

/-!
# Lookup-and-set: the set, and the old value

`DICT*SETGET`, `...REPLACEGET`, `...ADDGET` (C++ `dict.lookup_set`, dict.cpp) run
`dictLookupSetGenAuxWithCells`, which walks the dictionary as the set does and also returns the
value the key had. Here:

* `DictMap.lookupSet_snd`: without the old value it is the set (`dictSetGenAuxWithCells`): the
  same new root, flag, cells created and cells loaded, the same errors; so everything known of
  the set (`Dict.value_set`, `Dict.WF.set`, `DictMap.set_loaded`, ...) holds of it;
* `DictMap.val_lookupSet_old`: the old value is the value the lookup finds (its contents);
* `DictMap.lookupSet_resolve`: on a well-formed dictionary any resolver of ordinary cells gives
  the result of the default one.
-/

namespace TvmLean

namespace DictMap

theorem dictLabelBits_eq (lbl : DictLabel) :
    dictLabelBits lbl = match lbl.sameBit with
      | some b => Array.replicate lbl.len b
      | none => lbl.remainder.readBits lbl.len := by
  unfold dictLabelBits; rfl

theorem map_bind' {ε α β γ : Type} (x : Except ε α) (f : α → Except ε β) (g : β → γ) :
    Except.map g (x >>= f) = x >>= fun a => Except.map g (f a) := by
  cases x <;> rfl

theorem bind_map' {ε α β γ : Type} (x : Except ε α) (g : α → β) (f : β → Except ε γ) :
    (Except.map g x) >>= f = x >>= fun a => f (g a) := by
  cases x <;> rfl

theorem ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem error_bind' {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl

theorem map_pure' {ε β γ : Type} (a : β) (g : β → γ) : Except.map g (pure a : Except ε β) = pure (g a) := rfl

theorem map_ite' {ε β γ : Type} (c : Prop) [Decidable c] (a b : Except ε β) (g : β → γ) :
    Except.map g (if c then a else b) = if c then Except.map g a else Except.map g b := by
  split <;> rfl

theorem map_dite' {ε β γ : Type} (c : Prop) [Decidable c] (a : c → Except ε β) (b : ¬c → Except ε β) (g : β → γ) :
    Except.map g (if h : c then a h else b h) = if h : c then Except.map g (a h) else Except.map g (b h) := by
  split <;> rfl

/-- **The set inside a lookup-and-set**: without the old value, `dictLookupSetGenAuxWithCells` is
`dictSetGenAuxWithCells` (the same walk, the same results and errors). -/
theorem lookupSet_snd (r : Cell → Except Excno Cell) (sv : Builder → Except Excno Builder) (mode : DictSetMode) :
    ∀ (n : Nat) (root : Option Cell) (key : BitString), key.size = n →
      (dictLookupSetGenAuxWithCells root key sv mode r).map Prod.snd = dictSetGenAuxWithCells root key sv mode r := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro root key hk
  rw [dictLookupSetGenAuxWithCells.eq_def, dictSetGenAuxWithCells.eq_def]
  cases root with
  | none =>
    dsimp only
    split
    · rfl
    · simp only [bind, Except.bind]
      cases builderStoreBitsChecked Builder.empty (dictLabelEncode key key.size key.size) with
      | error e => rfl
      | ok b1 =>
        dsimp only
        cases sv b1 with
        | error e => rfl
        | ok b2 => rfl
  | some cell =>
    dsimp only
    simp only [map_bind', map_pure', map_ite', map_dite', dictLabelBits_eq]
    cases hp : parseDictLabel cell key.size r with
    | error e => rfl
    | ok lbl =>
      simp only [ok_bind']
      cases hv : dictValidateNodeExtLe lbl key.size with
      | error e => rfl
      | ok v =>
        simp only [ok_bind']
        obtain ⟨hv1, -⟩ := dictValidateNodeExtLe_ok hv
        by_cases hpfx : dictCommonPrefixLen lbl key < lbl.len
        · simp only [hpfx, if_true]
          rfl
        · simp only [hpfx, if_false]
          by_cases h0 : v.val = 0
          · simp only [h0, dif_pos]
          · simp only [dif_neg h0, pure_bind]
            have hlt : (key.extract (lbl.len + 1)).size < n := by simp; omega
            by_cases hb : key[lbl.len]! = true
            · simp only [hb, if_true]
              rw [← ih _ hlt _ _ rfl, bind_map']
              cases dictLookupSetGenAuxWithCells (some lbl.remainder.cell.refs[1]!) (key.extract (lbl.len + 1))
                sv mode r with
              | error e => rfl
              | ok d =>
              simp only [ok_bind']
              rcases d with ⟨old, newR, ok, created, loaded⟩
              cases ok
              · rfl
              · cases newR
                · rfl
                · simp only [map_bind', map_pure', Bool.not_true, Bool.false_eq_true, if_false]
            · rw [if_neg hb, if_neg hb]
              rw [← ih _ hlt _ _ rfl, bind_map']
              cases dictLookupSetGenAuxWithCells (some lbl.remainder.cell.refs[0]!) (key.extract (lbl.len + 1))
                sv mode r with
              | error e => rfl
              | ok d =>
              simp only [ok_bind']
              rcases d with ⟨old, newR, ok, created, loaded⟩
              cases ok
              · rfl
              · cases newR
                · rfl
                · simp only [map_bind', map_pure', Bool.not_true, Bool.false_eq_true, if_false]


/-- **The old value of a lookup-and-set** is the value the lookup finds (its contents). -/
theorem val_lookupSet_old (r : Cell → Except Excno Cell) (sv : Builder → Except Excno Builder) (mode : DictSetMode) :
    ∀ (n : Nat) (root : Option Cell) (key : BitString), key.size = n →
      ∀ res, dictLookupSetGenAuxWithCells root key sv mode r = .ok res →
        val (dictLookupWithCells root key r) = .ok (res.1.map Slice.toCellRemaining) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro root key hk res h
  rw [dictLookupSetGenAuxWithCells.eq_def] at h
  cases root with
  | none =>
    dsimp only at h
    rw [lookup_none]
    split at h
    · cases h; rfl
    · simp only [bind, Except.bind] at h
      repeat' (first | (cases h; done) | split at h)
      all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
  | some cell =>
    dsimp only at h
    rw [lookup_some]
    cases hp : parseDictLabel cell key.size r with
    | error e => rw [hp] at h; cases h
    | ok lbl =>
      rw [hp] at h
      simp only [ok_bind'] at h
      cases hv : dictValidateNodeExtLe lbl key.size with
      | error e => rw [hv] at h; cases h
      | ok v =>
        rw [hv] at h
        simp only [ok_bind'] at h
        obtain ⟨hv1, hv2⟩ := dictValidateNodeExtLe_ok hv
        obtain ⟨c', hrc, hcell, hrp, hlen, hsz, hst⟩ := parseDictLabel_ok hp
        have hnb : ¬ (key.size - lbl.len > 0 ∧
            (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)) := by
          rintro ⟨h1, h2⟩
          obtain ⟨e1, e2⟩ := hv2 h1
          rcases h2 with h2 | h2 <;> contradiction
        rw [val_lookup_node r cell key lbl hp, if_neg hnb]
        obtain ⟨hpl, hpre, hdiff⟩ := dictCommonPrefixLen_spec lbl key hlen
        by_cases hpfx : dictCommonPrefixLen lbl key < lbl.len
        · -- the key leaves the edge: absent
          have hne : ¬ key.extract 0 lbl.len = dictLabelBits lbl := by
            intro heq
            apply hdiff hpfx
            have := congrArg (fun a : BitString => a[dictCommonPrefixLen lbl key]!) heq
            simp only at this
            rw [bget_extract, if_pos (by simp; omega), Nat.zero_add] at this
            exact this.symm
          rw [if_neg hne]
          simp only [hpfx, if_true] at h
          split at h
          · cases h; rfl
          · simp only [pure_bind, bind, Except.bind] at h
            repeat' (first | (cases h; done) | split at h)
            all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
        · have heq : key.extract 0 lbl.len = dictLabelBits lbl := by
            apply bits_ext (by simp; omega)
            intro i hi
            simp only [Array.size_extract] at hi
            rw [bget_extract, if_pos (by simp; omega), Nat.zero_add]
            exact (hpre i (by omega)).symm
          rw [if_pos heq]
          simp only [hpfx, if_false, pure_bind] at h
          split at h
          · -- a leaf: its value
            rename_i h0
            rw [if_pos (by omega)]
            split at h
            · cases h; rfl
            · simp only [pure_bind, bind, Except.bind] at h
              repeat' (first | (cases h; done) | split at h)
              all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
          · -- a fork: the child's
            rename_i h0
            rw [if_neg (by omega)]
            have hlt : (key.extract (lbl.len + 1)).size < n := by simp; omega
            have hchild : ∀ (b : Bool) res', dictLookupSetGenAuxWithCells
                (some lbl.remainder.cell.refs[if b then 1 else 0]!) (key.extract (lbl.len + 1)) sv mode r = .ok res' →
                val (dictLookupAuxWithCells lbl.remainder.cell.refs[if b then 1 else 0]!
                  (key.extract (lbl.len + 1) key.size) 0 (key.extract (lbl.len + 1) key.size).size r) =
                  .ok (res'.1.map Slice.toCellRemaining) := by
              intro b res' h'
              have := ih _ hlt _ _ rfl res' h'
              rw [lookup_some] at this
              exact this
            by_cases hb : key[lbl.len]! = true
            · simp only [hb, if_true] at h ⊢
              cases hd : dictLookupSetGenAuxWithCells (some lbl.remainder.cell.refs[1]!) (key.extract (lbl.len + 1))
                sv mode r with
              | error e => rw [hd] at h; cases h
              | ok d =>
                rw [hd] at h
                simp only [ok_bind'] at h
                have hc := hchild true d (by simpa using hd)
                simp only [if_true] at hc
                rw [hc]
                split at h
                · cases h; rfl
                · simp only [pure_bind, bind, Except.bind] at h
                  repeat' (first | (cases h; done) | split at h)
                  all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
            · simp only [hb, if_false, Bool.false_eq_true] at h ⊢
              cases hd : dictLookupSetGenAuxWithCells (some lbl.remainder.cell.refs[0]!) (key.extract (lbl.len + 1))
                sv mode r with
              | error e => rw [hd] at h; cases h
              | ok d =>
                rw [hd] at h
                simp only [ok_bind'] at h
                have hc := hchild false d (by simpa using hd)
                simp only [Bool.false_eq_true, if_false] at hc
                rw [hc]
                split at h
                · cases h; rfl
                · simp only [pure_bind, bind, Except.bind] at h
                  repeat' (first | (cases h; done) | split at h)
                  all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)

/-- **A lookup-and-set with any resolver of ordinary cells**, on a well-formed dictionary, is the
lookup-and-set with the default resolver. -/
theorem lookupSet_resolve (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (sv : Builder → Except Excno Builder)
    (mode : DictSetMode) : ∀ (n : Nat) (root : Option Cell) (key : BitString), key.size = n → Dict.WF root n →
      dictLookupSetGenAuxWithCells root key sv mode r = dictLookupSetGenAuxWithCells root key sv mode := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro root key hk hwf
  subst hk
  rw [dictLookupSetGenAuxWithCells.eq_def root key sv mode r,
    dictLookupSetGenAuxWithCells.eq_def root key sv mode Cell.rejectSpecial]
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

/-- A lookup-and-set that succeeds is a set that succeeds, with the same results. -/
theorem lookupSet_set {sv : Builder → Except Excno Builder} {mode : DictSetMode} {r : Cell → Except Excno Cell}
    {root : Option Cell} {key : BitString} {res : Option Slice × Option Cell × Bool × Nat × Array Cell}
    (h : dictLookupSetGenAuxWithCells root key sv mode r = .ok res) :
    dictSetGenAuxWithCells root key sv mode r = .ok res.2 := by
  rw [← lookupSet_snd r sv mode _ root key rfl, h]
  rfl

/-- A lookup-and-set that fails is a set that fails, with the same error. -/
theorem lookupSet_set_error {sv : Builder → Except Excno Builder} {mode : DictSetMode} {r : Cell → Except Excno Cell}
    {root : Option Cell} {key : BitString} {e : Excno}
    (h : dictLookupSetGenAuxWithCells root key sv mode r = .error e) :
    dictSetGenAuxWithCells root key sv mode r = .error e := by
  rw [← lookupSet_snd r sv mode _ root key rfl, h]
  rfl

theorem dictLookupSetSliceWithCells_eq (root : Option Cell) (key : BitString) (val : Slice) (mode : DictSetMode)
    (r : Cell → Except Excno Cell) :
    dictLookupSetSliceWithCells root key val mode r = dictLookupSetGenAuxWithCells root key (storeB (sliceB val)) mode r := by
  simp only [dictLookupSetSliceWithCells]
  rfl

theorem dictLookupSetRefWithCells_eq (root : Option Cell) (key : BitString) (c : Cell) (mode : DictSetMode)
    (r : Cell → Except Excno Cell) :
    dictLookupSetRefWithCells root key c mode r = dictLookupSetGenAuxWithCells root key (storeB (refB c)) mode r := by
  simp only [dictLookupSetRefWithCells, storeRef_eq]

theorem dictLookupSetBuilderWithCells_eq (root : Option Cell) (key : BitString) (vb : Builder) (mode : DictSetMode)
    (r : Cell → Except Excno Cell) :
    dictLookupSetBuilderWithCells root key vb mode r = dictLookupSetGenAuxWithCells root key (storeB vb) mode r := by
  simp only [dictLookupSetBuilderWithCells]

end DictMap

end TvmLean

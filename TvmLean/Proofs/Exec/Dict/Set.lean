import TvmLean.Proofs.Exec.Dict.Lookup

/-!
# A set on a dictionary, seen through its map

`dictSetGenAuxWithCells` (C++ `DictionaryFixed::dict_set`, dict.cpp) adds or replaces the value of
a key: it walks the key from the root, splits the edge where the key leaves it (a new fork, the
lower part of the old edge `cOld`, a new leaf `cNew`), replaces a leaf, or rebuilds the forks on
the way back. Whatever the shape of the dictionary, a lookup after it (with the same resolver)
finds the new value at the key and what it found before at every other key of the same length
(`val_set`, as the contents of the values, `DictMap.val`), errors included.

The value is stored by `storeVal`; the three forms of the instructions (a slice, a reference, a
builder) append bits and references, as `builderAppendBuilderChecked` of a builder does
(`DictMap.storeB`, `dictSetSliceWithCells_eq` and the like).
-/

namespace TvmLean

namespace DictMap

/-! ## Arrays of bits: comparing keys -/

/-- Two keys of the same length are equal iff they agree before `p`, at `p` and after `p`. -/
theorem key_eq_iff (key key' : BitString) (p : Nat) (hs : key'.size = key.size) (hp : p < key.size) :
    key' = key ↔ key'.extract 0 p = key.extract 0 p ∧ key'[p]! = key[p]! ∧
      key'.extract (p + 1) key'.size = key.extract (p + 1) key.size := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    apply bits_ext hs
    intro i hi
    rcases Nat.lt_trichotomy i p with hlt | rfl | hgt
    · have := congrArg (·[i]!) h1
      simp only [bget_extract] at this
      rw [if_pos (by simp; omega), if_pos (by simp; omega)] at this
      simpa using this
    · exact h2
    · have := congrArg (·[i - (p + 1)]!) h3
      simp only [bget_extract] at this
      rw [if_pos (by simp; omega), if_pos (by simp; omega)] at this
      rwa [show p + 1 + (i - (p + 1)) = i by omega] at this

/-- Two bit strings differ if they differ at some position below both their sizes. -/
theorem ne_of_bget_ne {a b : BitString} {i : Nat} (h : a[i]! ≠ b[i]!) : a ≠ b := by
  rintro rfl; exact h rfl

theorem bget_extract_lt {a : BitString} {s e i : Nat} (h : s + i < e) (h' : s + i < a.size) :
    (a.extract s e)[i]! = a[s + i]! := by
  rw [bget_extract, if_pos (by omega)]

/-! ## The builders of the set -/

/-- The value of a dictionary entry stored as the bits and references of a builder (what the
three forms of `DICTSET` store: `dictSetSliceWithCells_eq` and the like). -/
abbrev storeB (vb : Builder) : Builder → Except Excno Builder := fun b => builderAppendBuilderChecked b vb

theorem storeBits_ok {b b' : Builder} {bs : BitString} (h : builderStoreBitsChecked b bs = .ok b') :
    b' = b.storeBits bs := by
  unfold builderStoreBitsChecked at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
  · cases h

theorem appendBuilder_ok {b v b' : Builder} (h : builderAppendBuilderChecked b v = .ok b') :
    b' = ⟨b.bits ++ v.bits, b.refs ++ v.refs⟩ := by
  unfold builderAppendBuilderChecked at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
  · cases h

theorem appendCell_ok {b b' : Builder} {c : Cell} (h : builderAppendCellChecked b c = .ok b') :
    b' = ⟨b.bits ++ c.bits, b.refs ++ c.refs⟩ := by
  unfold builderAppendCellChecked at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
  · cases h

theorem storeRef_ok {b b' : Builder} {c : Cell} (h : builderStoreRefChecked b c = .ok b') :
    b' = ⟨b.bits, b.refs.push c⟩ := by
  unfold builderStoreRefChecked at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
  · cases h

theorem dictValidateNodeExtLe_ok {lbl : DictLabel} {n : Nat} {v : {r : Nat // r ≤ n}}
    (h : dictValidateNodeExtLe lbl n = .ok v) :
    v.val = n - lbl.len ∧ (n - lbl.len > 0 →
      lbl.remainder.bitsRemaining = lbl.storedBits ∧ lbl.remainder.refsRemaining = 2) := by
  unfold dictValidateNodeExtLe at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · rename_i h1 h2
      simp at h
    · rename_i h1 h2
      simp only [Except.ok.injEq] at h
      subst h
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at h2
      exact ⟨rfl, fun _ => h2⟩
  · rename_i h1
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun h => absurd h h1⟩

/-- The lookup in a dictionary given by its root. -/
theorem lookup_some (r : Cell → Except Excno Cell) (c : Cell) (key : BitString) :
    dictLookupWithCells (some c) key r = dictLookupAuxWithCells c key 0 key.size r := rfl

theorem lookup_none (r : Cell → Except Excno Cell) (key : BitString) :
    dictLookupWithCells none key r = .ok (none, #[]) := rfl

/-- The lookup from a leaf built for `key` (the encoding of `key` as its label, then the value
`X`, `Y`): the value for `key`, nothing for the other keys of its length. -/
theorem val_lookup_leaf (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (key key' X : BitString)
    (Y : Array Cell) (hs : key'.size = key.size) :
    val (dictLookupAuxWithCells (Cell.mkOrdinary (dictLabelEncode key key.size key.size ++ X) Y) key' 0
        key'.size r) =
      if key' = key then .ok (some (Cell.mkOrdinary X Y)) else .ok none := by
  have := val_lookup_built r hr key X Y key' (by omega)
  rw [hs] at this
  rw [hs, this]
  have e : key'.extract 0 key.size = key ↔ key' = key := by
    rw [← hs, extract_all (Nat.le_refl _)]
  simp only [Nat.sub_self, gt_iff_lt, Nat.lt_irrefl, false_and, if_false, e, if_true]

/-- The lookup from a fork built by a set or a delete: the encoding of its label `bits` (of
length `len < key.size`), and its two children. -/
theorem val_lookup_fork (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (bits : BitString)
    (a b : Cell) (key : BitString) (len n : Nat) (hbl : bits.size = len) (hn : key.size = n) (hlt : len < n) :
    val (dictLookupAuxWithCells (Cell.mkOrdinary (dictLabelEncode bits len n) #[a, b]) key 0 key.size r) =
      if key.extract 0 len = bits then
        val (dictLookupAuxWithCells (if key[len]! then b else a) (key.extract (len + 1) key.size) 0
          (key.extract (len + 1) key.size).size r)
      else .ok none := by
  subst hbl hn
  have := val_lookup_built r hr bits #[] #[a, b] key (by omega)
  rw [Array.append_empty] at this
  rw [this]
  have h1 : ¬ (key.size - bits.size > 0 ∧ ((#[] : BitString).size ≠ 0 ∨ (#[a, b] : Array Cell).size ≠ 2)) := by
    simp
  rw [if_neg h1]
  have h2 : ¬ key.size = bits.size := by omega
  simp only [h2, if_false]
  congr 1
  cases key[bits.size]! <;> rfl

/-- The lookup from a leaf built for a key of `n` bits. -/
theorem val_lookup_leaf' (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (k key' X : BitString)
    (Y : Array Cell) (n : Nat) (hk : k.size = n) (hs : key'.size = n) :
    val (dictLookupAuxWithCells (Cell.mkOrdinary (dictLabelEncode k n n ++ X) Y) key' 0 key'.size r) =
      if key' = k then .ok (some (Cell.mkOrdinary X Y)) else .ok none := by
  subst hk
  exact val_lookup_leaf r hr k key' X Y hs

/-- **A fork rebuilt with one child replaced.** If the new child `x` is the old one with the value
of the rest of `key` changed to `V`, the fork rebuilt with its label (`dictLabelEncode`, C++
`append_dict_label`) is the old node with the value of `key` changed to `V`. -/
theorem val_rebuilt_fork (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (c : Cell)
    (lbl : DictLabel) (key : BitString) (x : Cell) (V : Except Excno (Option Cell)) (Y : Array Cell)
    (hp : parseDictLabel c key.size r = .ok lbl) (hlt : lbl.len < key.size)
    (hok : lbl.remainder.bitsRemaining = lbl.storedBits ∧ lbl.remainder.refsRemaining = 2)
    (hmatch : key.extract 0 lbl.len = dictLabelBits lbl)
    (hY : Y = if key[lbl.len]! then #[lbl.remainder.cell.refs[0]!, x] else #[x, lbl.remainder.cell.refs[1]!])
    (hx : ∀ key'' : BitString, key''.size = (key.extract (lbl.len + 1) key.size).size →
        val (dictLookupAuxWithCells x key'' 0 key''.size r) =
          if key'' = key.extract (lbl.len + 1) key.size then V
          else val (dictLookupAuxWithCells (lbl.remainder.cell.refs[if key[lbl.len]! then 1 else 0]!) key'' 0
            key''.size r))
    (key' : BitString) (hk' : key'.size = key.size) :
    val (dictLookupAuxWithCells (Cell.mkOrdinary (dictLabelEncode (dictLabelBits lbl) lbl.len key.size) Y)
        key' 0 key'.size r) =
      if key' = key then V else val (dictLookupAuxWithCells c key' 0 key'.size r) := by
  obtain ⟨_, _, _, _, _, hsz, _⟩ := parseDictLabel_ok hp
  have hp' : parseDictLabel c key'.size r = .ok lbl := by rw [hk']; exact hp
  rw [val_lookup_node r c key' lbl hp']
  have hbad : ¬ (key'.size - lbl.len > 0 ∧
      (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)) := by
    simp [hok]
  rw [if_neg hbad]
  have hne : ¬ key'.size = lbl.len := by omega
  simp only [hne, if_false]
  have hkey := key_eq_iff key key' lbl.len hk' hlt
  rw [hmatch] at hkey
  by_cases hY0 : key[lbl.len]! = true
  · rw [hY, if_pos hY0, val_lookup_fork r hr _ _ _ key' lbl.len key.size hsz hk' hlt]
    by_cases hm : key'.extract 0 lbl.len = dictLabelBits lbl
    · rw [if_pos hm, if_pos hm]
      by_cases hb : key'[lbl.len]! = true
      · rw [if_pos hb]
        have := hx (key'.extract (lbl.len + 1) key'.size) (by simp; omega)
        rw [this, if_pos hY0, if_pos hb]
        have e : (key'.extract (lbl.len + 1) key'.size = key.extract (lbl.len + 1) key.size) ↔ key' = key := by
          rw [hkey]; simp [hm, hb, hY0]
        simp only [e]
      · rw [if_neg hb]
        have hne' : key' ≠ key := by
          intro h; subst h; exact hb hY0
        rw [if_neg hne', if_neg hb]
    · rw [if_neg hm, if_neg hm]
      have hne' : key' ≠ key := by
        intro h; subst h; exact hm hmatch
      rw [if_neg hne']
  · rw [hY, if_neg hY0, val_lookup_fork r hr _ _ _ key' lbl.len key.size hsz hk' hlt]
    by_cases hm : key'.extract 0 lbl.len = dictLabelBits lbl
    · rw [if_pos hm, if_pos hm]
      by_cases hb : key'[lbl.len]! = true
      · rw [if_pos hb]
        have hne' : key' ≠ key := by
          intro h; subst h; exact hY0 hb
        rw [if_neg hne', if_pos hb]
      · rw [if_neg hb]
        have := hx (key'.extract (lbl.len + 1) key'.size) (by simp; omega)
        rw [this, if_neg hY0, if_neg hb]
        have e : (key'.extract (lbl.len + 1) key'.size = key.extract (lbl.len + 1) key.size) ↔ key' = key := by
          rw [hkey]; simp only [hm, true_and]
          simp only [Bool.not_eq_true] at hb hY0
          simp [hb, hY0]
        simp only [e]
    · rw [if_neg hm, if_neg hm]
      have hne' : key' ≠ key := by
        intro h; subst h; exact hm hmatch
      rw [if_neg hne']

/-- `val_lookup_built` with the length of the label and of the keys given. -/
theorem val_lookup_built' (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (bits X : BitString)
    (Y : Array Cell) (key : BitString) (len n : Nat) (hbl : bits.size = len) (hn : key.size = n) (hlen : len ≤ n) :
    val (dictLookupAuxWithCells (Cell.mkOrdinary (dictLabelEncode bits len n ++ X) Y) key 0 key.size r) =
      if n - len > 0 ∧ (X.size ≠ 0 ∨ Y.size ≠ 2) then .error .dictErr
      else if key.extract 0 len = bits then
        (if n = len then .ok (some (Cell.mkOrdinary X Y))
         else val (dictLookupAuxWithCells (Y[if key[len]! then 1 else 0]!)
          (key.extract (len + 1) key.size) 0 (key.extract (len + 1) key.size).size r))
      else .ok none := by
  subst hbl hn
  exact val_lookup_built r hr bits X Y key hlen

theorem push_push_empty {α : Type} (a b : α) : (#[].push a).push b = #[a, b] := rfl

/-- Where the key leaves the edge at `pfx` (the label `L` and the key agree before it and differ
at it), a key `key'` that agrees with the label before `pfx` and at it has the label iff the rest
of it has the rest of the label. -/
theorem split_match_iff (key' L : BitString) (pfx n : Nat) (hn : key'.size = n) (hL : L.size ≤ n)
    (hlt : pfx < L.size)
    (hpre : ∀ i < pfx, key'[i]! = L[i]!) (hat : key'[pfx]! = L[pfx]!) :
    key'.extract 0 L.size = L ↔
      (key'.extract (pfx + 1) key'.size).extract 0 (L.size - pfx - 1) = L.extract (pfx + 1) L.size := by
  rw [bits_ext_iff, bits_ext_iff]
  simp only [Array.size_extract, Nat.min_self]
  constructor
  · rintro ⟨_, h2⟩
    refine ⟨by omega, fun i hi => ?_⟩
    have := h2 (pfx + 1 + i) (by omega)
    rw [bget_extract, if_pos (by omega), Nat.zero_add] at this
    rw [bget_extract, if_pos (by simp; omega), bget_suffix, bget_extract, if_pos (by omega), Nat.zero_add]
    rw [this]
  · rintro ⟨_, h2⟩
    refine ⟨by omega, fun i hi => ?_⟩
    rw [bget_extract, if_pos (by omega), Nat.zero_add]
    rcases Nat.lt_trichotomy i pfx with hlt' | rfl | hgt
    · exact hpre i hlt'
    · exact hat
    · have := h2 (i - (pfx + 1)) (by simp; omega)
      rw [bget_extract, if_pos (by simp; omega), bget_suffix, bget_extract, if_pos (by omega), Nat.zero_add] at this
      rw [show pfx + 1 + (i - (pfx + 1)) = i by omega] at this
      exact this

theorem ite_pair_fst_snd {α : Type} (a b : Bool) (x y : α) :
    (if a = true then (if b = true then (x, y) else (y, x)).2 else (if b = true then (x, y) else (y, x)).1) =
      if a = b then y else x := by
  cases a <;> cases b <;> rfl

/-- The rest of a node after its label (the value of a leaf, the references of a fork) as a cell. -/
theorem payload_size (lbl : DictLabel) (hrp : lbl.remainder.refPos = 0) :
    (lbl.remainder.advanceBits lbl.storedBits).toCellRemaining.bits.size =
        lbl.remainder.bitsRemaining - lbl.storedBits ∧
      (lbl.remainder.advanceBits lbl.storedBits).toCellRemaining.refs = lbl.remainder.cell.refs := by
  simp only [Slice.toCellRemaining, Slice.advanceBits, Cell.mkOrdinary, Array.size_extract, Nat.min_self,
    Slice.bitsRemaining, hrp]
  refine ⟨by omega, extract_all (Nat.le_refl _)⟩

/-- **Get after set.** If the set of the value `vb` for `key` (mode `mode`) succeeds and changes the
dictionary (`ok`), a lookup with the same resolver finds `vb` at `key`, and at every other key of
the same length what it found before (as contents of the values; errors included). -/
theorem val_set (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (vb : Builder) (mode : DictSetMode) :
    ∀ (n : Nat) (root : Option Cell) (key : BitString), key.size = n →
    ∀ (root' : Option Cell) (created : Nat) (loaded : Array Cell),
      dictSetGenAuxWithCells root key (storeB vb) mode r = .ok (root', true, created, loaded) →
      ∀ key' : BitString, key'.size = key.size →
        val (dictLookupWithCells root' key' r) =
          if key' = key then .ok (some vb.finalize) else val (dictLookupWithCells root key' r) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro root key hk root' created loaded h key' hk'
  subst hk
  rw [dictSetGenAuxWithCells.eq_def] at h
  cases root with
  | none =>
    dsimp only at h
    split at h
    · simp [pure, Except.pure] at h
    · dsimp only [pure, Except.pure, bind, Except.bind] at h
      split at h
      · cases h
      rename_i b1 hb1
      split at h
      · cases h
      rename_i b2 hb2
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -, -⟩ := h
      rw [storeBits_ok hb1] at hb2
      rw [appendBuilder_ok hb2, lookup_some, lookup_none]
      simp only [Builder.finalize, Builder.storeBits, Builder.empty, Array.empty_append, val_ok, Option.map_none]
      rw [val_lookup_leaf r hr key key' vb.bits vb.refs hk']
  | some c =>
    dsimp only at h
    cases hp : parseDictLabel c key.size r with
    | error e => rw [hp] at h; cases h
    | ok lbl =>
      rw [hp] at h
      dsimp only [bind, Except.bind] at h
      obtain ⟨c', hrc, hcell, hrp, hlen, hsz, hst⟩ := parseDictLabel_ok hp
      split at h
      · cases h
      rename_i v hv
      obtain ⟨hv1, hv2⟩ := dictValidateNodeExtLe_ok hv
      -- the old lookup
      have hp' : parseDictLabel c key'.size r = .ok lbl := by rw [hk']; exact hp
      have hold : val (dictLookupWithCells (some c) key' r) =
          if key'.extract 0 lbl.len = dictLabelBits lbl then
            (if key'.size = lbl.len then .ok (some (lbl.remainder.advanceBits lbl.storedBits).toCellRemaining)
             else val (dictLookupAuxWithCells (lbl.remainder.cell.refs[if key'[lbl.len]! then 1 else 0]!)
              (key'.extract (lbl.len + 1) key'.size) 0 (key'.extract (lbl.len + 1) key'.size).size r))
          else .ok none := by
        rw [lookup_some, val_lookup_node r c key' lbl hp']
        rw [if_neg]
        rintro ⟨h1, h2⟩
        obtain ⟨e1, e2⟩ := hv2 (by omega)
        rcases h2 with h2 | h2 <;> contradiction
      obtain ⟨hpl, hpre, hdiff⟩ := dictCommonPrefixLen_spec lbl key hlen
      generalize hpfx : dictCommonPrefixLen lbl key = pfx at h hpl hpre hdiff
      split at h
      · -- the key leaves the edge at `pfx`: a new fork, the old edge below it, a new leaf
        rename_i hsplit
        split at h
        · simp [pure, Except.pure] at h
        dsimp only [pure, Except.pure] at h
        rw [hold]
        have hLsz := hsz
        have hpk : pfx < key.size := by omega
        -- the bits of the old label, as the set computes them
        rcases hsb : lbl.sameBit with _ | b0 <;> simp only [hsb] at h
        all_goals first
          | rw [show lbl.remainder.readBits lbl.len = dictLabelBits lbl by simp [dictLabelBits, hsb]] at h
          | rw [show Array.replicate lbl.len b0 = dictLabelBits lbl by simp [dictLabelBits, hsb]] at h
        all_goals
          split at h
          · cases h
          rename_i b1 hb1
          split at h
          · cases h
          rename_i b1' hb1'
          split at h
          · cases h
          rename_i b2 hb2
          split at h
          · cases h
          rename_i b2' hb2'
          split at h
          · cases h
          rename_i bF hbF
          split at h
          · cases h
          rename_i bF1 hbF1
          split at h
          · cases h
          rename_i bF2 hbF2
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -, -, -⟩ := h
          rw [storeBits_ok hb1] at hb1'
          rw [storeBits_ok hb2] at hb2'
          rw [storeBits_ok hbF] at hbF1
          rw [storeRef_ok hbF1] at hbF2
          rw [storeRef_ok hbF2, appendBuilder_ok hb1', appendCell_ok hb2', lookup_some]
          simp only [Builder.finalize, Builder.storeBits, Builder.empty, Array.empty_append, push_push_empty]
          rw [val_lookup_fork r hr _ _ _ key' pfx key.size (by simp; omega) hk' hpk, ite_pair_fst_snd]
          generalize hP : (lbl.remainder.advanceBits lbl.storedBits).toCellRemaining = P
          obtain ⟨hPb, hPr⟩ := payload_size lbl hrp
          rw [hP] at hPb hPr
          by_cases hpe : key'.extract 0 pfx = key.take pfx
          · rw [if_pos hpe]
            have hpre' : ∀ i < pfx, key'[i]! = (dictLabelBits lbl)[i]! := by
              intro i hi
              have := congrArg (·[i]!) hpe
              simp only [bget_extract, Array.take_eq_extract] at this
              rw [if_pos (by simp; omega), if_pos (by simp; omega), Nat.zero_add] at this
              rw [this, hpre i hi]
            by_cases hbit : key'[pfx]! = key[pfx]!
            · -- the new leaf
              rw [if_pos hbit]
              rw [val_lookup_leaf' r hr _ _ _ _ (key.size - pfx - 1) (by bsz) (by bsz)]
              have hkey := key_eq_iff key key' pfx hk' hpk
              rw [Array.take_eq_extract] at hpe
              by_cases hkk : key' = key
              · rw [if_pos (hkey.mp hkk).2.2, if_pos hkk]
              · have hne : key'.extract (pfx + 1) key'.size ≠ key.extract (pfx + 1) key.size := by
                  intro he; exact hkk (hkey.mpr ⟨hpe, hbit, he⟩)
                rw [if_neg hne, if_neg hkk, if_neg]
                intro hm
                apply hdiff hsplit
                have := congrArg (·[pfx]!) hm
                simp only [bget_extract] at this
                rw [if_pos (by simp; omega), Nat.zero_add] at this
                rw [← this, hbit]
            · -- the old edge, below the new fork
              rw [if_neg hbit]
              have hkk : key' ≠ key := by intro h; subst h; exact hbit rfl
              rw [if_neg hkk]
              have hat : key'[pfx]! = (dictLabelBits lbl)[pfx]! := by
                have := hdiff hsplit
                revert hbit this
                cases key'[pfx]! <;> cases key[pfx]! <;> cases (dictLabelBits lbl)[pfx]! <;> simp
              have hiff := split_match_iff key' (dictLabelBits lbl) pfx key.size hk' (by omega) (by omega)
                hpre' hat
              rw [hsz] at hiff
              rw [val_lookup_built' r hr _ _ _ _ (lbl.len - pfx - 1) (key.size - pfx - 1) (by simp; omega)
                (by simp; omega) (by omega)]
              rw [if_neg]
              · by_cases hm : key'.extract 0 lbl.len = dictLabelBits lbl
                · rw [if_pos hm, if_pos (hiff.mp hm)]
                  by_cases hz : key'.size = lbl.len
                  · rw [if_pos hz, if_pos (by omega)]
                    rw [← hP]; rfl
                  · rw [if_neg hz, if_neg (by omega), hPr]
                    have e1 : (key'.extract (pfx + 1) key'.size)[lbl.len - pfx - 1]! = key'[lbl.len]! := by
                      rw [bget_suffix]; congr 1; omega
                    have e2 : (key'.extract (pfx + 1) key'.size).extract (lbl.len - pfx - 1 + 1)
                        (key'.extract (pfx + 1) key'.size).size = key'.extract (lbl.len + 1) key'.size := by
                      rw [extract_suffix_suffix]; congr 1; omega
                    rw [e1, e2]
                · rw [if_neg hm, if_neg (fun h => hm (hiff.mpr h))]
              · rintro ⟨h1, h2⟩
                obtain ⟨e1, e2⟩ := hv2 (by omega)
                rcases h2 with h2 | h2
                · apply h2; rw [hPb, e1, Nat.sub_self]
                · apply h2; rw [hPr]; simp only [Slice.refsRemaining, hrp, Nat.sub_zero] at e2; exact e2
          · rw [if_neg hpe]
            have hkk : key' ≠ key := by intro h; subst h; exact hpe (by rw [Array.take_eq_extract])
            rw [if_neg hkk, if_neg]
            intro hm
            apply hpe
            rw [Array.take_eq_extract]
            apply bits_ext (by simp; omega)
            intro i hi
            simp only [Array.size_extract] at hi
            have := congrArg (·[i]!) hm
            simp only [bget_extract] at this ⊢
            rw [if_pos (by simp; omega), Nat.zero_add] at this
            rw [if_pos (by simp; omega), if_pos (by simp; omega), Nat.zero_add, this, hpre i (by omega)]
      · -- the key follows the whole edge
        rename_i hnsplit
        have hpfxeq : pfx = lbl.len := by omega
        subst hpfxeq
        have hL : dictLabelBits lbl = key.extract 0 lbl.len := by
          apply bits_ext (by simp; omega)
          intro i hi
          rw [hpre i (by omega), bget_extract, if_pos (by simp; omega), Nat.zero_add]
        dsimp only [pure, Except.pure] at h
        split at h
        · -- a leaf: replaced
          rename_i h0
          have hn : key.size = lbl.len := by omega
          split at h
          · simp at h
          split at h
          · cases h
          rename_i b1 hb1
          split at h
          · cases h
          rename_i b2 hb2
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -, -, -⟩ := h
          rw [storeBits_ok hb1] at hb2
          rw [hold, appendBuilder_ok hb2, lookup_some]
          simp only [Builder.finalize, Builder.storeBits, Builder.empty, Array.empty_append]
          rw [val_lookup_leaf r hr key key' vb.bits vb.refs hk', hL,
            if_pos (show key'.size = lbl.len by omega)]
          by_cases hkk : key' = key
          · simp only [hkk, if_true]
          · simp only [hkk, if_false]
            rw [if_neg]
            intro he
            apply hkk
            rw [← hn, ← hk', extract_all (Nat.le_refl _), hk', extract_all (Nat.le_refl _)] at he
            exact he
        · -- a fork: the child of the next bit, then the fork rebuilt
          rename_i h0
          have hlt : lbl.len < key.size := by omega
          have hok := hv2 (by omega)
          have htake : key.take lbl.len = dictLabelBits lbl := by rw [Array.take_eq_extract, hL]
          have hmatch : key.extract 0 lbl.len = dictLabelBits lbl := hL.symm
          have hm : (key.extract (lbl.len + 1) key.size).size < key.size := by simp; omega
          split at h
          · rename_i hb
            split at h
            · cases h
            rename_i res hres
            split at h
            · simp at h
            rename_i hok'
            split at h
            · cases h
            rename_i x hx
            split at h
            · cases h
            rename_i b3 hb3
            split at h
            · cases h
            rename_i b4 hb4
            split at h
            · cases h
            rename_i b5 hb5
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -, -, -⟩ := h
            rw [storeBits_ok hb3] at hb4
            rw [storeRef_ok hb4] at hb5
            rw [storeRef_ok hb5, lookup_some, lookup_some]
            simp only [Builder.finalize, Builder.storeBits, Builder.empty, Array.empty_append, htake]
            have hres' : dictSetGenAuxWithCells (some lbl.remainder.cell.refs[1]!) (key.extract (lbl.len + 1) key.size)
                (storeB vb) mode r = .ok (some x, true, res.2.2.1, res.2.2.2) := by
              rw [hres]; congr 1
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hok'
              rw [← hx, ← hok']
            refine val_rebuilt_fork r hr c lbl key x _ _ hp hlt hok hmatch ?_ ?_ key' hk'
            · simp [hb]
            · intro key'' hk''
              have := ih _ hm _ _ rfl _ _ _ hres' key'' hk''
              rw [lookup_some, lookup_some] at this
              rw [this, hb]
              rfl
          · rename_i hb
            split at h
            · cases h
            rename_i res hres
            split at h
            · simp at h
            rename_i hok'
            split at h
            · cases h
            rename_i x hx
            split at h
            · cases h
            rename_i b3 hb3
            split at h
            · cases h
            rename_i b4 hb4
            split at h
            · cases h
            rename_i b5 hb5
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -, -, -⟩ := h
            rw [storeBits_ok hb3] at hb4
            rw [storeRef_ok hb4] at hb5
            rw [storeRef_ok hb5, lookup_some, lookup_some]
            simp only [Builder.finalize, Builder.storeBits, Builder.empty, Array.empty_append, htake]
            have hres' : dictSetGenAuxWithCells (some lbl.remainder.cell.refs[0]!) (key.extract (lbl.len + 1) key.size)
                (storeB vb) mode r = .ok (some x, true, res.2.2.1, res.2.2.2) := by
              rw [hres]; congr 1
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hok'
              rw [← hx, ← hok']
            refine val_rebuilt_fork r hr c lbl key x _ _ hp hlt hok hmatch ?_ ?_ key' hk'
            · simp [hb]
            · intro key'' hk''
              have := ih _ hm _ _ rfl _ _ _ hres' key'' hk''
              rw [lookup_some, lookup_some] at this
              rw [this, if_neg hb]
              rfl

/-! ## The three forms of the value -/

/-- The value of a slice (`DICTSET`): its remaining bits and references. -/
def sliceB (val : Slice) : Builder := ⟨val.toCellRemaining.bits, val.toCellRemaining.refs⟩

/-- The value of a reference (`DICTSETREF`): no bits and the reference. -/
def refB (c : Cell) : Builder := ⟨#[], #[c]⟩

theorem dictSetSliceWithCells_eq (root : Option Cell) (key : BitString) (val : Slice) (mode : DictSetMode)
    (r : Cell → Except Excno Cell) :
    dictSetSliceWithCells root key val mode r = dictSetGenAuxWithCells root key (storeB (sliceB val)) mode r := by
  simp only [dictSetSliceWithCells]
  rfl

theorem storeRef_eq (c : Cell) : (fun b => builderStoreRefChecked b c) = storeB (refB c) := by
  funext b
  simp only [builderStoreRefChecked, builderAppendBuilderChecked, refB, List.size_toArray, List.length_nil,
    List.length_cons, Nat.zero_add, Array.append_empty]
  congr 2

theorem dictSetRefWithCells_eq (root : Option Cell) (key : BitString) (c : Cell) (mode : DictSetMode)
    (r : Cell → Except Excno Cell) :
    dictSetRefWithCells root key c mode r = dictSetGenAuxWithCells root key (storeB (refB c)) mode r := by
  simp only [dictSetRefWithCells, storeRef_eq]

theorem dictSetBuilderWithCells_eq (root : Option Cell) (key : BitString) (vb : Builder) (mode : DictSetMode)
    (r : Cell → Except Excno Cell) :
    dictSetBuilderWithCells root key vb mode r = dictSetGenAuxWithCells root key (storeB vb) mode r := by
  simp only [dictSetBuilderWithCells]

@[simp] theorem sliceB_finalize (val : Slice) : (sliceB val).finalize = val.toCellRemaining := rfl

end DictMap

end TvmLean

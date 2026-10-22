import TvmLean.Proofs.Exec.Dict.Set

/-!
# A delete on a dictionary, seen through its map

`dictDeleteAuxWithLoads` (C++ `DictionaryFixed::dict_lookup_delete`, dict.cpp:1116) removes the
value of a key: it walks the key from the root; at the leaf of the key the leaf goes; on the way
back a fork whose child lost its leaf merges its edge with the surviving child (the label of the
fork, the bit of the survivor and the survivor's label, then the survivor's value or children), and
a fork whose child changed otherwise is rebuilt with its label. Whatever the shape of the
dictionary, a lookup after it (with the same resolver) finds nothing at the key and what it found
before at every other key of the same length (`val_delete`), and the value removed is the value
the lookup found (`val_delete_old`). A key that is absent leaves the dictionary unchanged
(`delete_none`).
-/

namespace TvmLean

namespace DictMap

/-- The lookup in a dictionary given by an optional root, from its first bit. -/
def lookupOpt (r : Cell → Except Excno Cell) : Option Cell → BitString → Except Excno (Option Slice × Array Cell)
  | none, _ => .ok (none, #[])
  | some c, key => dictLookupAuxWithCells c key 0 key.size r

theorem lookupOpt_eq (r : Cell → Except Excno Cell) (root : Option Cell) (key : BitString) :
    lookupOpt r root key = dictLookupWithCells root key r := by
  cases root <;> rfl

theorem withLoads_ok {α : Type} {l : Array Cell} {x : Except Excno α} {a : α} (h : withLoads l x = .ok a) :
    x = .ok a := by
  cases x <;> simp_all [withLoads, Except.mapError]

theorem underCell_ok {α : Type} {c : Cell} {x : Except (Excno × Array Cell) α} {a : α}
    (h : underCell c x = .ok a) : x = .ok a := by
  cases x <;> simp_all [underCell, Except.mapError]

theorem ite_refs (a : Array Cell) (b : Bool) :
    (if b = true then a[1]! else a[0]!) = a[if b = true then 1 else 0]! := by
  cases b <;> rfl

theorem ite_refs' (a : Array Cell) (b : Bool) :
    (if b = true then a[0]! else a[1]!) = a[if (!b) = true then 1 else 0]! := by
  cases b <;> rfl

/-- A key has the label `L ++ #[b] ++ L2` iff it has `L`, then `b`, then `L2` after it. -/
theorem extract_three_iff (key L L2 : BitString) (b : Bool) (len len2 : Nat) (hL : L.size = len)
    (hL2 : L2.size = len2) (hk : len + 1 + len2 ≤ key.size) :
    key.extract 0 (len + 1 + len2) = L ++ #[b] ++ L2 ↔
      key.extract 0 len = L ∧ key[len]! = b ∧ (key.extract (len + 1) key.size).extract 0 len2 = L2 := by
  subst hL hL2
  constructor
  · intro h
    have hget : ∀ i : Nat, (key.extract 0 (L.size + 1 + L2.size))[i]! = (L ++ #[b] ++ L2)[i]! :=
      fun i => by rw [h]
    refine ⟨?_, ?_, ?_⟩
    · apply bits_ext (by simp; omega)
      intro i hi
      simp only [Array.size_extract] at hi
      have := hget i
      rw [bget_extract, if_pos (by omega), bget_append_left (by simp; omega), bget_append_left (by omega)] at this
      rw [bget_extract, if_pos (by omega), this]
    · have := hget L.size
      rw [bget_extract, if_pos (by omega), bget_append_left (by simp), bget_append_right (by simp),
        Nat.sub_self, Nat.zero_add] at this
      rw [this]; rfl
    · apply bits_ext (by simp; omega)
      intro i hi
      simp only [Array.size_extract] at hi
      have := hget (L.size + 1 + i)
      rw [bget_extract, if_pos (by omega), bget_append_right (by simp)] at this
      simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil] at this
      rw [show L.size + 1 + i - (L.size + (0 + 1)) = i by omega, Nat.zero_add] at this
      rw [bget_extract, if_pos (by simp; omega), bget_suffix, Nat.zero_add, this]
  · rintro ⟨h1, h2, h3⟩
    apply bits_ext (by simp; omega)
    intro i hi
    simp only [Array.size_extract] at hi
    rw [bget_extract, if_pos (by omega), Nat.zero_add]
    rcases Nat.lt_or_ge i L.size with hlt | hge
    · rw [bget_append_left (by simp; omega), bget_append_left hlt, ← h1, bget_extract, if_pos (by omega),
        Nat.zero_add]
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · subst heq
        rw [bget_append_left (by simp), bget_append_right (by simp), Nat.sub_self, h2]; rfl
      · rw [bget_append_right (by simp; omega)]
        simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [← h3, bget_extract, if_pos (by simp; omega), bget_suffix]
        congr 1; omega

/-- **A fork merged with its surviving child.** At a fork whose child on the side of `k` lost the
last key of `k`'s rest (`hgone`: it holds no other key), the merged edge (the fork's label, the
survivor's bit and label, then the survivor's value or children, C++ `dict_lookup_delete`) is the
old fork without `k`. -/
theorem val_merged (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (c : Cell) (lbl lbl2 : DictLabel)
    (k : BitString) (hp : parseDictLabel c k.size r = .ok lbl) (hlt : lbl.len < k.size)
    (hok : lbl.remainder.bitsRemaining = lbl.storedBits ∧ lbl.remainder.refsRemaining = 2)
    (hmatch : k.extract 0 lbl.len = dictLabelBits lbl)
    (hp2 : parseDictLabel (lbl.remainder.cell.refs[if (!k[lbl.len]!) = true then 1 else 0]!)
      (k.size - lbl.len - 1) r = .ok lbl2)
    (hok2 : k.size - lbl.len - 1 - lbl2.len > 0 →
      lbl2.remainder.bitsRemaining = lbl2.storedBits ∧ lbl2.remainder.refsRemaining = 2)
    (hgone : ∀ key'' : BitString, key''.size = k.size - lbl.len - 1 → key'' ≠ k.extract (lbl.len + 1) k.size →
      val (dictLookupAuxWithCells (lbl.remainder.cell.refs[if k[lbl.len]! then 1 else 0]!) key'' 0 key''.size r) =
        .ok none)
    (key' : BitString) (hk' : key'.size = k.size) :
    val (dictLookupAuxWithCells (Cell.mkOrdinary
        (dictLabelEncode (dictLabelBits lbl ++ #[!k[lbl.len]!] ++ dictLabelBits lbl2) (lbl.len + 1 + lbl2.len) k.size ++
          (lbl2.remainder.advanceBits lbl2.storedBits).toCellRemaining.bits)
        (lbl2.remainder.advanceBits lbl2.storedBits).toCellRemaining.refs) key' 0 key'.size r) =
      if key' = k then .ok none else val (dictLookupAuxWithCells c key' 0 key'.size r) := by
  obtain ⟨_, _, _, _, hlen, hsz, _⟩ := parseDictLabel_ok hp
  obtain ⟨_, _, _, hrp2, hlen2, hsz2, _⟩ := parseDictLabel_ok hp2
  generalize hP : (lbl2.remainder.advanceBits lbl2.storedBits).toCellRemaining = P
  obtain ⟨hPb, hPr⟩ := payload_size lbl2 hrp2
  rw [hP] at hPb hPr
  have hcomb : (dictLabelBits lbl ++ #[!k[lbl.len]!] ++ dictLabelBits lbl2).size = lbl.len + 1 + lbl2.len := by
    simp [hsz, hsz2]
  rw [val_lookup_built' r hr _ _ _ key' _ k.size hcomb hk' (by omega)]
  have hnobad : ¬ (k.size - (lbl.len + 1 + lbl2.len) > 0 ∧ (P.bits.size ≠ 0 ∨ P.refs.size ≠ 2)) := by
    rintro ⟨h1, h2⟩
    obtain ⟨e1, e2⟩ := hok2 (by omega)
    rcases h2 with h2 | h2
    · apply h2; rw [hPb, e1, Nat.sub_self]
    · apply h2; rw [hPr]; simp only [Slice.refsRemaining, hrp2, Nat.sub_zero] at e2; exact e2
  rw [if_neg hnobad]
  have hp' : parseDictLabel c key'.size r = .ok lbl := by rw [hk']; exact hp
  have hnb : ¬ (key'.size - lbl.len > 0 ∧
      (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)) := by
    simp only [ne_eq, hok, not_true_eq_false, or_self, and_false, not_false_eq_true]
  rw [val_lookup_node r c key' lbl hp', if_neg hnb]
  have hne : ¬ key'.size = lbl.len := by omega
  simp only [hne, if_false]
  have h3 := extract_three_iff key' (dictLabelBits lbl) (dictLabelBits lbl2) (!k[lbl.len]!) lbl.len lbl2.len hsz
    hsz2 (by omega)
  have hkey := key_eq_iff k key' lbl.len hk' hlt
  rw [hmatch] at hkey
  by_cases hm : key'.extract 0 lbl.len = dictLabelBits lbl
  · rw [if_pos hm]
    by_cases hb : key'[lbl.len]! = k[lbl.len]!
    · -- the side of `k`: nothing left but `k`'s rest, which is gone
      rw [if_neg (fun h => by
        have := (h3.mp h).2.1
        rw [hb] at this
        cases k[lbl.len]! <;> simp at this)]
      by_cases hkk : key' = k
      · rw [if_pos hkk]
      · rw [if_neg hkk, hb]
        rw [hgone _ (by simp; omega) (fun he => hkk (hkey.mpr ⟨hm, hb, he⟩))]
    · -- the side of the survivor
      have hb' : key'[lbl.len]! = !k[lbl.len]! := by
        revert hb; cases key'[lbl.len]! <;> cases k[lbl.len]! <;> simp
      have hkk : key' ≠ k := fun h => hb (h ▸ rfl)
      rw [if_neg hkk, hb']
      have hp2' : parseDictLabel (lbl.remainder.cell.refs[if (!k[lbl.len]!) = true then 1 else 0]!)
          (key'.extract (lbl.len + 1) key'.size).size r = .ok lbl2 := by
        rw [show (key'.extract (lbl.len + 1) key'.size).size = k.size - lbl.len - 1 by simp; omega]; exact hp2
      have hnobad2 : ¬ ((key'.extract (lbl.len + 1) key'.size).size - lbl2.len > 0 ∧
          (lbl2.remainder.bitsRemaining ≠ lbl2.storedBits ∨ lbl2.remainder.refsRemaining ≠ 2)) := by
        rintro ⟨h1, h2⟩
        obtain ⟨e1, e2⟩ := hok2 (by simp at h1; omega)
        rcases h2 with h2 | h2 <;> contradiction
      rw [val_lookup_node r _ _ lbl2 hp2', if_neg hnobad2]
      by_cases hm2 : (key'.extract (lbl.len + 1) key'.size).extract 0 lbl2.len = dictLabelBits lbl2
      · rw [if_pos (h3.mpr ⟨hm, hb', hm2⟩), if_pos hm2]
        by_cases hz : k.size = lbl.len + 1 + lbl2.len
        · have hz' : (key'.extract (lbl.len + 1) key'.size).size = lbl2.len := by simp; omega
          rw [if_pos hz, if_pos hz', ← hP]; rfl
        · have hz' : ¬ (key'.extract (lbl.len + 1) key'.size).size = lbl2.len := by simp; omega
          rw [if_neg hz, if_neg hz', hPr]
          have e1 : key'[lbl.len + 1 + lbl2.len]! = (key'.extract (lbl.len + 1) key'.size)[lbl2.len]! := by
            rw [bget_suffix]
          have e2 : key'.extract (lbl.len + 1 + lbl2.len + 1) key'.size =
              (key'.extract (lbl.len + 1) key'.size).extract (lbl2.len + 1)
                (key'.extract (lbl.len + 1) key'.size).size := by
            rw [extract_suffix_suffix, show lbl.len + 1 + (lbl2.len + 1) = lbl.len + 1 + lbl2.len + 1 by omega]
          rw [e1, e2]
      · rw [if_neg (fun h => hm2 (h3.mp h).2.2), if_neg hm2]
  · rw [if_neg hm, if_neg (fun h => hm (h3.mp h).1)]
    have hkk : key' ≠ k := fun h => hm (h ▸ hmatch)
    rw [if_neg hkk]

theorem val_delete (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) :
    ∀ (rem : Nat) (cell : Cell) (key : BitString) (pos : Nat), key.size = pos + rem →
    ∀ (oldV : Slice) (newCell : Option Cell) (created : Nat) (loaded : Array Cell),
      dictDeleteAuxWithLoads cell key pos rem r = .ok (some oldV, newCell, created, loaded) →
      val (dictLookupAuxWithCells cell (key.extract pos key.size) 0 rem r) = .ok (some oldV.toCellRemaining) ∧
      ∀ key' : BitString, key'.size = rem →
        val (lookupOpt r newCell key') =
          if key' = key.extract pos key.size then .ok none
          else val (dictLookupAuxWithCells cell key' 0 key'.size r) := by
  intro rem
  induction rem using Nat.strongRecOn with
  | _ rem ih =>
  intro cell key pos hks oldV newCell created loaded h
  rw [dictDeleteAuxWithLoads] at h
  dsimp only [bind, Except.bind] at h
  -- the rest of the key from `pos`
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
  split at h
  · simp [pure, Except.pure] at h
  rename_i hmatch0
  have hmatchB : dictLabelMatches lbl key pos = true := by simpa using hmatch0
  rw [dictLabelMatches_shift lbl key pos (by omega)] at hmatchB
  have hmatch := ((dictLabelMatches_iff lbl _ 0 hsz).mp hmatchB).2
  simp only [Nat.zero_add] at hmatch
  dsimp only [pure, Except.pure] at h
  have hnb : ∀ n : Nat, n = rem → ¬ (n - lbl.len > 0 ∧
      (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)) := by
    rintro n rfl ⟨h1, h2⟩
    obtain ⟨e1, e2⟩ := hv2 h1
    rcases h2 with h2 | h2 <;> contradiction
  split at h
  · -- the leaf of the key: removed
    rename_i h0
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl, -, -⟩ := h
    have hn : rem = lbl.len := by omega
    refine ⟨?_, ?_⟩
    · rw [← hksz, val_lookup_node r cell _ lbl hpk, if_neg (hnb _ hksz), if_pos hmatch,
        if_pos (show (key.extract pos key.size).size = lbl.len by omega)]
    · intro key' hk'
      simp only [lookupOpt, val_ok, Option.map_none]
      by_cases hkk : key' = key.extract pos key.size
      · rw [if_pos hkk]
      · have hp' : parseDictLabel cell key'.size r = .ok lbl := by rw [hk']; exact hp
        rw [if_neg hkk, val_lookup_node r cell key' lbl hp', if_neg (hnb _ hk'), if_neg]
        intro hm
        apply hkk
        rw [show lbl.len = key'.size by omega, extract_all (Nat.le_refl _)] at hm
        rw [hm, ← hmatch, show lbl.len = (key.extract pos key.size).size by omega, extract_all (Nat.le_refl _)]
  · -- a fork: the child of the next bit
    rename_i h0
    have hlt : lbl.len < rem := by omega
    split at h
    · cases h
    rename_i res hres
    have hres' := underCell_ok hres
    split at h
    · simp at h
    rename_i oldVal hov
    have hres'' : dictDeleteAuxWithLoads (if key[pos + lbl.len]! = true then lbl.remainder.cell.refs[1]!
        else lbl.remainder.cell.refs[0]!) key (pos + lbl.len + 1) (v.val - 1) r =
        .ok (some oldVal, res.2.1, res.2.2.1, res.2.2.2) := by
      rw [hres', ← hov]
    obtain ⟨ih1, ih2⟩ := ih (v.val - 1) (by omega) _ key (pos + lbl.len + 1) (by omega) oldVal res.2.1
      res.2.2.1 res.2.2.2 hres''
    rw [ite_refs] at ih1 ih2
    have hbit : (key.extract pos key.size)[lbl.len]! = key[pos + lbl.len]! := bget_suffix _ _ _
    have hrest : (key.extract pos key.size).extract (lbl.len + 1) (key.extract pos key.size).size =
        key.extract (pos + lbl.len + 1) key.size := by
      rw [extract_suffix_suffix, Nat.add_assoc]
    have hrsz : (key.extract (pos + lbl.len + 1) key.size).size = v.val - 1 := by simp; omega
    -- the old value: found through the child
    have hold : val (dictLookupAuxWithCells cell (key.extract pos key.size) 0 rem r) =
        .ok (some oldVal.toCellRemaining) := by
      rw [← hksz, val_lookup_node r cell _ lbl hpk, if_neg (hnb _ hksz), if_pos hmatch,
        if_neg (show ¬ (key.extract pos key.size).size = lbl.len by omega), hbit, hrest, hrsz]
      exact ih1
    split at h
    · -- the child kept a root: the fork rebuilt with it
      rename_i x hx
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, -, -⟩ := h
      refine ⟨hold, fun key' hk' => ?_⟩
      simp only [lookupOpt]
      rw [hx] at ih2
      have := val_rebuilt_fork r hr cell lbl (key.extract pos key.size) x (.ok none)
        (if key[pos + lbl.len]! = true then #[lbl.remainder.cell.refs[0]!, x] else #[x, lbl.remainder.cell.refs[1]!])
        hpk (by omega) (hv2 (by omega)) hmatch (by rw [hbit]) ?_ key' (by omega)
      · rw [hksz] at this
        exact this
      · intro key'' hk''
        rw [hrest] at hk'' ⊢
        rw [hbit, ← ih2 key'' (by omega)]
        rfl
    · -- the child lost its last key: the fork merged with the survivor
      rename_i hx
      split at h
      · cases h
      rename_i lbl2 hpl2
      have hp2 := withLoads_ok hpl2
      split at h
      · cases h
      rename_i u hvl2
      have hv2' := withLoads_ok hvl2
      rw [dictValidateNodeExt_eq] at hv2'
      have hok2 : v.val - 1 - lbl2.len > 0 →
          lbl2.remainder.bitsRemaining = lbl2.storedBits ∧ lbl2.remainder.refsRemaining = 2 := by
        intro hpos
        split at hv2'
        · cases hv2'
        · rename_i hgood
          simp only [not_and, not_or, Decidable.not_not] at hgood
          exact hgood hpos
      split at h
      · cases h
      rename_i b6 hb6
      split at h
      · cases h
      rename_i b7 hb7
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, -, -⟩ := h
      refine ⟨hold, fun key' hk' => ?_⟩
      rw [storeBits_ok (withLoads_ok hb6)] at hb7
      rw [appendCell_ok (withLoads_ok hb7)]
      simp only [lookupOpt, Builder.finalize, Builder.storeBits, Builder.empty, Array.empty_append]
      rw [hx] at ih2
      have hgone : ∀ key'' : BitString, key''.size = (key.extract pos key.size).size - lbl.len - 1 →
          key'' ≠ (key.extract pos key.size).extract (lbl.len + 1) (key.extract pos key.size).size →
          val (dictLookupAuxWithCells
            (lbl.remainder.cell.refs[if (key.extract pos key.size)[lbl.len]! then 1 else 0]!) key'' 0
              key''.size r) = .ok none := by
        intro key'' hk'' hne
        rw [hrest] at hne
        have := ih2 key'' (by omega)
        rw [if_neg hne] at this
        rw [hbit, ← this]
        rfl
      have hp2' : parseDictLabel (lbl.remainder.cell.refs[if (!(key.extract pos key.size)[lbl.len]!) = true then 1 else 0]!)
          ((key.extract pos key.size).size - lbl.len - 1) r = .ok lbl2 := by
        rw [hbit, ← ite_refs', show (key.extract pos key.size).size - lbl.len - 1 = v.val - 1 by omega]
        exact hp2
      have := val_merged r hr cell lbl lbl2 (key.extract pos key.size) hpk (by omega) (hv2 (by omega)) hmatch
        hp2' (by intro hpos; exact hok2 (by omega)) hgone key' (by omega)
      rw [hksz, hbit] at this
      exact this

/-- **A key that is absent leaves the dictionary unchanged** (the root itself is returned). -/
theorem delete_none (r : Cell → Except Excno Cell) (cell : Cell) (key : BitString) (pos rem : Nat)
    (newCell : Option Cell) (created : Nat) (loaded : Array Cell)
    (h : dictDeleteAuxWithLoads cell key pos rem r = .ok (none, newCell, created, loaded)) :
    newCell = some cell := by
  rw [dictDeleteAuxWithLoads] at h
  dsimp only [bind, Except.bind] at h
  repeat' (first | (cases h; done) | (simp [pure, Except.pure] at h; done) | split at h)
  all_goals (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h)
  all_goals first | exact h.2.1.symm | (simp at h)

/-- **Get after delete**, from the root: if the delete of `key` removed a value `oldV`, it was
the value of `key`, and a lookup (with the same resolver) finds nothing at `key` and what it found
before at every other key of the same length. -/
theorem val_deleteWithLoads (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (root : Option Cell)
    (key : BitString) (oldV : Slice) (newRoot : Option Cell) (created : Nat) (loaded : Array Cell)
    (h : dictDeleteWithLoads root key r = .ok (some oldV, newRoot, created, loaded)) :
    val (dictLookupWithCells root key r) = .ok (some oldV.toCellRemaining) ∧
    ∀ key' : BitString, key'.size = key.size →
      val (dictLookupWithCells newRoot key' r) =
        if key' = key then .ok none else val (dictLookupWithCells root key' r) := by
  cases root with
  | none => simp [dictDeleteWithLoads, pure, Except.pure] at h
  | some c =>
    simp only [dictDeleteWithLoads] at h
    obtain ⟨h1, h2⟩ := val_delete r hr key.size c key 0 (by simp) oldV newRoot created loaded h
    rw [extract_all (Nat.le_refl _)] at h1 h2
    refine ⟨h1, fun key' hk' => ?_⟩
    rw [← lookupOpt_eq, h2 key' hk']
    rfl

/-- A delete of an absent key returns the dictionary unchanged. -/
theorem deleteWithLoads_none (r : Cell → Except Excno Cell) (root : Option Cell) (key : BitString)
    (newRoot : Option Cell) (created : Nat) (loaded : Array Cell)
    (h : dictDeleteWithLoads root key r = .ok (none, newRoot, created, loaded)) : newRoot = root := by
  cases root with
  | none => simp [dictDeleteWithLoads, pure, Except.pure] at h; exact h.1.symm
  | some c =>
    simp only [dictDeleteWithLoads] at h
    exact delete_none r c key 0 key.size newRoot created loaded h

end DictMap

end TvmLean

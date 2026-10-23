import TvmLean.Proofs.Exec.Dict.Map

/-!
# Dictionaries as maps: the nearest key, the least and the greatest

The walks of `DICT*GETNEXT*`, `DICT*GETPREV*` (`dictNearestWithCells`, C++
`DictionaryFixed::lookup_nearest_key`, dict.cpp) and of `DICT*MIN*`, `DICT*MAX*`, `DICT*REMMIN*`,
... (`dictMinMaxWithCells`, C++ `DictionaryFixed::get_minmax_key`) said as the map of the
dictionary (`Dict.value`, `Proofs/Exec/Dict/Map.lean`):

* the order of keys a walk follows (`Dict.KeyLt fb rb`): at the first bit where two keys differ, the
  later one has the bit `Dict.laterBit fb rb i` (`rb` but at the first bit of the key, `fb`: the sign
  bit of a signed key, which C++ inverts);
* `Dict.minMax_spec`: a min/max walk that ends finds a key of the map, and no key of the map comes
  after it;
* `Dict.nearest_spec`: a nearest walk that ends finds the first key of the map after the hint (or
  the hint itself, `allowEq`), or finds nothing and no key of the map comes after the hint.

Both on any dictionary, with the resolver of the walk (`Dict.valueWith`: the map as lookups with
that resolver read it); on a well-formed dictionary (`Dict.WF`) and the resolver of the VM, the map
is `Dict.value` (`Dict.valueWith_eq_value`, and `Dict.nearest_value`, `Dict.minMax_value`).
For integer keys the order is the order of the integers: `Dict.keyLt_natToBits` (unsigned keys,
`natToBits`, the bits `true true` of `DICTU*GETNEXT`), `Dict.keyLt_intBits` (signed keys,
`dictKeyBits?`, the bits `false true` of `DICTI*GETNEXT`: the sign bit inverted).
-/

namespace TvmLean

/-- The bit the later of two keys has at the first bit `i` where they differ, in the order of a
walk with the bits `fb` (the first bit of the key) and `rb` (every other bit). -/
def Dict.laterBit (fb rb : Bool) (i : Nat) : Bool := if i = 0 then fb else rb

/-- `a` comes before `b` in the order of a walk with the bits `fb`, `rb`, the keys starting at the
bit `pos` of the whole key: they agree before some bit `i`, where `b` has the later bit and `a` not. -/
def Dict.KeyLt (fb rb : Bool) (pos : Nat) (a b : BitString) : Prop :=
  ∃ i, i < a.size ∧ i < b.size ∧ (∀ j < i, a[j]! = b[j]!) ∧
    b[i]! = Dict.laterBit fb rb (pos + i) ∧ a[i]! ≠ Dict.laterBit fb rb (pos + i)

/-- `b` comes after `a`, or is `a` when `allowEq`. -/
def Dict.KeyAfter (fb rb : Bool) (pos : Nat) (allowEq : Bool) (a b : BitString) : Prop :=
  Dict.KeyLt fb rb pos a b ∨ (allowEq = true ∧ b = a)

/-- The map of the dictionary `root` as the lookups with the resolver `res` read it: the contents of
the value of `key` (`none` if absent or if the lookup fails). With the default resolver it is
`Dict.value` (`Dict.valueWith_rejectSpecial`). -/
def Dict.valueWith (res : Cell → Except Excno Cell) (root : Option Cell) (key : BitString) : Option Cell :=
  match DictMap.val (dictLookupWithCells root key res) with
  | .ok w => w
  | .error _ => none

theorem Dict.valueWith_rejectSpecial (root : Option Cell) (key : BitString) :
    Dict.valueWith Cell.rejectSpecial root key = Dict.value root key := by
  unfold Dict.valueWith Dict.value Dict.get
  cases dictLookupWithCells root key with
  | error e => rfl
  | ok x => rfl

/-- On a well-formed dictionary, the map read with a resolver that loads ordinary cells as themselves
(the VM's, `resolvesOrdinary_library`) is `Dict.value`. -/
theorem Dict.valueWith_eq_value {res : Cell → Except Excno Cell} (hr : ResolvesOrdinary res)
    {root : Option Cell} {n : Nat} (hwf : Dict.WF root n) {key : BitString} (hk : key.size = n) :
    Dict.valueWith res root key = Dict.value root key := by
  obtain ⟨x, hx⟩ := hwf key hk
  rw [← Dict.valueWith_rejectSpecial]
  unfold Dict.valueWith
  rw [dictLookupWithCells_of_rejectSpecial res hr root key x hx, hx]

namespace DictNear

open DictMap

/-! ## The order of keys -/

theorem bool_ne_iff (x y : Bool) : x ≠ y ↔ x = !y := by cases x <;> cases y <;> decide

theorem bool_ne_not (y : Bool) : y ≠ !y := by cases y <;> decide

theorem laterBit_not (fb rb : Bool) (i : Nat) :
    Dict.laterBit (!fb) (!rb) i = !Dict.laterBit fb rb i := by
  unfold Dict.laterBit; split <;> rfl

/-- The order of the walk with the other bits is the reverse order. -/
theorem keyLt_flip {fb rb : Bool} {pos : Nat} {a b : BitString} :
    Dict.KeyLt fb rb pos a b ↔ Dict.KeyLt (!fb) (!rb) pos b a := by
  unfold Dict.KeyLt
  simp only [laterBit_not]
  constructor
  · rintro ⟨i, h1, h2, h3, h4, h5⟩
    refine ⟨i, h2, h1, fun j hj => (h3 j hj).symm, (bool_ne_iff _ _).mp h5, ?_⟩
    rw [h4]; exact bool_ne_not _
  · rintro ⟨i, h1, h2, h3, h4, h5⟩
    refine ⟨i, h2, h1, fun j hj => (h3 j hj).symm, ?_, ?_⟩
    · have := (bool_ne_iff _ _).mp h5; rw [Bool.not_not] at this; exact this
    · rw [h4]; exact (bool_ne_not _).symm

/-- Keys that agree before the bit `m` and differ at it: the later is the one with the later bit. -/
theorem keyLt_at {fb rb : Bool} {pos m : Nat} {a b : BitString} (ha : m < a.size) (hb : m < b.size)
    (hpre : ∀ j < m, a[j]! = b[j]!) (hm : a[m]! ≠ b[m]!) :
    Dict.KeyLt fb rb pos a b ↔ b[m]! = Dict.laterBit fb rb (pos + m) := by
  constructor
  · rintro ⟨i, _, _, h3, h4, h5⟩
    rcases Nat.lt_trichotomy i m with hlt | rfl | hgt
    · exact absurd ((hpre i hlt).trans h4) h5
    · exact h4
    · exact absurd (h3 m hgt) hm
  · intro h
    refine ⟨m, ha, hb, hpre, h, ?_⟩
    rw [← h]; exact hm

theorem keyLt_asymm {fb rb : Bool} {pos : Nat} {a b : BitString} (h : Dict.KeyLt fb rb pos a b) :
    ¬ Dict.KeyLt fb rb pos b a := by
  obtain ⟨i, h1, h2, h3, h4, h5⟩ := h
  intro h'
  have hne : b[i]! ≠ a[i]! := by rw [h4]; exact fun e => h5 e.symm
  rw [keyLt_at h2 h1 (fun j hj => (h3 j hj).symm) hne] at h'
  exact h5 h'

theorem keyLt_irrefl {fb rb : Bool} {pos : Nat} {a : BitString} : ¬ Dict.KeyLt fb rb pos a a := by
  rintro ⟨i, _, _, _, h4, h5⟩
  exact h5 h4

theorem keyAfter_not_lt {fb rb : Bool} {pos : Nat} {allowEq : Bool} {a b : BitString}
    (h : Dict.KeyAfter fb rb pos allowEq a b) : ¬ Dict.KeyLt fb rb pos b a := by
  rcases h with h | ⟨_, rfl⟩
  · exact keyLt_asymm h
  · exact keyLt_irrefl

/-- A key between two keys that agree before the bit `m` agrees with them before `m`. -/
theorem keyLt_between {fb rb : Bool} {pos m : Nat} {a b c : BitString} (hmc : m ≤ c.size)
    (hac : ∀ j < m, a[j]! = c[j]!) (hab : Dict.KeyLt fb rb pos a b) (hbc : Dict.KeyLt fb rb pos b c) :
    ∀ j < m, b[j]! = a[j]! := by
  obtain ⟨i, _, h2, h3, h4, h5⟩ := hab
  rcases Nat.lt_or_ge i m with him | him
  · exfalso
    have hbc' : ∀ j < i, b[j]! = c[j]! := fun j hj => (h3 j hj).symm.trans (hac j (by omega))
    have hne : b[i]! ≠ c[i]! := by rw [h4, ← hac i him]; exact fun e => h5 e.symm
    have hci := (keyLt_at h2 (by omega) hbc' hne).mp hbc
    exact h5 ((hac i him).trans hci)
  · intro j hj; exact (h3 j (by omega)).symm

theorem keyAfter_between {fb rb : Bool} {pos m : Nat} {allowEq : Bool} {a b c : BitString}
    (hmc : m ≤ c.size) (hac : ∀ j < m, a[j]! = c[j]!) (hab : Dict.KeyAfter fb rb pos allowEq a b)
    (hbc : Dict.KeyLt fb rb pos b c) : ∀ j < m, b[j]! = a[j]! := by
  rcases hab with hab | ⟨_, rfl⟩
  · exact keyLt_between hmc hac hab hbc
  · intro j _; rfl

/-- Keys that agree before the bit `m` are in the order of their rests from `m`. -/
theorem keyLt_suffix {fb rb : Bool} {pos m : Nat} {a b : BitString} (ha : m ≤ a.size) (hb : m ≤ b.size)
    (hpre : ∀ j < m, a[j]! = b[j]!) :
    Dict.KeyLt fb rb pos a b ↔
      Dict.KeyLt fb rb (pos + m) (a.extract m a.size) (b.extract m b.size) := by
  constructor
  · rintro ⟨i, h1, h2, h3, h4, h5⟩
    have him : m ≤ i := by
      rcases Nat.lt_or_ge i m with hlt | hge
      · exact absurd ((hpre i hlt).trans h4) h5
      · exact hge
    refine ⟨i - m, by simp only [Array.size_extract, Nat.min_self]; omega,
      by simp only [Array.size_extract, Nat.min_self]; omega, fun j hj => ?_, ?_, ?_⟩
    · rw [bget_suffix, bget_suffix]; exact h3 _ (by omega)
    · rw [bget_suffix, show m + (i - m) = i by omega, show pos + m + (i - m) = pos + i by omega]
      exact h4
    · rw [bget_suffix, show m + (i - m) = i by omega, show pos + m + (i - m) = pos + i by omega]
      exact h5
  · rintro ⟨i, h1, h2, h3, h4, h5⟩
    simp only [Array.size_extract, Nat.min_self] at h1 h2
    rw [bget_suffix, show pos + m + i = pos + (m + i) by omega] at h4 h5
    refine ⟨m + i, by omega, by omega, fun j hj => ?_, h4, h5⟩
    rcases Nat.lt_or_ge j m with hjm | hjm
    · exact hpre j hjm
    · have := h3 (j - m) (by omega)
      rw [bget_suffix, bget_suffix, show m + (j - m) = j by omega] at this
      exact this

theorem keyAfter_suffix {fb rb : Bool} {pos m : Nat} {allowEq : Bool} {a b : BitString}
    (ha : m ≤ a.size) (hab : a.size = b.size) (hpre : ∀ j < m, a[j]! = b[j]!) :
    Dict.KeyAfter fb rb pos allowEq a b ↔
      Dict.KeyAfter fb rb (pos + m) allowEq (a.extract m a.size) (b.extract m b.size) := by
  unfold Dict.KeyAfter
  rw [keyLt_suffix ha (by omega) hpre]
  constructor
  · rintro (h | ⟨he, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨he, rfl⟩
  · rintro (h | ⟨he, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨he, ?_⟩
      apply bits_ext hab.symm
      intro i hi
      rcases Nat.lt_or_ge i m with him | him
      · exact (hpre i him).symm
      · have := congrArg (fun x : BitString => x[i - m]!) h
        simp only [bget_suffix, show m + (i - m) = i by omega] at this
        exact this

/-! ## Lookups from a node -/

/-- The lookup of `k` from the node `c` (the key relative to the node), as the map reads it. -/
abbrev look (res : Cell → Except Excno Cell) (c : Cell) (k : BitString) : Except Excno (Option Cell) :=
  val (dictLookupAuxWithCells c k 0 k.size res)

/-- The lookup of `k` from `c` finds no value (the key is absent, or the lookup fails). -/
def NoVal (res : Cell → Except Excno Cell) (c : Cell) (k : BitString) : Prop :=
  ∀ w, look res c k ≠ .ok (some w)

/-- The check of a node that holds (C++ `LabelParser::validate_ext`). -/
def Good (lbl : DictLabel) (n : Nat) : Prop :=
  ¬ (n - lbl.len > 0 ∧ (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2))

theorem extract_eq_label {k : BitString} {lbl : DictLabel} (hsz : (dictLabelBits lbl).size = lbl.len)
    (hlen : lbl.len ≤ k.size) :
    k.extract 0 lbl.len = dictLabelBits lbl ↔ ∀ j < lbl.len, k[j]! = (dictLabelBits lbl)[j]! := by
  rw [bits_ext_iff]
  simp only [Array.size_extract, hsz]
  constructor
  · rintro ⟨_, h⟩ j hj
    have := h j (by omega)
    rw [bget_extract, if_pos (by omega), Nat.zero_add] at this
    exact this
  · intro h
    refine ⟨by omega, fun j hj => ?_⟩
    rw [bget_extract, if_pos (by omega), Nat.zero_add]
    exact h j (by omega)

/-- A key that leaves the label of the node has no value. -/
theorem noVal_of_bit {res : Cell → Except Excno Cell} {c : Cell} {k : BitString} {lbl : DictLabel}
    (hp : parseDictLabel c k.size res = .ok lbl) {j : Nat} (hj : j < lbl.len)
    (hne : k[j]! ≠ (dictLabelBits lbl)[j]!) : NoVal res c k := by
  obtain ⟨_, _, _, _, hlen, hsz, _⟩ := parseDictLabel_ok hp
  intro w hw
  unfold look at hw
  rw [val_lookup_node res c k lbl hp] at hw
  have hmis : ¬ k.extract 0 lbl.len = dictLabelBits lbl := by
    rw [extract_eq_label hsz hlen]
    intro h; exact hne (h j hj)
  by_cases hb : k.size - lbl.len > 0 ∧
      (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)
  · rw [if_pos hb] at hw; cases hw
  · rw [if_neg hb, if_neg hmis] at hw; cases hw

/-- The value of a leaf whose label is the key. -/
theorem look_leaf {res : Cell → Except Excno Cell} {c : Cell} {k : BitString} {lbl : DictLabel}
    (hp : parseDictLabel c k.size res = .ok lbl) (hpre : ∀ j < lbl.len, k[j]! = (dictLabelBits lbl)[j]!)
    (hz : k.size = lbl.len) :
    look res c k = .ok (some (lbl.remainder.advanceBits lbl.storedBits).toCellRemaining) := by
  obtain ⟨_, _, _, _, hlen, hsz, _⟩ := parseDictLabel_ok hp
  unfold look
  rw [val_lookup_node res c k lbl hp, if_neg (by omega), if_pos ((extract_eq_label hsz hlen).mpr hpre),
    if_pos hz]

/-- The lookup of a key that goes on below a fork: the lookup of its rest in the child its next bit
selects. -/
theorem look_child {res : Cell → Except Excno Cell} {c : Cell} {k : BitString} {lbl : DictLabel}
    (hp : parseDictLabel c k.size res = .ok lbl) (hgood : Good lbl k.size)
    (hpre : ∀ j < lbl.len, k[j]! = (dictLabelBits lbl)[j]!) (hlt : lbl.len < k.size) :
    look res c k =
      look res (lbl.remainder.cell.refs[if k[lbl.len]! then 1 else 0]!) (k.extract (lbl.len + 1) k.size) := by
  obtain ⟨_, _, _, _, hlen, hsz, _⟩ := parseDictLabel_ok hp
  unfold look
  rw [val_lookup_node res c k lbl hp, if_neg hgood, if_pos ((extract_eq_label hsz hlen).mpr hpre),
    if_neg (by omega)]

/-- The bits of a key built by a walk: the label, the bit of the fork, the rest. -/
theorem bget_built {lb kt : BitString} {b : Bool} (j : Nat) :
    (lb ++ #[b] ++ kt)[j]! = if j < lb.size then lb[j]! else if j = lb.size then b else kt[j - lb.size - 1]! := by
  rw [bget_append, Array.size_append]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
  by_cases h1 : j < lb.size
  · rw [if_pos (by omega), bget_append_left h1, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : j = lb.size
    · subst h2
      rw [if_pos (by omega), bget_append_right (Nat.le_refl _), Nat.sub_self, if_pos rfl]; rfl
    · rw [if_neg (by omega), if_neg h2]
      congr 1
      all_goals omega

theorem built_extract {lb kt : BitString} {b : Bool} {m : Nat} (hm : lb.size = m) :
    (lb ++ #[b] ++ kt).extract (m + 1) (lb ++ #[b] ++ kt).size = kt := by
  subst hm
  apply bits_ext
  · simp only [Array.size_extract, Array.size_append, Nat.min_self, List.size_toArray,
      List.length_cons, List.length_nil]; omega
  · intro i _
    rw [bget_suffix, bget_built, if_neg (by omega), if_neg (by omega)]
    congr 1; omega

theorem built_size {lb kt : BitString} {b : Bool} : (lb ++ #[b] ++ kt).size = lb.size + 1 + kt.size := by
  simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]

/-! ## The walks, one node at a time -/

theorem validateLe_ok {lbl : DictLabel} {n : Nat} {x : {r : Nat // r ≤ n}}
    (h : dictValidateNodeExtLe lbl n = .ok x) : x.1 = n - lbl.len ∧ Good lbl n := by
  unfold dictValidateNodeExtLe at h
  unfold Good
  by_cases h1 : n - lbl.len > 0
  · by_cases h2 : lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2
    · have h2' : (lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2) = true := by
        rcases h2 with h | h <;> simp [h]
      simp only [h1, h2', if_true] at h
      cases h
    · have h2' : (lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2) = false := by
        simp only [not_or, Decidable.not_not] at h2; simp [h2.1, h2.2]
      simp only [h1, h2', if_true, Bool.false_eq_true, if_false] at h
      cases h
      exact ⟨rfl, fun hc => h2 hc.2⟩
  · simp only [h1, if_false] at h
    cases h
    exact ⟨rfl, fun hc => h1 hc.1⟩

/-- One node of a min/max walk: a leaf, its label the key; or a fork, the walk going on in the child
of the later bit. -/
theorem minMax_ok {res : Cell → Except Excno Cell} {cell : Cell} {n pos : Nat} {f r : Bool}
    {v : Slice} {k : BitString} {ld : Array Cell}
    (h : dictMinMaxAuxWithCells cell n pos f r res = .ok (v, k, ld)) :
    ∃ lbl, parseDictLabel cell n res = .ok lbl ∧ Good lbl n ∧
      ((n - lbl.len = 0 ∧ v = lbl.remainder.advanceBits lbl.storedBits ∧ k = dictLabelBits lbl) ∨
       (0 < n - lbl.len ∧ ∃ kt ld', dictMinMaxAuxWithCells
          (lbl.remainder.cell.refs[if Dict.laterBit f r (pos + lbl.len) then 1 else 0]!)
          (n - lbl.len - 1) (pos + lbl.len + 1) f r res = .ok (v, kt, ld') ∧
          k = dictLabelBits lbl ++ #[Dict.laterBit f r (pos + lbl.len)] ++ kt)) := by
  rw [dictMinMaxAuxWithCells] at h
  cases hp : parseDictLabel cell n res with
  | error e => simp only [hp, bind, Except.bind] at h; cases h
  | ok lbl =>
    simp only [hp, bind, Except.bind] at h
    cases hv : dictValidateNodeExtLe lbl n with
    | error e => simp only [hv] at h; cases h
    | ok x =>
      obtain ⟨hx, hgood⟩ := validateLe_ok hv
      simp only [hv] at h
      obtain ⟨rem0, hle⟩ := x
      simp only at hx
      subst hx
      refine ⟨lbl, rfl, hgood, ?_⟩
      by_cases h0 : n - lbl.len = 0
      · rw [dif_pos h0] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact Or.inl ⟨h0, h.1.symm, h.2.1.symm⟩
      · rw [dif_neg h0] at h
        refine Or.inr ⟨by omega, ?_⟩
        unfold Dict.laterBit
        revert h
        cases dictMinMaxAuxWithCells
            (lbl.remainder.cell.refs[if (if pos + lbl.len = 0 then f else r) = true then 1 else 0]!)
            (n - lbl.len - 1) (pos + lbl.len + 1) f r res with
        | error e => intro h; cases h
        | ok y =>
          obtain ⟨v', kt, ld'⟩ := y
          intro h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact ⟨kt, ld', rfl, rfl⟩

/-- **A min/max walk that ends finds a key of the map, and no key of the map comes after it** (in
the order of its bits `f`, `r`: the walk takes the later child at every fork), from a node: any
dictionary, the lookups with the walk's resolver. -/
theorem minMax_aux (res : Cell → Except Excno Cell) : ∀ (n : Nat) (cell : Cell) (pos : Nat) (f r : Bool)
    (v : Slice) (k : BitString) (ld : Array Cell),
    dictMinMaxAuxWithCells cell n pos f r res = .ok (v, k, ld) →
    k.size = n ∧ look res cell k = .ok (some v.toCellRemaining) ∧
      ∀ k' : BitString, k'.size = n → Dict.KeyLt f r pos k k' → NoVal res cell k' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro cell pos f r v k ld h
  obtain ⟨lbl, hp, hgood, hcase⟩ := minMax_ok h
  obtain ⟨_, _, _, _, hlen, hsz, _⟩ := parseDictLabel_ok hp
  rcases hcase with ⟨h0, rfl, rfl⟩ | ⟨h0, kt, ld', hrec, rfl⟩
  · -- a leaf: the key is the label
    have hn : lbl.len = n := by omega
    have hp' : parseDictLabel cell (dictLabelBits lbl).size res = .ok lbl := by rw [hsz, hn]; exact hp
    refine ⟨by rw [hsz, hn], look_leaf hp' (fun _ _ => rfl) hsz, ?_⟩
    intro k' hk' hlt
    obtain ⟨i, h1, _, _, h4, h5⟩ := hlt
    have hp'' : parseDictLabel cell k'.size res = .ok lbl := by rw [hk']; exact hp
    exact noVal_of_bit hp'' (j := i) (by omega) (by rw [h4]; exact fun e => h5 e.symm)
  · -- a fork: the label, the later bit, the key found in that child
    obtain ⟨hkt, hlook, hmax⟩ := ih _ (by omega) _ _ _ _ _ _ _ hrec
    have hks : (dictLabelBits lbl ++ #[Dict.laterBit f r (pos + lbl.len)] ++ kt).size = n := by
      rw [built_size, hsz, hkt]; omega
    have hpre : ∀ j < lbl.len, (dictLabelBits lbl ++ #[Dict.laterBit f r (pos + lbl.len)] ++ kt)[j]! =
        (dictLabelBits lbl)[j]! := by
      intro j hj; rw [bget_built, if_pos (by omega)]
    have hbit : (dictLabelBits lbl ++ #[Dict.laterBit f r (pos + lbl.len)] ++ kt)[lbl.len]! =
        Dict.laterBit f r (pos + lbl.len) := by
      rw [bget_built, if_neg (by omega), if_pos (by omega)]
    refine ⟨hks, ?_, ?_⟩
    · rw [look_child (by rw [hks]; exact hp) (by rw [hks]; exact hgood) hpre (by omega), hbit,
        built_extract hsz]
      exact hlook
    · intro k' hk' hlt
      obtain ⟨i, h1, h2, h3, h4, h5⟩ := hlt
      have hp' : parseDictLabel cell k'.size res = .ok lbl := by rw [hk']; exact hp
      rcases Nat.lt_trichotomy i lbl.len with hi | rfl | hi
      · -- `k'` leaves the label
        apply noVal_of_bit hp' (j := i) hi
        rw [h4, ← hpre i hi]; exact fun e => h5 e.symm
      · -- `k'` and the key differ at the fork: the key has the later bit there
        exact absurd hbit h5
      · -- `k'` goes into the same child, after the key's rest
        have hpre' : ∀ j < lbl.len, k'[j]! = (dictLabelBits lbl)[j]! := fun j hj =>
          ((h3 j (by omega)).symm.trans (hpre j hj))
        have hb' : k'[lbl.len]! = Dict.laterBit f r (pos + lbl.len) := (h3 lbl.len hi).symm.trans hbit
        rw [NoVal, look_child hp' (by rw [hk']; exact hgood) hpre' (by omega), hb']
        apply hmax
        · simp only [Array.size_extract, Nat.min_self]; omega
        · have hlt' := (keyLt_suffix (m := lbl.len + 1) (by omega) (by omega)
            (fun j hj => h3 j (by omega))).mp ⟨i, h1, h2, h3, h4, h5⟩
          rw [built_extract hsz, show pos + (lbl.len + 1) = pos + lbl.len + 1 by omega] at hlt'
          exact hlt'

/-- A key with a value starts with the label of the node. -/
theorem label_or_noVal {res : Cell → Except Excno Cell} {cell : Cell} {k : BitString} {lbl : DictLabel}
    (hp : parseDictLabel cell k.size res = .ok lbl) :
    (∀ j < lbl.len, k[j]! = (dictLabelBits lbl)[j]!) ∨ NoVal res cell k := by
  by_cases hall : ∀ j < lbl.len, k[j]! = (dictLabelBits lbl)[j]!
  · exact Or.inl hall
  · right
    have : ∃ j, j < lbl.len ∧ k[j]! ≠ (dictLabelBits lbl)[j]! := by
      apply Classical.byContradiction
      intro hne
      apply hall
      intro j hj
      apply Classical.byContradiction
      intro hj'
      exact hne ⟨j, hj, hj'⟩
    obtain ⟨j, hj, hne⟩ := this
    exact noVal_of_bit hp hj hne

/-- The common prefix of the label and the hint (`bitsCommonPrefixLen`, C++
`LabelParser::common_prefix_len`): the bits before it agree, the bit at it differs if it is within
the label. -/
theorem pfx_spec (lbl : DictLabel) (hint : BitString) (hsz : (dictLabelBits lbl).size = lbl.len)
    (hlen : lbl.len ≤ hint.size) :
    bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len) ≤ lbl.len ∧
      (∀ i < bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len), (dictLabelBits lbl)[i]! = hint[i]!) ∧
      (bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len) < lbl.len →
        (dictLabelBits lbl)[bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len)]! ≠
          hint[bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len)]!) := by
  have htake : ∀ i < lbl.len, (hint.take lbl.len)[i]! = hint[i]! := by
    intro i hi
    rw [Array.take_eq_extract, bget_extract, if_pos (by omega), Nat.zero_add]
  have hm : Nat.min (dictLabelBits lbl).size (hint.take lbl.len).size = lbl.len := by
    have h1 : (hint.take lbl.len).size = lbl.len := by
      simp only [Array.take_eq_extract, Array.size_extract]; omega
    rw [hsz, h1]; exact Nat.min_self lbl.len
  unfold bitsCommonPrefixLen
  simp only [hm]
  obtain ⟨_, h2, h3, h4⟩ := countWhile_spec lbl.len
    (fun k => (dictLabelBits lbl)[k]! == (hint.take lbl.len)[k]!) 0
  have hle := h2 (Nat.zero_le _)
  refine ⟨hle, fun i hi => ?_, fun hlt => ?_⟩
  · have := h3 i (Nat.zero_le _) hi
    simp only [beq_iff_eq] at this
    rw [this, htake i (by omega)]
  · have := h4 hlt
    simp only [beq_eq_false_iff_ne, ne_eq] at this
    rw [htake _ hlt] at this
    exact this

theorem laterBit_first (fb rb : Bool) (pos p : Nat) :
    (if pos = 0 ∧ p = 0 then fb else rb) = Dict.laterBit fb rb (pos + p) := by
  unfold Dict.laterBit
  by_cases hz : pos = 0 ∧ p = 0
  · rw [if_pos hz, if_pos (by omega)]
  · rw [if_neg hz, if_neg (by omega)]

/-- One node of a nearest walk, by its cases: the hint leaves the label (the walk finds nothing
here, or the first key of the node's subtree: a min/max walk with the other bits); the node is a
leaf with the hint as its key; the walk goes on in the child of the hint's next bit, and if it finds
nothing there, in the other child if it comes later. -/
theorem near_ok {res : Cell → Except Excno Cell} {cell : Cell} {hint : BitString} {n pos : Nat}
    {allowEq fb rb : Bool} {out : Option (Slice × BitString)} {ld : Array Cell} (hn : hint.size = n)
    (h : dictNearestAuxWithCells cell hint n pos allowEq fb rb res = .ok (out, ld)) :
    ∃ lbl, parseDictLabel cell n res = .ok lbl ∧ Good lbl n ∧
      ((bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len) < lbl.len ∧
          hint[bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len)]! =
            Dict.laterBit fb rb (pos + bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len)) ∧
          out = none) ∨
       (bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len) < lbl.len ∧
          hint[bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len)]! ≠
            Dict.laterBit fb rb (pos + bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len)) ∧
          ∃ v k ld', dictMinMaxAuxWithCells cell n pos (!fb) (!rb) res = .ok (v, k, ld') ∧
            out = some (v, k)) ∨
       (¬ bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len) < lbl.len ∧ n - lbl.len = 0 ∧
          ((allowEq = true ∧ out = some (lbl.remainder.advanceBits lbl.storedBits, dictLabelBits lbl)) ∨
           (allowEq = false ∧ out = none))) ∨
       (¬ bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len) < lbl.len ∧ 0 < n - lbl.len ∧
          ∃ rc ldc, dictNearestAuxWithCells (lbl.remainder.cell.refs[if hint[lbl.len]! then 1 else 0]!)
              (hint.extract (lbl.len + 1) hint.size) (n - lbl.len - 1) (pos + lbl.len + 1) allowEq fb rb res =
              .ok (rc, ldc) ∧
            ((∃ v kt, rc = some (v, kt) ∧ out = some (v, dictLabelBits lbl ++ #[hint[lbl.len]!] ++ kt)) ∨
             (rc = none ∧ hint[lbl.len]! = Dict.laterBit fb rb (pos + lbl.len) ∧ out = none) ∨
             (rc = none ∧ hint[lbl.len]! ≠ Dict.laterBit fb rb (pos + lbl.len) ∧
               ∃ v ka ld', dictMinMaxAuxWithCells
                  (lbl.remainder.cell.refs[if Dict.laterBit fb rb (pos + lbl.len) then 1 else 0]!)
                  (n - lbl.len - 1) (pos + lbl.len + 1) (!fb) (!rb) res = .ok (v, ka, ld') ∧
                 out = some (v, dictLabelBits lbl ++ #[Dict.laterBit fb rb (pos + lbl.len)] ++ ka))))) := by
  rw [dictNearestAuxWithCells] at h
  cases hp : parseDictLabel cell n res with
  | error e => simp only [hp, bind, Except.bind] at h; cases h
  | ok lbl =>
    simp only [hp, bind, Except.bind] at h
    cases hv : dictValidateNodeExtLe lbl n with
    | error e => simp only [hv] at h; cases h
    | ok x =>
      obtain ⟨hx, hgood⟩ := validateLe_ok hv
      simp only [hv] at h
      obtain ⟨rem0, hle⟩ := x
      simp only at hx
      subst hx
      refine ⟨lbl, rfl, hgood, ?_⟩
      obtain ⟨_, _, _, _, hlen, hsz, _⟩ := parseDictLabel_ok hp
      generalize hpfx : bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len) = p at h ⊢
      by_cases hlt : p < lbl.len
      · rw [if_pos hlt] at h
        rw [laterBit_first] at h
        by_cases he : hint[p]! = Dict.laterBit fb rb (pos + p)
        · rw [if_pos he] at h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          exact Or.inl ⟨hlt, he, h.1.symm⟩
        · rw [if_neg he] at h
          refine Or.inr (Or.inl ⟨hlt, he, ?_⟩)
          revert h
          cases dictMinMaxAuxWithCells cell n pos (!fb) (!rb) res with
          | error e => intro h; cases h
          | ok y =>
            obtain ⟨v, k, ld'⟩ := y
            intro h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            exact ⟨v, k, ld', rfl, h.1.symm⟩
      · rw [if_neg hlt] at h
        by_cases h0 : n - lbl.len = 0
        · rw [dif_pos h0] at h
          refine Or.inr (Or.inr (Or.inl ⟨hlt, h0, ?_⟩))
          cases allowEq
          · simp only [Bool.false_eq_true, if_false, pure, Except.pure, Except.ok.injEq,
              Prod.mk.injEq] at h
            exact Or.inr ⟨rfl, h.1.symm⟩
          · simp only [if_true, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            exact Or.inl ⟨rfl, h.1.symm⟩
        · rw [dif_neg h0] at h
          refine Or.inr (Or.inr (Or.inr ⟨hlt, by omega, ?_⟩))
          have hne : (hint.extract lbl.len hint.size).isEmpty = false := by
            rw [Array.isEmpty_eq_false_iff]
            intro he
            have := congrArg Array.size he
            simp only [Array.size_extract, Nat.min_self, List.size_toArray, List.length_nil] at this
            omega
          simp only [hne, Bool.false_eq_true, if_false, bget_suffix, extract_suffix_suffix,
            Nat.add_zero] at h
          revert h
          cases dictNearestAuxWithCells (lbl.remainder.cell.refs[if hint[lbl.len]! then 1 else 0]!)
              (hint.extract (lbl.len + 1) hint.size) (n - lbl.len - 1) (pos + lbl.len + 1) allowEq fb rb res with
          | error e => intro h; cases h
          | ok y =>
            obtain ⟨rc, ldc⟩ := y
            intro h
            simp only [pure, Except.pure] at h
            refine ⟨rc, ldc, rfl, ?_⟩
            cases rc with
            | some y =>
              obtain ⟨v, kt⟩ := y
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              exact Or.inl ⟨v, kt, rfl, h.1.symm⟩
            | none =>
              have hl : (if pos + lbl.len = 0 then fb else rb) = Dict.laterBit fb rb (pos + lbl.len) := rfl
              rw [hl] at h
              by_cases he : hint[lbl.len]! = Dict.laterBit fb rb (pos + lbl.len)
              · rw [if_pos he] at h
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                exact Or.inr (Or.inl ⟨rfl, he, h.1.symm⟩)
              · rw [if_neg he] at h
                refine Or.inr (Or.inr ⟨rfl, he, ?_⟩)
                revert h
                cases dictMinMaxAuxWithCells
                    (lbl.remainder.cell.refs[if Dict.laterBit fb rb (pos + lbl.len) then 1 else 0]!)
                    (n - lbl.len - 1) (pos + lbl.len + 1) (!fb) (!rb) res with
                | error e => intro h; cases h
                | ok y =>
                  obtain ⟨v, ka, ld'⟩ := y
                  intro h
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨v, ka, ld', rfl, h.1.symm⟩

/-- What a nearest walk from a node says, its result `out`: the first key with a value after the
hint, or no key with a value after it. -/
def NearOut (res : Cell → Except Excno Cell) (cell : Cell) (hint : BitString) (pos : Nat)
    (allowEq fb rb : Bool) : Option (Slice × BitString) → Prop
  | some (v, k) => k.size = hint.size ∧ look res cell k = .ok (some v.toCellRemaining) ∧
      Dict.KeyAfter fb rb pos allowEq hint k ∧
      ∀ k' : BitString, k'.size = hint.size → Dict.KeyAfter fb rb pos allowEq hint k' →
        Dict.KeyLt fb rb pos k' k → NoVal res cell k'
  | none => ∀ k' : BitString, k'.size = hint.size → Dict.KeyAfter fb rb pos allowEq hint k' → NoVal res cell k'

theorem look_some_label {res : Cell → Except Excno Cell} {cell : Cell} {k : BitString} {lbl : DictLabel}
    (hp : parseDictLabel cell k.size res = .ok lbl) {w : Cell} (h : look res cell k = .ok (some w)) :
    ∀ j < lbl.len, k[j]! = (dictLabelBits lbl)[j]! := by
  rcases label_or_noVal hp with h' | h'
  · exact h'
  · exact absurd h (h' w)

/-- **A nearest walk that ends finds the first key of the map after the hint, or there is none**
(in the order of its bits `fb`, `rb`), from a node: any dictionary, the lookups with the walk's
resolver. -/
theorem near_aux (res : Cell → Except Excno Cell) : ∀ (n : Nat) (cell : Cell) (hint : BitString)
    (pos : Nat) (allowEq fb rb : Bool) (out : Option (Slice × BitString)) (ld : Array Cell),
    hint.size = n → dictNearestAuxWithCells cell hint n pos allowEq fb rb res = .ok (out, ld) →
    NearOut res cell hint pos allowEq fb rb out := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro cell hint pos allowEq fb rb out ld hn h
  obtain ⟨lbl, hp, hgood, hcase⟩ := near_ok hn h
  obtain ⟨_, _, _, _, hlen, hsz, _⟩ := parseDictLabel_ok hp
  obtain ⟨hpfxle, hpfxeq, hpfxne⟩ := pfx_spec lbl hint hsz (by omega)
  generalize bitsCommonPrefixLen (dictLabelBits lbl) (hint.take lbl.len) = p at hcase hpfxle hpfxeq hpfxne
  have hpk : ∀ k' : BitString, k'.size = hint.size → parseDictLabel cell k'.size res = .ok lbl :=
    fun k' hk' => by rw [hk', hn]; exact hp
  rcases hcase with ⟨hlt, he, rfl⟩ | ⟨hlt, he, v, k, ld', hmm, rfl⟩ | ⟨hlt, h0, hcase⟩ |
    ⟨hlt, h0, rc, ldc, hrec, hcase⟩
  · -- the hint leaves the label after every key of the node: nothing after it
    intro k' hk' hafter
    rcases label_or_noVal (hpk k' hk') with hl | hl
    · exfalso
      apply keyAfter_not_lt hafter
      have hpre : ∀ j < p, k'[j]! = hint[j]! := fun j hj => (hl j (by omega)).trans (hpfxeq j hj)
      have hd : k'[p]! ≠ hint[p]! := by rw [hl p hlt]; exact hpfxne hlt
      exact (keyLt_at (by omega) (by omega) hpre hd).mpr he
    · exact hl
  · -- the hint leaves the label before every key of the node: the first key of the node
    obtain ⟨hks, hlook, hmin⟩ := minMax_aux res n cell pos (!fb) (!rb) v k ld' hmm
    have hkl := look_some_label (by rw [hks]; exact hp) hlook
    have hlater : (dictLabelBits lbl)[p]! = Dict.laterBit fb rb (pos + p) := by
      have := hpfxne hlt
      revert this he
      generalize (dictLabelBits lbl)[p]! = x
      generalize hint[p]! = y
      generalize Dict.laterBit fb rb (pos + p) = z
      cases x <;> cases y <;> cases z <;> decide
    refine ⟨by omega, hlook, Or.inl ?_, ?_⟩
    · have hpre : ∀ j < p, hint[j]! = k[j]! := fun j hj => ((hpfxeq j hj).symm.trans (hkl j (by omega)).symm)
      have hd : hint[p]! ≠ k[p]! := by rw [hkl p hlt]; exact fun e => hpfxne hlt e.symm
      rw [keyLt_at (by omega) (by omega) hpre hd, hkl p hlt]
      exact hlater
    · intro k' hk' _ hlt'
      exact hmin k' (by omega) (keyLt_flip.mp hlt')
  · -- a leaf whose key is the hint
    have hp' : p = lbl.len := by omega
    subst hp'
    have hhint : hint = dictLabelBits lbl := by
      apply bits_ext (by omega)
      intro i hi; exact (hpfxeq i (by omega)).symm
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨by rw [hhint], ?_, Or.inr ⟨rfl, hhint.symm⟩, ?_⟩
      · exact look_leaf (by rw [hsz, show lbl.len = n by omega]; exact hp) (fun _ _ => rfl) hsz
      · intro k' _ hafter hlt'
        exact absurd hlt' (by rw [← hhint]; exact keyAfter_not_lt hafter)
    · intro k' hk' hafter
      rcases hafter with hafter | ⟨he, _⟩
      · rcases label_or_noVal (hpk k' hk') with hl | hl
        · exfalso
          have : k' = hint := by
            rw [hhint]; apply bits_ext (by omega)
            intro i hi; exact hl i (by omega)
          rw [this] at hafter
          exact keyLt_irrefl hafter
        · exact hl
      · cases he
  · -- a fork: the child of the hint's next bit, then the later child
    have hmatch : ∀ j < lbl.len, hint[j]! = (dictLabelBits lbl)[j]! := by
      have : p = lbl.len := by omega
      subst this
      intro j hj; exact (hpfxeq j hj).symm
    have hcs : (hint.extract (lbl.len + 1) hint.size).size = n - lbl.len - 1 := by
      simp only [Array.size_extract, Nat.min_self]; omega
    have hih := ih (n - lbl.len - 1) (by omega) _ _ _ allowEq fb rb rc ldc hcs hrec
    -- a key that agrees with the label: its lookup goes into the child of its next bit
    have hlookk : ∀ k' : BitString, k'.size = hint.size → (∀ j < lbl.len, k'[j]! = (dictLabelBits lbl)[j]!) →
        look res cell k' = look res (lbl.remainder.cell.refs[if k'[lbl.len]! then 1 else 0]!)
          (k'.extract (lbl.len + 1) k'.size) :=
      fun k' hk' hl => look_child (hpk k' hk') (by rw [hk', hn]; exact hgood) hl (by omega)
    rcases hcase with ⟨v, kt, rfl, rfl⟩ | ⟨rfl, he, rfl⟩ | ⟨rfl, he, v, ka, ld', hmm, rfl⟩
    · -- found in the child of the hint's bit
      obtain ⟨hkt, hlook, hafter, hbetween⟩ := hih
      have hks : (dictLabelBits lbl ++ #[hint[lbl.len]!] ++ kt).size = hint.size := by
        rw [built_size, hsz, hkt]; omega
      have hpre : ∀ j < lbl.len + 1, hint[j]! = (dictLabelBits lbl ++ #[hint[lbl.len]!] ++ kt)[j]! := by
        intro j hj
        rw [bget_built]
        rcases Nat.lt_or_ge j lbl.len with hj' | hj'
        · rw [if_pos (by omega)]; exact hmatch j hj'
        · rw [if_neg (by omega), if_pos (by omega), show j = lbl.len by omega]
      refine ⟨hks, ?_, ?_, ?_⟩
      · rw [hlookk _ hks (fun j hj => by rw [← hpre j (by omega)]; exact hmatch j hj),
          ← hpre lbl.len (by omega), built_extract hsz]
        exact hlook
      · rw [keyAfter_suffix (m := lbl.len + 1) (by omega) hks.symm hpre, built_extract hsz]
        exact hafter
      · intro k' hk' hafter' hlt'
        have hk'pre := keyAfter_between (m := lbl.len + 1) (by omega) hpre hafter' hlt'
        have hl : ∀ j < lbl.len, k'[j]! = (dictLabelBits lbl)[j]! := fun j hj =>
          (hk'pre j (by omega)).trans (hmatch j hj)
        rw [NoVal, hlookk k' hk' hl, hk'pre lbl.len (by omega)]
        apply hbetween
        · simp only [Array.size_extract, Nat.min_self]; omega
        · rw [keyAfter_suffix (m := lbl.len + 1) (by omega) hk'.symm (fun j hj => (hk'pre j hj).symm)] at hafter'
          exact hafter'
        · have := (keyLt_suffix (m := lbl.len + 1) (by omega) (by omega)
            (fun j hj => (hk'pre j hj).trans (hpre j hj))).mp hlt'
          rw [built_extract hsz] at this
          exact this
    · -- nothing in the child of the hint's bit, and it is the later bit: nothing
      intro k' hk' hafter
      rcases label_or_noVal (hpk k' hk') with hl | hl
      · have hpre : ∀ j < lbl.len, k'[j]! = hint[j]! := fun j hj => (hl j hj).trans (hmatch j hj).symm
        by_cases hb : k'[lbl.len]! = hint[lbl.len]!
        · have hpre' : ∀ j < lbl.len + 1, hint[j]! = k'[j]! := by
            intro j hj
            rcases Nat.lt_or_ge j lbl.len with hj' | hj'
            · exact (hpre j hj').symm
            · rw [show j = lbl.len by omega]; exact hb.symm
          rw [NoVal, hlookk k' hk' hl, hb]
          apply hih
          · simp only [Array.size_extract, Nat.min_self]; omega
          · exact (keyAfter_suffix (m := lbl.len + 1) (by omega) hk'.symm hpre').mp hafter
        · exfalso
          apply keyAfter_not_lt hafter
          exact (keyLt_at (by omega) (by omega) hpre hb).mpr he
      · exact hl
    · -- nothing in the child of the hint's bit, the other bit later: the first key of that child
      obtain ⟨hka, hlook, hmin⟩ := minMax_aux res _ _ _ _ _ v ka ld' hmm
      have hks : (dictLabelBits lbl ++ #[Dict.laterBit fb rb (pos + lbl.len)] ++ ka).size = hint.size := by
        rw [built_size, hsz, hka]; omega
      have hpreK : ∀ j < lbl.len, (dictLabelBits lbl ++ #[Dict.laterBit fb rb (pos + lbl.len)] ++ ka)[j]! =
          (dictLabelBits lbl)[j]! := by
        intro j hj; rw [bget_built, if_pos (by omega)]
      have hbitK : (dictLabelBits lbl ++ #[Dict.laterBit fb rb (pos + lbl.len)] ++ ka)[lbl.len]! =
          Dict.laterBit fb rb (pos + lbl.len) := by
        rw [bget_built, if_neg (by omega), if_pos (by omega)]
      have hpreHK : ∀ j < lbl.len, hint[j]! = (dictLabelBits lbl ++ #[Dict.laterBit fb rb (pos + lbl.len)] ++ ka)[j]! :=
        fun j hj => (hmatch j hj).trans (hpreK j hj).symm
      have hdHK : hint[lbl.len]! ≠ (dictLabelBits lbl ++ #[Dict.laterBit fb rb (pos + lbl.len)] ++ ka)[lbl.len]! := by
        rw [hbitK]; exact he
      refine ⟨hks, ?_, Or.inl ?_, ?_⟩
      · rw [hlookk _ hks hpreK, hbitK, built_extract hsz]
        exact hlook
      · rw [keyLt_at (by omega) (by omega) hpreHK hdHK]
        exact hbitK
      · intro k' hk' hafter' hlt'
        have hk'pre := keyAfter_between (m := lbl.len) (by omega) hpreHK hafter' hlt'
        have hl : ∀ j < lbl.len, k'[j]! = (dictLabelBits lbl)[j]! := fun j hj =>
          (hk'pre j hj).trans (hmatch j hj)
        by_cases hb : k'[lbl.len]! = hint[lbl.len]!
        · -- in the child of the hint's bit, where there is nothing after the hint
          have hpre' : ∀ j < lbl.len + 1, hint[j]! = k'[j]! := by
            intro j hj
            rcases Nat.lt_or_ge j lbl.len with hj' | hj'
            · exact (hk'pre j hj').symm
            · rw [show j = lbl.len by omega]; exact hb.symm
          rw [NoVal, hlookk k' hk' hl, hb]
          apply hih
          · simp only [Array.size_extract, Nat.min_self]; omega
          · exact (keyAfter_suffix (m := lbl.len + 1) (by omega) hk'.symm hpre').mp hafter'
        · -- in the later child, before its first key
          have hb' : k'[lbl.len]! = Dict.laterBit fb rb (pos + lbl.len) := by
            revert hb he
            generalize k'[lbl.len]! = x
            generalize hint[lbl.len]! = y
            generalize Dict.laterBit fb rb (pos + lbl.len) = z
            cases x <;> cases y <;> cases z <;> decide
          have hpre' : ∀ j < lbl.len + 1,
              k'[j]! = (dictLabelBits lbl ++ #[Dict.laterBit fb rb (pos + lbl.len)] ++ ka)[j]! := by
            intro j hj
            rcases Nat.lt_or_ge j lbl.len with hj' | hj'
            · exact (hl j hj').trans (hpreK j hj').symm
            · rw [show j = lbl.len by omega, hb', hbitK]
          rw [NoVal, hlookk k' hk' hl, hb']
          apply hmin
          · simp only [Array.size_extract, Nat.min_self]; omega
          · have := (keyLt_suffix (m := lbl.len + 1) (by omega) (by omega) hpre').mp hlt'
            rw [built_extract hsz, show pos + (lbl.len + 1) = pos + lbl.len + 1 by omega] at this
            exact keyLt_flip.mp this

end DictNear

/-! ## The walks of the instructions, as maps -/

/-- The result `out` of a nearest walk from `hint` in the map `m`, in the order of the bits `fb`,
`rb`: the first key of the map after the hint (or the hint, `allowEq`), with its value; or nothing,
and no key of the map after the hint. -/
def Dict.IsNearest (m : BitString → Option Cell) (fb rb allowEq : Bool) (hint : BitString) :
    Option (Slice × BitString) → Prop
  | some (v, k) => k.size = hint.size ∧ m k = some v.toCellRemaining ∧
      Dict.KeyAfter fb rb 0 allowEq hint k ∧
      ∀ k' : BitString, k'.size = hint.size → Dict.KeyAfter fb rb 0 allowEq hint k' →
        Dict.KeyLt fb rb 0 k' k → m k' = none
  | none => ∀ k' : BitString, k'.size = hint.size → Dict.KeyAfter fb rb 0 allowEq hint k' → m k' = none

/-- The result `out` of a min/max walk over `n`-bit keys in the map `m`, the order of the bits `fb`,
`rb`: the last key of the map, with its value; or nothing, and the map empty. -/
def Dict.IsLast (m : BitString → Option Cell) (fb rb : Bool) (n : Nat) :
    Option (Slice × BitString) → Prop
  | some (v, k) => k.size = n ∧ m k = some v.toCellRemaining ∧
      ∀ k' : BitString, k'.size = n → Dict.KeyLt fb rb 0 k k' → m k' = none
  | none => ∀ k' : BitString, k'.size = n → m k' = none

namespace DictNear

theorem valueWith_of_look {res : Cell → Except Excno Cell} {cell : Cell} {k : BitString} {w : Cell}
    (h : look res cell k = .ok (some w)) : Dict.valueWith res (some cell) k = some w := by
  show (match look res cell k with | .ok w => w | .error _ => none) = some w
  rw [h]

theorem valueWith_of_noVal {res : Cell → Except Excno Cell} {cell : Cell} {k : BitString}
    (h : NoVal res cell k) : Dict.valueWith res (some cell) k = none := by
  show (match look res cell k with | .ok w => w | .error _ => none) = none
  cases hl : look res cell k with
  | error e => rfl
  | ok w =>
    cases w with
    | none => rfl
    | some w => exact absurd hl (h w)

end DictNear

open DictNear in
/-- **`DICT*GETNEXT*`, `DICT*GETPREV*` as maps** (`dictNearestWithCells`, C++
`DictionaryFixed::lookup_nearest_key`): a walk that ends finds the first key of the map after the
hint, or there is none; the order of the walk's bits: `rb` the direction (`fetchNext`), `fb` the
first bit (inverted for signed keys, `invertFirst`). Any dictionary, the map as the lookups with the
walk's resolver read it. -/
theorem Dict.nearest_spec (res : Cell → Except Excno Cell) (root : Option Cell) (hint : BitString)
    (fetchNext allowEq invertFirst : Bool) (out : Option (Slice × BitString)) (ld : Array Cell)
    (h : dictNearestWithCells root hint fetchNext allowEq invertFirst res = .ok (out, ld)) :
    Dict.IsNearest (Dict.valueWith res root) (fetchNext != invertFirst) fetchNext allowEq hint out := by
  cases root with
  | none =>
    simp only [dictNearestWithCells, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro k' _ _
    rfl
  | some cell =>
    simp only [dictNearestWithCells] at h
    have hn := near_aux res hint.size cell hint 0 allowEq _ _ out ld rfl h
    cases out with
    | none =>
      intro k' hk' hafter
      exact valueWith_of_noVal (hn k' hk' hafter)
    | some y =>
      obtain ⟨v, k⟩ := y
      obtain ⟨hks, hlook, hafter, hbetween⟩ := hn
      exact ⟨hks, valueWith_of_look hlook, hafter, fun k' hk' ha hl => valueWith_of_noVal (hbetween k' hk' ha hl)⟩

open DictNear in
/-- **`DICT*MIN*`, `DICT*MAX*` (and the `REM` forms) as maps** (`dictMinMaxWithCells`, C++
`DictionaryFixed::get_minmax_key`): a walk that ends finds the last key of the map in the order of
its bits (`rb`: `fetchMax`, `fb`: the first bit, inverted for signed keys), or the map is empty. -/
theorem Dict.minMax_spec (res : Cell → Except Excno Cell) (root : Option Cell) (n : Nat)
    (fetchMax invertFirst : Bool) (out : Option (Slice × BitString)) (ld : Array Cell)
    (h : dictMinMaxWithCells root n fetchMax invertFirst res = .ok (out, ld)) :
    Dict.IsLast (Dict.valueWith res root) (fetchMax != invertFirst) fetchMax n out := by
  cases root with
  | none =>
    simp only [dictMinMaxWithCells, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro k' _
    rfl
  | some cell =>
    simp only [dictMinMaxWithCells, bind, Except.bind] at h
    revert h
    cases hm : dictMinMaxAuxWithCells cell n 0 (fetchMax != invertFirst) fetchMax res with
    | error e => intro h; cases h
    | ok y =>
      obtain ⟨v, k, ld'⟩ := y
      intro h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨hks, hlook, hmax⟩ := minMax_aux res n cell 0 _ _ v k ld' hm
      exact ⟨hks, valueWith_of_look hlook, fun k' hk' hl => valueWith_of_noVal (hmax k' hk' hl)⟩

/-- `Dict.nearest_spec` for the result of the walk as one term (the form a symbolic run splits on). -/
theorem Dict.nearest_spec_ok {res : Cell → Except Excno Cell} {root : Option Cell} {hint : BitString}
    {fetchNext allowEq invertFirst : Bool} {r : Option (Slice × BitString) × Array Cell}
    (h : dictNearestWithCells root hint fetchNext allowEq invertFirst res = .ok r) :
    Dict.IsNearest (Dict.valueWith res root) (fetchNext != invertFirst) fetchNext allowEq hint r.1 :=
  Dict.nearest_spec res root hint fetchNext allowEq invertFirst r.1 r.2 h

/-- `Dict.minMax_spec` for the result of the walk as one term. -/
theorem Dict.minMax_spec_ok {res : Cell → Except Excno Cell} {root : Option Cell} {n : Nat}
    {fetchMax invertFirst : Bool} {r : Option (Slice × BitString) × Array Cell}
    (h : dictMinMaxWithCells root n fetchMax invertFirst res = .ok r) :
    Dict.IsLast (Dict.valueWith res root) (fetchMax != invertFirst) fetchMax n r.1 :=
  Dict.minMax_spec res root n fetchMax invertFirst r.1 r.2 h

/-- The map of a walk read with a resolver that loads ordinary cells as themselves, on a well-formed
dictionary, is `Dict.value`: the nearest key in `Dict.value`. -/
theorem Dict.nearest_value {res : Cell → Except Excno Cell} (hr : ResolvesOrdinary res)
    {root : Option Cell} {hint : BitString} (hwf : Dict.WF root hint.size)
    {fetchNext allowEq invertFirst : Bool} {out : Option (Slice × BitString)} {ld : Array Cell}
    (h : dictNearestWithCells root hint fetchNext allowEq invertFirst res = .ok (out, ld)) :
    Dict.IsNearest (Dict.value root) (fetchNext != invertFirst) fetchNext allowEq hint out := by
  have hs := Dict.nearest_spec res root hint fetchNext allowEq invertFirst out ld h
  have he : ∀ k : BitString, k.size = hint.size → Dict.valueWith res root k = Dict.value root k :=
    fun k hk => Dict.valueWith_eq_value hr hwf hk
  cases out with
  | none =>
    intro k' hk' ha
    rw [← he k' hk']; exact hs k' hk' ha
  | some y =>
    obtain ⟨v, k⟩ := y
    obtain ⟨hks, hv, ha, hb⟩ := hs
    exact ⟨hks, by rw [← he k hks]; exact hv, ha,
      fun k' hk' ha' hl => by rw [← he k' hk']; exact hb k' hk' ha' hl⟩

/-- The last key of a well-formed dictionary in `Dict.value`. -/
theorem Dict.minMax_value {res : Cell → Except Excno Cell} (hr : ResolvesOrdinary res)
    {root : Option Cell} {n : Nat} (hwf : Dict.WF root n) {fetchMax invertFirst : Bool}
    {out : Option (Slice × BitString)} {ld : Array Cell}
    (h : dictMinMaxWithCells root n fetchMax invertFirst res = .ok (out, ld)) :
    Dict.IsLast (Dict.value root) (fetchMax != invertFirst) fetchMax n out := by
  have hs := Dict.minMax_spec res root n fetchMax invertFirst out ld h
  have he : ∀ k : BitString, k.size = n → Dict.valueWith res root k = Dict.value root k :=
    fun k hk => Dict.valueWith_eq_value hr hwf hk
  cases out with
  | none =>
    intro k' hk'
    rw [← he k' hk']; exact hs k' hk'
  | some y =>
    obtain ⟨v, k⟩ := y
    obtain ⟨hks, hv, hb⟩ := hs
    exact ⟨hks, by rw [← he k hks]; exact hv, fun k' hk' hl => by rw [← he k' hk']; exact hb k' hk' hl⟩

/-! ## The resolver of the VM on well-formed dictionaries -/

/-- A delete with the resolver of the VM (any resolver of ordinary cells) on a well-formed dictionary
is the delete with the default resolver (`DictMap.delete_resolve`): the form `Dict.value_delete`,
`Dict.WF.delete` take. -/
theorem Dict.deleteWithLoads_resolve {r : Cell → Except Excno Cell} (hr : ResolvesOrdinary r)
    {root : Option Cell} {key : BitString} (hwf : Dict.WF root key.size) :
    dictDeleteWithLoads root key r = dictDeleteWithLoads root key := by
  cases root with
  | none => rfl
  | some c => exact DictMap.delete_resolve r hr key.size c key 0 hwf

/-- `Dict.nearest_value` for the result of the walk as one term. -/
theorem Dict.nearest_value_ok {res : Cell → Except Excno Cell} (hr : ResolvesOrdinary res)
    {root : Option Cell} {hint : BitString} {n : Nat} (hwf : Dict.WF root n) (hn : hint.size = n)
    {fetchNext allowEq invertFirst : Bool} {r : Option (Slice × BitString) × Array Cell}
    (h : dictNearestWithCells root hint fetchNext allowEq invertFirst res = .ok r) :
    Dict.IsNearest (Dict.value root) (fetchNext != invertFirst) fetchNext allowEq hint r.1 :=
  Dict.nearest_value hr (by rw [hn]; exact hwf) h

/-- `Dict.minMax_value` for the result of the walk as one term. -/
theorem Dict.minMax_value_ok {res : Cell → Except Excno Cell} (hr : ResolvesOrdinary res)
    {root : Option Cell} {n : Nat} (hwf : Dict.WF root n) {fetchMax invertFirst : Bool}
    {r : Option (Slice × BitString) × Array Cell}
    (h : dictMinMaxWithCells root n fetchMax invertFirst res = .ok r) :
    Dict.IsLast (Dict.value root) (fetchMax != invertFirst) fetchMax n r.1 :=
  Dict.minMax_value hr hwf h

/-! ## Unsigned integer keys -/

namespace DictNear

open DictMap

theorem bget_natToBits (u w i : Nat) (h : i < w) : (natToBits u w)[i]! = u.testBit (w - 1 - i) := by
  simp [natToBits, h]

/-- Two numbers whose bits agree above `i`, the first with `0` at `i`, the second with `1`. -/
theorem lt_of_testBit_above {x y : Nat} (i : Nat) (hx : x.testBit i = false) (hy : y.testBit i = true)
    (habove : ∀ j, i < j → x.testBit j = y.testBit j) : x < y := by
  have hq : x / 2 ^ (i + 1) = y / 2 ^ (i + 1) := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact habove _ (by omega)
  have hxm : x % 2 ^ (i + 1) < 2 ^ i := by
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    rw [Nat.testBit_mod_two_pow]
    by_cases hji : j < i + 1
    · have : j = i := by omega
      subst this; simp [hx]
    · simp [hji]
  have hym : 2 ^ i ≤ y % 2 ^ (i + 1) := by
    apply Nat.ge_two_pow_of_testBit
    rw [Nat.testBit_mod_two_pow]; simp [hy]
  have h1 := Nat.div_add_mod x (2 ^ (i + 1))
  have h2 := Nat.div_add_mod y (2 ^ (i + 1))
  rw [hq] at h1
  omega

/-- Two different bit strings of a size: the first bit where they differ. -/
theorem first_diff {a b : BitString} (hs : a.size = b.size) (hne : a ≠ b) :
    ∃ i, i < a.size ∧ (∀ j < i, a[j]! = b[j]!) ∧ a[i]! ≠ b[i]! := by
  have key : ∀ m, m ≤ a.size → (∀ j < m, a[j]! = b[j]!) ∨
      ∃ i, i < m ∧ (∀ j < i, a[j]! = b[j]!) ∧ a[i]! ≠ b[i]! := by
    intro m
    induction m with
    | zero => intro _; left; intro j hj; omega
    | succ m ih =>
      intro hm
      rcases ih (by omega) with h | ⟨i, hi, h1, h2⟩
      · by_cases hb : a[m]! = b[m]!
        · left
          intro j hj
          rcases Nat.lt_or_ge j m with hj' | hj'
          · exact h j hj'
          · rw [show j = m by omega]; exact hb
        · exact Or.inr ⟨m, by omega, h, hb⟩
      · exact Or.inr ⟨i, by omega, h1, h2⟩
  rcases key a.size (Nat.le_refl _) with h | ⟨i, hi, h1, h2⟩
  · exact absurd (bits_ext hs h) hne
  · exact ⟨i, hi, h1, h2⟩

/-- Two different keys of a size come one before the other. -/
theorem keyLt_total {fb rb : Bool} {pos : Nat} {a b : BitString} (hs : a.size = b.size) (hne : a ≠ b) :
    Dict.KeyLt fb rb pos a b ∨ Dict.KeyLt fb rb pos b a := by
  obtain ⟨i, hi, h1, h2⟩ := first_diff hs hne
  by_cases hb : b[i]! = Dict.laterBit fb rb (pos + i)
  · exact Or.inl ((keyLt_at hi (by omega) h1 h2).mpr hb)
  · right
    refine (keyLt_at (by omega) hi (fun j hj => (h1 j hj).symm) (fun e => h2 e.symm)).mpr ?_
    revert hb h2
    generalize a[i]! = x
    generalize b[i]! = y
    generalize Dict.laterBit fb rb (pos + i) = z
    cases x <;> cases y <;> cases z <;> decide

theorem keyLt_natToBits_lt {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : Dict.KeyLt true true 0 (natToBits a n) (natToBits b n)) : a < b := by
  obtain ⟨i, h1, _, h3, h4, h5⟩ := h
  rw [natToBits_size] at h1
  have hl : Dict.laterBit true true (0 + i) = true := by unfold Dict.laterBit; split <;> rfl
  rw [hl, bget_natToBits _ _ _ h1] at h4 h5
  apply lt_of_testBit_above (n - 1 - i) (by simpa using h5) h4
  intro j hj
  rcases Nat.lt_or_ge j n with hjn | hjn
  · have := h3 (n - 1 - j) (by omega)
    rw [bget_natToBits _ _ _ (by omega), bget_natToBits _ _ _ (by omega),
      show n - 1 - (n - 1 - j) = j by omega] at this
    exact this
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hjn)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hjn))]

theorem natToBits_ne {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hne : a ≠ b) :
    natToBits a n ≠ natToBits b n := by
  intro h
  apply hne
  apply Nat.eq_of_testBit_eq
  intro j
  rcases Nat.lt_or_ge j n with hj | hj
  · have := congrArg (fun x : BitString => x[n - 1 - j]!) h
    simp only at this
    rw [bget_natToBits _ _ _ (by omega), bget_natToBits _ _ _ (by omega),
      show n - 1 - (n - 1 - j) = j by omega] at this
    exact this
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hj)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hj))]

end DictNear

open DictNear in
/-- **Unsigned keys come in the order of the integers** (`DICTU*`, `fetchNext`, the bits
`true true`): `natToBits a n` before `natToBits b n` iff `a < b`. -/
theorem Dict.keyLt_natToBits {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    Dict.KeyLt true true 0 (natToBits a n) (natToBits b n) ↔ a < b := by
  constructor
  · exact keyLt_natToBits_lt ha hb
  · intro hlt
    rcases keyLt_total (by rw [natToBits_size, natToBits_size]) (natToBits_ne ha hb (by omega)) with h | h
    · exact h
    · exact absurd (keyLt_natToBits_lt hb ha h) (by omega)

/-! ## Signed integer keys -/

namespace DictNear

open DictMap

/-- The bits of a signed key (`dictKeyBits?`, C++ `export_bits` of a signed integer): the two's
complement of a key within the range of `n` bits. -/
theorem signed_bits {x : Int} {n : Nat} {bs : BitString} (hn : 0 < n)
    (h : dictKeyBits? x n false = some bs) :
    -((2 ^ (n - 1) : Nat) : Int) ≤ x ∧ x < ((2 ^ (n - 1) : Nat) : Int) ∧
      bs = natToBits (if 0 ≤ x then x.toNat else 2 ^ n - (-x).toNat) n := by
  have hP : intPow2 (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := by simp [intPow2]
  have hS : (1 <<< n : Nat) = 2 ^ n := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  unfold dictKeyBits? at h
  rw [if_neg (by omega)] at h
  simp only [Bool.false_eq_true, if_false, hP] at h
  split at h
  · cases h
  · rename_i hr
    split at h
    · rename_i bs' hb
      cases h
      refine ⟨by omega, by omega, ?_⟩
      unfold intToBitsTwos at hb
      simp only [bind, Except.bind, pure, Except.pure, hP, hS] at hb
      rw [if_neg (by omega)] at hb
      split at hb
      · cases hb
      · split at hb
        · rename_i hx
          cases hb
          rw [if_pos (by omega)]
        · rename_i hx
          cases hb
          rw [if_neg (by omega)]
    · cases h

/-- The bits of a signed key and of the key plus `2 ^ (n - 1)` (an unsigned key) differ only in the
first bit. -/
theorem offset_testBit {n : Nat} {x : Int} (hn : 0 < n) (h1 : -((2 ^ (n - 1) : Nat) : Int) ≤ x)
    (h2 : x < ((2 ^ (n - 1) : Nat) : Int)) :
    (∀ j, j < n - 1 → (if 0 ≤ x then x.toNat else 2 ^ n - (-x).toNat).testBit j =
        (x + ((2 ^ (n - 1) : Nat) : Int)).toNat.testBit j) ∧
      (if 0 ≤ x then x.toNat else 2 ^ n - (-x).toNat).testBit (n - 1) =
        !(x + ((2 ^ (n - 1) : Nat) : Int)).toNat.testBit (n - 1) := by
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    have ho : (x + ((2 ^ (n - 1) : Nat) : Int)).toNat = 2 ^ (n - 1) + x.toNat := by omega
    rw [ho]
    refine ⟨fun j hj => (Nat.testBit_two_pow_add_gt hj _).symm, ?_⟩
    rw [Nat.testBit_two_pow_add_eq, Bool.not_not]
  · rw [if_neg hx]
    have hu : 2 ^ n - (-x).toNat = 2 ^ (n - 1) + (x + ((2 ^ (n - 1) : Nat) : Int)).toNat := by omega
    rw [hu]
    exact ⟨fun j hj => Nat.testBit_two_pow_add_gt hj _, Nat.testBit_two_pow_add_eq _ _⟩

/-- The order of a walk with the first bit inverted (`false true`) on keys is the order of all bits
(`true true`) on the keys with their first bit inverted. -/
theorem keyLt_flipFirst {a b a' b' : BitString} (ha : a.size = a'.size) (hb : b.size = b'.size)
    (hfa : ∀ i, 0 < i → a[i]! = a'[i]!) (hfb : ∀ i, 0 < i → b[i]! = b'[i]!)
    (h0a : a'[0]! = !a[0]!) (h0b : b'[0]! = !b[0]!) :
    Dict.KeyLt false true 0 a b ↔ Dict.KeyLt true true 0 a' b' := by
  have hl : ∀ i, Dict.laterBit true true (0 + i) = true := fun i => by
    unfold Dict.laterBit; split <;> rfl
  have hl' : ∀ i, Dict.laterBit false true (0 + i) = (if i = 0 then false else true) := fun i => by
    unfold Dict.laterBit; simp
  unfold Dict.KeyLt
  simp only [hl, hl']
  constructor
  · rintro ⟨i, h1, h2, h3, h4, h5⟩
    refine ⟨i, by omega, by omega, fun j hj => ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [h0a, h0b, h3 0 hj]
      · rw [← hfa j hj0, ← hfb j hj0]; exact h3 j hj
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [h0b]; simp at h4; simp [h4]
      · rw [← hfb i hi0]; rw [if_neg (by omega)] at h4; exact h4
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [h0a]; simp at h5; simp [h5]
      · rw [← hfa i hi0]; rw [if_neg (by omega)] at h5; exact h5
  · rintro ⟨i, h1, h2, h3, h4, h5⟩
    refine ⟨i, by omega, by omega, fun j hj => ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have := h3 0 hj
        rw [h0a, h0b] at this
        cases ha0 : a[0]! <;> cases hb0 : b[0]! <;> simp_all
      · rw [hfa j hj0, hfb j hj0]; exact h3 j hj
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [h0b] at h4; simp only [if_true]; cases hb0 : b[0]! <;> simp_all
      · rw [hfb i hi0, if_neg (by omega)]; exact h4
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [h0a] at h5; simp only [if_true]; cases ha0 : a[0]! <;> simp_all
      · rw [hfa i hi0, if_neg (by omega)]; exact h5

theorem signed_flip {n : Nat} {x : Int} (hn : 0 < n) (h1 : -((2 ^ (n - 1) : Nat) : Int) ≤ x)
    (h2 : x < ((2 ^ (n - 1) : Nat) : Int)) :
    (∀ i, 0 < i → (natToBits (if 0 ≤ x then x.toNat else 2 ^ n - (-x).toNat) n)[i]! =
        (natToBits (x + ((2 ^ (n - 1) : Nat) : Int)).toNat n)[i]!) ∧
      (natToBits (x + ((2 ^ (n - 1) : Nat) : Int)).toNat n)[0]! =
        !(natToBits (if 0 ≤ x then x.toNat else 2 ^ n - (-x).toNat) n)[0]! := by
  obtain ⟨hlow, htop⟩ := offset_testBit hn h1 h2
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases Nat.lt_or_ge i n with hin | hin
    · rw [bget_natToBits _ _ _ hin, bget_natToBits _ _ _ hin]
      exact hlow _ (by omega)
    · rw [bget_of_size_le _ _ (by rw [natToBits_size]; omega),
        bget_of_size_le _ _ (by rw [natToBits_size]; omega)]
  · rw [bget_natToBits _ _ _ hn, bget_natToBits _ _ _ hn, Nat.sub_zero, htop, Bool.not_not]

end DictNear

open DictNear in
/-- **Signed keys come in the order of the integers** (`DICTI*GETNEXT`: `fetchNext`, the first bit
inverted, the bits `false true`): the bits of `x` before those of `y` iff `x < y`. -/
theorem Dict.keyLt_intBits {n : Nat} {x y : Int} {bx bY : BitString} (hn : 0 < n)
    (hx : dictKeyBits? x n false = some bx) (hy : dictKeyBits? y n false = some bY) :
    Dict.KeyLt false true 0 bx bY ↔ x < y := by
  obtain ⟨hx1, hx2, rfl⟩ := signed_bits hn hx
  obtain ⟨hy1, hy2, rfl⟩ := signed_bits hn hy
  obtain ⟨fx, f0x⟩ := signed_flip hn hx1 hx2
  obtain ⟨fy, f0y⟩ := signed_flip hn hy1 hy2
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  rw [keyLt_flipFirst (by rw [natToBits_size, natToBits_size]) (by rw [natToBits_size, natToBits_size])
    fx fy f0x f0y, Dict.keyLt_natToBits (by omega) (by omega)]
  omega

end TvmLean

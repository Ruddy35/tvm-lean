import TvmLean.Proofs.Exec.Spec.Dict

/-!
# Dictionary labels: the encoding read back

A node of a dictionary (C++ `Dictionary`, dict.cpp) starts with the label of its edge, written by
`dictLabelEncode` (C++ `append_dict_label`) in one of three forms (`hml_short`, `hml_long`,
`hml_same`) and read by `parseDictLabel` (C++ `LabelParser`). The set and delete operations build
nodes with `dictLabelEncode`; to follow a lookup through them, the label they wrote must read back:

* `parseDictLabel_encode`: a node whose bits start with `dictLabelEncode bits bits.size maxLen` (and
  `bits.size ≤ maxLen`) reads back as a label of length `bits.size` with the bits `bits`, the rest of
  the node right after the encoding (`DictLabel.remainder`, `storedBits`);
* `dictLabelMatches_iff`, `dictCommonPrefixLen_spec`: the comparison of a label with a key that the
  lookup and the set make, as equality of bit strings;
* `parseDictLabel_bits_size`, `parseDictLabel_len_le`, `parseDictLabel_refPos`: what any label read
  from a node satisfies.
-/

namespace TvmLean

namespace DictMap

/-! ## Bit strings -/

theorem bget (a : Array Bool) (i : Nat) : a[i]! = (a[i]?).getD false := by
  rw [getElem!_def]; cases a[i]? <;> rfl

theorem bget_append (a b : Array Bool) (i : Nat) :
    (a ++ b)[i]! = if i < a.size then a[i]! else b[i - a.size]! := by
  simp only [bget, Array.getElem?_append]; split <;> rfl

theorem bget_extract (a : Array Bool) (i s e : Nat) :
    (a.extract s e)[i]! = if i < min e a.size - s then a[s + i]! else false := by
  simp only [bget, Array.getElem?_extract]; split <;> rfl

theorem bget_replicate (n i : Nat) (b : Bool) :
    (Array.replicate n b)[i]! = if i < n then b else false := by
  simp only [bget, Array.getElem?_replicate]; split <;> rfl

theorem bget_of_size_le (a : Array Bool) (i : Nat) (h : a.size ≤ i) : a[i]! = false := by
  simp only [bget, Array.getElem?_eq_none h, Option.getD_none]

/-- Two bit strings of the same size with the same bits are equal. -/
theorem bits_ext {a b : Array Bool} (hs : a.size = b.size) (h : ∀ i < a.size, a[i]! = b[i]!) : a = b := by
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at this

theorem bits_ext_iff {a b : Array Bool} : a = b ↔ a.size = b.size ∧ ∀ i < a.size, a[i]! = b[i]! := by
  constructor
  · rintro rfl; exact ⟨rfl, fun _ _ => rfl⟩
  · rintro ⟨h1, h2⟩; exact bits_ext h1 h2

theorem bitsToNat_pair (a b : Bool) : bitsToNat #[a, b] = (if a then 2 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> rfl

theorem extract_two (x : Array Bool) (h : 2 ≤ x.size) : x.extract 0 2 = #[x[0]!, x[1]!] := by
  apply bits_ext
  · simp; omega
  · intro i hi
    simp only [Array.size_extract] at hi
    simp only [bget_extract]
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp <;> omega

/-- `bitsAllSame?` finds the bit all the bits are equal to. -/
theorem bitsAllSame?_eq_some {bs : BitString} {b : Bool} (h : bitsAllSame? bs = some b) :
    bs = Array.replicate bs.size b := by
  unfold bitsAllSame? at h
  split at h
  · rename_i hpos
    have key : ∀ (l : List Nat) (ok : Bool),
        (forIn (m := Id) l ok (fun i r => if bs[i]! = bs[0]! then pure (ForInStep.yield r)
          else pure (ForInStep.yield false))) = (ok && l.all (fun i => bs[i]! == bs[0]!)) := by
      intro l
      induction l with
      | nil => intro ok; simp only [List.forIn_nil, List.all_nil, Bool.and_true]; rfl
      | cons a l ih =>
        intro ok
        by_cases ha : bs[a]! = bs[0]!
        · simp [List.forIn_cons, ha, ih]
        · have hb : (bs[a]! == bs[0]!) = false := by simp [ha]
          simp [List.forIn_cons, ha, ih, hb]
    simp only [Id.run, Std.Range.forIn_eq_forIn_range'] at h
    simp at h
    rw [key] at h
    change (if (true && (List.range' 0 bs.size).all fun i => bs[i]! == bs[0]!) = true then
      some bs[0]! else none) = some b at h
    split at h
    · rename_i hall
      cases h
      simp only [Bool.true_and, List.all_eq_true, List.mem_range'_1, beq_iff_eq] at hall
      apply bits_ext (by simp)
      intro i hi
      rw [bget_replicate, if_pos hi]
      exact hall i (by omega)
    · cases h
  · cases h

/-! ## Reading back the encoding -/

theorem natLenBits_lt {len maxLen : Nat} (h : len ≤ maxLen) : len < 2 ^ natLenBits maxLen := by
  unfold natLenBits
  split
  · omega
  · have := Nat.lt_log2_self (n := maxLen)
    omega

/-- The label `00` (empty). -/
theorem parseDictLabel_empty {r : Cell → Except Excno Cell} {c : Cell} {maxLen : Nat} {rest : BitString}
    (hr : r c = .ok c) (hc : c.bits = #[false, false] ++ rest) :
    parseDictLabel c maxLen r = .ok { remainder := ⟨c, 2, 0⟩, len := 0, sameBit := none, storedBits := 0 } := by
  have h2 : 2 ≤ c.bits.size := by rw [hc]; simp
  have hp : bitsToNat (c.bits.extract 0 2) = 0 := by
    rw [extract_two _ h2, bitsToNat_pair, hc]
    simp [bget_append]
  unfold parseDictLabel
  simp only [hr, bind, Except.bind, Slice.haveBits, Slice.ofCell, Slice.readBits, h2, decide_true,
    Bool.not_true, Bool.false_eq_true, if_false, Nat.zero_add, hp, pure, Except.pure, Slice.advanceBits]

/-- `countWhile` stops at the first index where the condition fails. -/
theorem countWhile_eq_of {limit m : Nat} {p : Nat → Bool} :
    ∀ (k : Nat), k ≤ m → m < limit → (∀ i, k ≤ i → i < m → p i = true) → p m = false →
      countWhile limit p k = m := by
  intro k hk hm hp hpm
  induction h : m - k generalizing k with
  | zero =>
    have : k = m := by omega
    subst this
    rw [countWhile_eq, if_pos hm, hpm]; rfl
  | succ d ih =>
    rw [countWhile_eq, if_pos (by omega), hp k (Nat.le_refl k) (by omega), if_pos rfl]
    exact ih (k + 1) (by omega) (fun i h1 h2 => hp i (by omega) h2) (by omega)

theorem bget_append_left {a b : Array Bool} {i : Nat} (h : i < a.size) : (a ++ b)[i]! = a[i]! := by
  rw [bget_append, if_pos h]

theorem bget_append_right {a b : Array Bool} {i : Nat} (h : a.size ≤ i) :
    (a ++ b)[i]! = b[i - a.size]! := by
  rw [bget_append, if_neg (by omega)]

theorem extract_append_of_le {a b : Array Bool} {i j : Nat} (h : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  have : j - a.size = 0 := by omega
  rw [Array.extract_append, this]
  simp

theorem extract_append_of_ge {a b : Array Bool} {i j : Nat} (h : a.size ≤ i) :
    (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) := by
  rw [Array.extract_append, Array.extract_empty_of_size_le_start h, Array.empty_append]

theorem extract_all {α : Type} {a : Array α} {j : Nat} (h : a.size ≤ j) : a.extract 0 j = a :=
  Array.extract_eq_self_iff.mpr (Or.inr ⟨rfl, h⟩)

/-- Side conditions on the sizes of bit strings. -/
macro "bsz" : tactic => `(tactic| first | omega | (simp <;> omega) | simp)

/-- The label `hml_short` (`0 1^len 0 bits`). -/
theorem parseDictLabel_short {r : Cell → Except Excno Cell} {c : Cell} {maxLen : Nat} {bits rest : BitString}
    (hr : r c = .ok c) (hpos : 0 < bits.size) (hlen : bits.size ≤ maxLen)
    (hc : c.bits = (#[false] ++ Array.replicate bits.size true ++ #[false] ++ bits) ++ rest) :
    parseDictLabel c maxLen r =
      .ok { remainder := ⟨c, bits.size + 2, 0⟩, len := bits.size, sameBit := none, storedBits := bits.size } := by
  generalize hn : bits.size = n at hc hpos hlen ⊢
  have hsz : c.bits.size = 2 * n + 2 + rest.size := by
    rw [hc]; simp only [Array.size_append, Array.size_replicate, List.size_toArray, List.length_cons,
      List.length_nil]; omega
  have hA : ∀ i, i < n + 1 → c.bits[i]! = (#[false] ++ Array.replicate n true)[i]! := by
    intro i hi
    rw [hc, bget_append_left (by bsz), bget_append_left (by bsz),
      bget_append_left (by bsz)]
  have h0 : c.bits[0]! = false := by
    rw [hA 0 (by omega), bget_append_left (by simp)]; rfl
  have h1 : ∀ i, 1 ≤ i → i ≤ n → c.bits[i]! = true := by
    intro i h1 h2
    rw [hA i (by omega), bget_append_right (by bsz), bget_replicate, if_pos (by bsz)]
  have hn1 : c.bits[n + 1]! = false := by
    have hs : (#[false] ++ Array.replicate n true).size = n + 1 := by simp; omega
    rw [hc, bget_append_left (by bsz), bget_append_left (by bsz), bget_append_right (by bsz), hs,
      Nat.sub_self]
    rfl
  have h2 : 2 ≤ c.bits.size := by omega
  have hp : bitsToNat (c.bits.extract 0 2) = 1 := by
    rw [extract_two _ h2, bitsToNat_pair, h0, h1 1 (Nat.le_refl 1) hpos]; rfl
  have hcount : Slice.countLeading ⟨c, 0 + 1, 0⟩ true = n := by
    unfold Slice.countLeading
    refine countWhile_eq_of 0 (Nat.zero_le _) (by simp only; omega) (fun i _ hi => ?_) ?_
    · simp only; rw [h1 (0 + 1 + i) (by omega) (by omega)]; rfl
    · simp only; rw [show 0 + 1 + n = n + 1 by omega, hn1]; rfl
  unfold parseDictLabel
  simp only [hr, bind, Except.bind, Slice.haveBits, Slice.ofCell, Slice.readBits, Nat.zero_add, h2,
    decide_true, Bool.not_true, Bool.false_eq_true, if_false, hp, Slice.advanceBits]
  rw [show ({ cell := c, bitPos := 1, refPos := 0 } : Slice) = ⟨c, 0 + 1, 0⟩ from rfl, hcount]
  have h3 : ¬ n > maxLen := by omega
  have h4 : 1 + (2 * n + 1) ≤ c.bits.size := by omega
  simp only [h3, if_false, h4, decide_true, Bool.not_true, Bool.false_eq_true, pure, Except.pure]
  congr 3
  omega

theorem natToBits_two_two : natToBits 2 2 = #[true, false] := by decide

/-- The label `hml_long` (`10`, the length on `natLenBits maxLen` bits, the bits). -/
theorem parseDictLabel_long {r : Cell → Except Excno Cell} {c : Cell} {maxLen : Nat} {bits rest : BitString}
    (hr : r c = .ok c) (hlen : bits.size ≤ maxLen)
    (hc : c.bits = (natToBits 2 2 ++ natToBits bits.size (natLenBits maxLen) ++ bits) ++ rest) :
    parseDictLabel c maxLen r =
      .ok { remainder := ⟨c, 2 + natLenBits maxLen, 0⟩, len := bits.size, sameBit := none,
            storedBits := bits.size } := by
  generalize hn : bits.size = n at hc hlen ⊢
  generalize hk : natLenBits maxLen = k at hc ⊢
  have hlt : n < 2 ^ k := hk ▸ natLenBits_lt hlen
  have hsz : c.bits.size = 2 + k + n + rest.size := by
    rw [hc]; simp only [Array.size_append, natToBits_size]; omega
  have h2 : 2 ≤ c.bits.size := by omega
  have hT : ∀ i, i < 2 → c.bits[i]! = (natToBits 2 2)[i]! := by
    intro i hi
    rw [hc, bget_append_left (by bsz), bget_append_left (by bsz),
      bget_append_left (by bsz)]
  have hp : bitsToNat (c.bits.extract 0 2) = 2 := by
    rw [extract_two _ h2, hT 0 (by omega), hT 1 (by omega), natToBits_two_two]; rfl
  have hL : c.bits.extract 2 (2 + k) = natToBits n k := by
    rw [hc, extract_append_of_le (by bsz), extract_append_of_le (by bsz),
      extract_append_of_ge (by bsz)]
    simp only [natToBits_size, Nat.sub_self, Nat.add_sub_cancel_left]
    exact extract_all (by simp)
  unfold parseDictLabel
  simp only [hr, bind, Except.bind, Slice.haveBits, Slice.ofCell, Slice.readBits, Nat.zero_add, h2,
    decide_true, Bool.not_true, Bool.false_eq_true, if_false, hp, Slice.advanceBits,
    Slice.takeBitsAsNatCellUnd, pure, Except.pure, hk]
  have h3 : 2 + k ≤ c.bits.size := by omega
  have h4 : ¬ n > maxLen := by omega
  have h5 : 2 + k + n ≤ c.bits.size := by omega
  simp only [h3, decide_true, if_true, hL, bitsToNat_natToBits_of_lt hlt, h4, if_false, h5,
    Bool.not_true, Bool.false_eq_true]

/-- The label `hml_same` (`11`, the bit, the length on `natLenBits maxLen` bits). -/
theorem parseDictLabel_same {r : Cell → Except Excno Cell} {c : Cell} {maxLen len : Nat} {b : Bool}
    {rest : BitString} (hr : r c = .ok c) (hlen : len ≤ maxLen)
    (hc : c.bits = (natToBits (6 + (if b then 1 else 0)) 3 ++ natToBits len (natLenBits maxLen)) ++ rest) :
    parseDictLabel c maxLen r =
      .ok { remainder := ⟨c, 3 + natLenBits maxLen, 0⟩, len := len, sameBit := some b,
            storedBits := 0 } := by
  generalize hk : natLenBits maxLen = k at hc ⊢
  have hlt : len < 2 ^ k := hk ▸ natLenBits_lt hlen
  have hsz : c.bits.size = 3 + k + rest.size := by
    rw [hc]; simp only [Array.size_append, natToBits_size]
  have h2 : 2 ≤ c.bits.size := by omega
  have hb3 : natToBits (6 + (if b then 1 else 0)) 3 = #[true, true, b] := by cases b <;> decide
  have h3 : c.bits.extract 0 3 = #[true, true, b] := by
    rw [hc, extract_append_of_le (by bsz), extract_append_of_le (by simp),
      extract_all (by simp), hb3]
  have hp : bitsToNat (c.bits.extract 0 2) = 3 := by
    have e : c.bits.extract 0 2 = (c.bits.extract 0 3).extract 0 2 := by
      rw [Array.extract_extract]; rfl
    rw [e, h3]; cases b <;> decide
  have hs3 : bitsToNat (c.bits.extract 0 3) = 6 + (if b then 1 else 0) := by
    rw [h3, ← hb3, bitsToNat_natToBits_of_lt (by cases b <;> decide)]
  have hL : c.bits.extract (0 + 3) (0 + 3 + k) = natToBits len k := by
    rw [hc, extract_append_of_le (by bsz), extract_append_of_ge (by bsz)]
    simp only [natToBits_size, Nat.zero_add, Nat.sub_self, Nat.add_sub_cancel_left]
    exact extract_all (by simp)
  have hsame : decide ((6 + (if b then 1 else 0)) &&& 1 = 1) = b := by cases b <;> decide
  unfold parseDictLabel
  simp only [hr, bind, Except.bind, Slice.haveBits, Slice.ofCell, Slice.readBits, h2,
    decide_true, Bool.not_true, Bool.false_eq_true, if_false, hp, Slice.advanceBits,
    Slice.takeBitsAsNatCellUnd, pure, Except.pure, hk]
  have h3' : 0 + 3 ≤ c.bits.size := by omega
  have h3'' : 0 + 3 + k ≤ c.bits.size := by omega
  have h4 : ¬ len > maxLen := by omega
  have h5 : 0 + (3 + k) ≤ c.bits.size := by omega
  simp only [h3', h3'', h5, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true, hs3,
    hL, bitsToNat_natToBits_of_lt hlt, h4, hsame]

/-- The bits right after a prefix of `P` bits. -/
theorem readBits_after {c : Cell} {pre bits rest : BitString} (hc : c.bits = (pre ++ bits) ++ rest) :
    c.bits.extract pre.size (pre.size + bits.size) = bits := by
  rw [hc, extract_append_of_le (by bsz), extract_append_of_ge (by bsz)]
  simp only [Nat.sub_self, Nat.add_sub_cancel_left]
  exact extract_all (Nat.le_refl _)

/-- **The label `dictLabelEncode` writes reads back** (C++ `append_dict_label`, then
`LabelParser`): a node of a dictionary with keys of at most `maxLen` bits whose bits start with the
encoding of the label `bits` reads as a label of `bits.size` bits equal to `bits`; the rest of the
node starts right after the encoding (`remainder` at the stored bits of the label, `storedBits`
of them), and no reference is read. -/
theorem parseDictLabel_encode {r : Cell → Except Excno Cell} {c : Cell} {maxLen : Nat} {bits rest : BitString}
    (hr : r c = .ok c) (hlen : bits.size ≤ maxLen)
    (hc : c.bits = dictLabelEncode bits bits.size maxLen ++ rest) :
    ∃ lbl, parseDictLabel c maxLen r = .ok lbl ∧ lbl.len = bits.size ∧ dictLabelBits lbl = bits ∧
      lbl.remainder.cell = c ∧ lbl.remainder.refPos = 0 ∧
      lbl.remainder.bitPos + lbl.storedBits = (dictLabelEncode bits bits.size maxLen).size := by
  have htake : bits.take bits.size = bits := by
    rw [Array.take_eq_extract]; exact extract_all (Nat.le_refl _)
  unfold dictLabelEncode at hc ⊢
  split
  · rename_i h0
    rw [if_pos h0] at hc
    refine ⟨_, parseDictLabel_empty hr hc, h0.symm, ?_, rfl, rfl, rfl⟩
    rw [Array.eq_empty_of_size_eq_zero h0]
    simp [dictLabelBits, Slice.readBits]; omega
  · rename_i h0
    rw [if_neg h0] at hc
    rw [htake] at hc ⊢
    split
    · rename_i b hsame
      rw [hsame] at hc
      have hrep := bitsAllSame?_eq_some hsame
      unfold dictLabelEncodeSame at hc ⊢
      dsimp only at hc ⊢
      split
      · rename_i h11
        rw [if_pos h11] at hc
        refine ⟨_, parseDictLabel_same hr hlen hc, rfl, ?_, rfl, rfl, ?_⟩
        · simp only [dictLabelBits]; exact hrep.symm
        · simp [natToBits_size]
      · rename_i h11
        rw [if_neg h11] at hc
        split
        · rename_i h10
          rw [if_pos h10, ← hrep] at hc
          refine ⟨_, parseDictLabel_long hr hlen hc, rfl, ?_, rfl, rfl, ?_⟩
          · simp only [dictLabelBits, Slice.readBits]
            have := readBits_after (pre := natToBits 2 2 ++ natToBits bits.size (natLenBits maxLen)) hc
            simpa [natToBits_size, Nat.add_assoc] using this
          · simp [natToBits_size, ← hrep]; omega
        · rename_i h10
          rw [if_neg h10, ← hrep] at hc
          refine ⟨_, parseDictLabel_short hr (by omega) hlen hc, rfl, ?_, rfl, rfl, ?_⟩
          · simp only [dictLabelBits, Slice.readBits]
            have := readBits_after (pre := #[false] ++ Array.replicate bits.size true ++ #[false]) hc
            simp only [Array.size_append, Array.size_replicate, List.size_toArray, List.length_cons,
              List.length_nil] at this
            rw [show bits.size + 2 = 0 + 1 + bits.size + 1 by omega]
            exact this
          · simp [← hrep]; omega
    · rename_i hsame
      rw [hsame] at hc
      dsimp only at hc ⊢
      split
      · rename_i h10
        rw [if_pos h10] at hc
        refine ⟨_, parseDictLabel_long hr hlen hc, rfl, ?_, rfl, rfl, ?_⟩
        · simp only [dictLabelBits, Slice.readBits]
          have := readBits_after (pre := natToBits 2 2 ++ natToBits bits.size (natLenBits maxLen)) hc
          simpa [natToBits_size, Nat.add_assoc] using this
        · simp [natToBits_size]; omega
      · rename_i h10
        rw [if_neg h10] at hc
        refine ⟨_, parseDictLabel_short hr (by omega) hlen hc, rfl, ?_, rfl, rfl, ?_⟩
        · simp only [dictLabelBits, Slice.readBits]
          have := readBits_after (pre := #[false] ++ Array.replicate bits.size true ++ #[false]) hc
          simp only [Array.size_append, Array.size_replicate, List.size_toArray, List.length_cons,
            List.length_nil] at this
          rw [show bits.size + 2 = 0 + 1 + bits.size + 1 by omega]
          exact this
        · simp; omega

/-! ## Any label read from a node -/

theorem takeBits_ok {s : Slice} {n : Nat} {v : Nat × Slice} (h : s.takeBitsAsNatCellUnd n = .ok v) :
    v = (bitsToNat (s.readBits n), s.advanceBits n) ∧ s.bitPos + n ≤ s.cell.bits.size := by
  unfold Slice.takeBitsAsNatCellUnd at h
  split at h
  · rename_i hb
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨h.symm, by simpa [Slice.haveBits] using hb⟩
  · cases h

open Lean Meta Elab Tactic in
/-- `takebits_facts`: every hypothesis `s.takeBitsAsNatCellUnd n = .ok v` (`v` a variable) is
replaced by what it says (`takeBits_ok`): `v` is substituted, the bound on the bits added. -/
elab "takebits_facts" : tactic => do
  let mut i := 0
  for _ in [0:8] do
    let found ← withMainContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        if let some (_, lhs, rhs) := ty.eq? then
          if lhs.isAppOf ``Slice.takeBitsAsNatCellUnd && rhs.isAppOf ``Except.ok && rhs.appArg!.isFVar then
            return some d.fvarId
      return none
    let some fv := found | return
    let name := Name.mkSimple s!"htb_{i}"
    i := i + 1
    let g ← getMainGoal
    let g ← g.rename fv name
    replaceMainGoal [g]
    let hv := mkIdent (Name.mkSimple s!"htbv_{i}")
    evalTactic (← `(tactic| (obtain ⟨$hv, _⟩ := takeBits_ok $(mkIdent name); clear $(mkIdent name); subst $hv)))

/-- What a label read from a node satisfies: the node is loaded by the resolver, the rest of the
node starts at its first reference, the label is at most `maxLen` long, its bits are stored in the
node (`dictLabelBits` has `len` bits), and the stored bits are within the node. -/
theorem parseDictLabel_ok {r : Cell → Except Excno Cell} {c : Cell} {maxLen : Nat} {lbl : DictLabel}
    (h : parseDictLabel c maxLen r = .ok lbl) :
    ∃ c', r c = .ok c' ∧ lbl.remainder.cell = c' ∧ lbl.remainder.refPos = 0 ∧ lbl.len ≤ maxLen ∧
      (dictLabelBits lbl).size = lbl.len ∧ lbl.remainder.bitPos + lbl.storedBits ≤ c'.bits.size := by
  unfold parseDictLabel at h
  cases hres : r c with
  | error e => simp [hres, bind, Except.bind] at h
  | ok c' =>
    refine ⟨c', rfl, ?_⟩
    simp only [hres, bind, Except.bind] at h
    repeat' (first | (cases h; done) | split at h)
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      takebits_facts
      simp only [Slice.haveBits, Slice.advanceBits, Slice.ofCell, dictLabelBits, Slice.readBits,
        Bool.not_eq_true', decide_eq_false_iff_not, Decidable.not_not, gt_iff_lt, Nat.not_lt,
        Nat.zero_add, Array.size_extract, Array.size_replicate] at *
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega

/-! ## Comparing a label with a key -/

/-- The bits of the label of `lbl` are the bits it is compared on. -/
theorem dictLabelBits_get (lbl : DictLabel) (i : Nat) (hi : i < lbl.len) :
    (dictLabelBits lbl)[i]! = match lbl.sameBit with
      | some b => b
      | none => (lbl.remainder.readBits lbl.len)[i]! := by
  unfold dictLabelBits
  split
  · rename_i b hb
    rw [bget_replicate, if_pos hi, hb]
  · rename_i hb
    rw [hb]

/-- `dictLabelMatches` (C++ `LabelParser::is_prefix_of`): the key has the label's bits at `pos`. -/
theorem dictLabelMatches_iff (lbl : DictLabel) (key : BitString) (pos : Nat)
    (hsz : (dictLabelBits lbl).size = lbl.len) :
    dictLabelMatches lbl key pos = true ↔
      pos + lbl.len ≤ key.size ∧ key.extract pos (pos + lbl.len) = dictLabelBits lbl := by
  unfold dictLabelMatches
  split
  · rename_i h
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro h'; omega
  · rename_i h
    have hle : pos + lbl.len ≤ key.size := by omega
    simp only [hle, true_and]
    rw [bits_ext_iff]
    have hs : (key.extract pos (pos + lbl.len)).size = lbl.len := by simp; omega
    simp only [hs, hsz, true_and]
    have hget : ∀ i < lbl.len, (key.extract pos (pos + lbl.len))[i]! = key[pos + i]! := by
      intro i hi; rw [bget_extract, if_pos (by omega)]
    split
    · rename_i b hb
      rw [allBelow_iff]
      constructor
      · intro h i hi
        rw [hget i hi, dictLabelBits_get lbl i hi, hb]
        simpa using h i hi
      · intro h i hi
        have := h i hi
        rw [hget i hi, dictLabelBits_get lbl i hi, hb] at this
        simp [this]
    · rename_i hb
      rw [allBelow_iff]
      constructor
      · intro h i hi
        rw [hget i hi, dictLabelBits_get lbl i hi, hb]
        have := h i hi
        simp only [beq_iff_eq] at this
        exact this.symm
      · intro h i hi
        have := h i hi
        rw [hget i hi, dictLabelBits_get lbl i hi, hb] at this
        simp [this]

/-- What `countWhile` finds: the first index from `k` at which the condition fails (or the
limit). -/
theorem countWhile_spec (lim : Nat) (P : Nat → Bool) (k : Nat) :
    k ≤ countWhile lim P k ∧ (k ≤ lim → countWhile lim P k ≤ lim) ∧
      (∀ i, k ≤ i → i < countWhile lim P k → P i = true) ∧
      (countWhile lim P k < lim → P (countWhile lim P k) = false) := by
  induction h : lim - k generalizing k with
  | zero =>
    have e : countWhile lim P k = k := by
      rw [countWhile_eq, if_neg (by omega)]
    rw [e]
    refine ⟨Nat.le_refl _, fun _ => by omega, fun i h1 h2 => by omega, fun h' => by omega⟩
  | succ d ih =>
    rw [countWhile_eq, if_pos (by omega)]
    cases hp : P k
    · simp only [Bool.false_eq_true, if_false]
      refine ⟨Nat.le_refl _, fun _ => by omega, fun i h1 h2 => by omega, fun _ => hp⟩
    · simp only [if_true]
      obtain ⟨h1, h2, h3, h4⟩ := ih (k + 1) (by omega)
      refine ⟨by omega, fun _ => h2 (by omega), fun i hi1 hi2 => ?_, h4⟩
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hlt
      · exact hp
      · exact h3 i (by omega) hi2

/-- The common prefix of a label and a key (C++ `LabelParser::common_prefix_len`, as the set of
the model computes it): at most the label's length, the bits before it agree, and the bit at it
differs if it is within the label. -/
theorem dictCommonPrefixLen_spec (lbl : DictLabel) (key : BitString) (hlen : lbl.len ≤ key.size) :
    dictCommonPrefixLen lbl key ≤ lbl.len ∧
      (∀ i < dictCommonPrefixLen lbl key, (dictLabelBits lbl)[i]! = key[i]!) ∧
      (dictCommonPrefixLen lbl key < lbl.len →
        (dictLabelBits lbl)[dictCommonPrefixLen lbl key]! ≠ key[dictCommonPrefixLen lbl key]!) := by
  have hmin : min lbl.len key.size = lbl.len := Nat.min_eq_left hlen
  unfold dictCommonPrefixLen
  split
  · rename_i b hb
    simp only [hmin]
    obtain ⟨_, h2, h3, h4⟩ := countWhile_spec lbl.len (fun k => key[k]! == b) 0
    refine ⟨h2 (Nat.zero_le _), fun i hi => ?_, fun hlt => ?_⟩
    · have := h3 i (Nat.zero_le _) hi
      rw [dictLabelBits_get lbl i (by have := h2 (Nat.zero_le _); omega), hb]
      simp only [beq_iff_eq] at this; exact this.symm
    · have := h4 hlt
      rw [dictLabelBits_get lbl _ hlt, hb]
      simp only [beq_eq_false_iff_ne, ne_eq] at this
      exact fun h => this h.symm
  · rename_i hb
    simp only [hmin]
    obtain ⟨_, h2, h3, h4⟩ := countWhile_spec lbl.len
      (fun k => (lbl.remainder.readBits lbl.len)[k]! == key[k]!) 0
    refine ⟨h2 (Nat.zero_le _), fun i hi => ?_, fun hlt => ?_⟩
    · have := h3 i (Nat.zero_le _) hi
      rw [dictLabelBits_get lbl i (by have := h2 (Nat.zero_le _); omega), hb]
      simpa using this
    · have := h4 hlt
      rw [dictLabelBits_get lbl _ hlt, hb]
      simpa using this

end DictMap

end TvmLean

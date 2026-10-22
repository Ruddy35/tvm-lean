import TvmLean.Proofs.Exec.Dict.Label

/-!
# Dictionary lookups, one node at a time

The lookup of the model (`dictLookupWithCells`, C++ `Dictionary::lookup`) walks the key from its
first bit, keeping the position `pos` in the key. The set operation of the model recurses on the
rest of the key instead (`key.extract (len + 1) key.size`). To relate them:

* `lookupAux_shift`: the lookup at position `pos` is the lookup of the rest of the key from `0`;
* `DictMap.val`: what a lookup says about the dictionary's map, the contents of the value found
  (`Slice.toCellRemaining`; a dictionary rebuilt by a set or a delete keeps the contents of its
  values, not the slices);
* `val_lookup_node`: the lookup from a node, by what its label says (the value of a leaf, or the
  lookup of the rest of the key in the child the next bit selects), and `val_lookup_built` for a
  node built as `dictLabelEncode` of its label, then its value or children.
-/

namespace TvmLean

namespace DictMap

/-- The bit `i` of the rest of a key from `pos` is the bit `pos + i` of the key. -/
theorem bget_suffix (key : BitString) (pos i : Nat) : (key.extract pos key.size)[i]! = key[pos + i]! := by
  rw [bget_extract]
  split
  · rfl
  · rw [bget_of_size_le]; simp at *; omega

theorem extract_suffix_suffix (key : BitString) (pos k : Nat) :
    (key.extract pos key.size).extract k (key.extract pos key.size).size = key.extract (pos + k) key.size := by
  rw [Array.extract_extract]
  simp only [Array.size_extract, Nat.min_self]
  congr 1
  omega

/-- The label is compared with the key at `pos` as with the rest of the key from `0`. -/
theorem dictLabelMatches_shift (lbl : DictLabel) (key : BitString) (pos : Nat) (hpos : pos ≤ key.size) :
    dictLabelMatches lbl key pos = dictLabelMatches lbl (key.extract pos key.size) 0 := by
  unfold dictLabelMatches
  simp only [Array.size_extract, Nat.min_self, bget_suffix, Nat.zero_add]
  by_cases h : pos + lbl.len > key.size
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- One step of the lookup at `pos` is the step at `0` on the rest of the key, if the recursive
calls agree. -/
theorem lookupStep_shift (key : BitString) (pos : Nat) (hpos : pos ≤ key.size)
    (rec : Cell → (p : Nat) → pos < p → p ≤ key.size → Nat → Except Excno (Option Slice × Array Cell))
    (rec' : Cell → (p : Nat) → 0 < p → p ≤ (key.extract pos key.size).size → Nat →
      Except Excno (Option Slice × Array Cell))
    (hrec : ∀ c p h1 h2 p' h1' h2' rm, p = pos + p' → rec c p h1 h2 rm = rec' c p' h1' h2' rm)
    (cell : Cell) (rem : Nat) (r : Cell → Except Excno Cell) :
    dictLookupWithCellsStep key pos rec cell rem r =
      dictLookupWithCellsStep (key.extract pos key.size) 0 rec' cell rem r := by
  unfold dictLookupWithCellsStep
  cases parseDictLabel cell rem r with
  | error e => rfl
  | ok lbl =>
    simp only [bind, Except.bind]
    cases dictValidateNodeExt lbl rem with
    | error e => rfl
    | ok rem0 =>
      simp only
      rw [← dictLabelMatches_shift lbl key pos hpos]
      split
      · rfl
      · split
        · rfl
        · have hs : (key.extract pos key.size).size = key.size - pos := by simp
          by_cases hge : pos + lbl.len ≥ key.size
          · rw [dif_pos hge, dif_pos (by omega)]
          · rw [dif_neg hge, dif_neg (by omega)]
            simp only [Nat.zero_add, bget_suffix]
            rw [hrec _ _ _ _ (lbl.len + 1) (by omega) (by omega) _ (by omega)]

/-- The lookup with a step budget, at `pos`, is the lookup of the rest of the key from `0`. -/
theorem lookupAuxF_shift (r : Cell → Except Excno Cell) (f : Nat) :
    ∀ (cell : Cell) (key : BitString) (pos rem : Nat), pos ≤ key.size →
      dictLookupAuxWithCellsF r f cell key pos rem =
        dictLookupAuxWithCellsF r f cell (key.extract pos key.size) 0 rem := by
  induction f with
  | zero => intro cell key pos rem _; rfl
  | succ f ih =>
    intro cell key pos rem hpos
    simp only [dictLookupAuxWithCellsF]
    apply lookupStep_shift key pos hpos
    intro c p h1 h2 p' h1' h2' rm hp
    rw [ih c key p rm (by omega), ih c (key.extract pos key.size) p' rm (by omega),
      extract_suffix_suffix, hp]

/-- **The lookup at `pos` is the lookup of the rest of the key.** -/
theorem lookupAux_shift (r : Cell → Except Excno Cell) (cell : Cell) (key : BitString) (pos rem : Nat)
    (hpos : pos ≤ key.size) :
    dictLookupAuxWithCells cell key pos rem r =
      dictLookupAuxWithCells cell (key.extract pos key.size) 0 rem r := by
  unfold dictLookupAuxWithCells
  rw [lookupAuxF_shift r _ cell key pos rem hpos]
  congr 1
  simp

/-! ## What a lookup says about the map -/

/-- What the result of a lookup says about the map of the dictionary: the contents of the value
found (`none` if the key is absent), or the error. -/
def val : Except Excno (Option Slice × Array Cell) → Except Excno (Option Cell)
  | .ok (v, _) => .ok (v.map Slice.toCellRemaining)
  | .error e => .error e

@[simp] theorem val_ok (v : Option Slice) (cells : Array Cell) : val (.ok (v, cells)) = .ok (v.map Slice.toCellRemaining) := rfl
@[simp] theorem val_error (e : Excno) : val (.error e) = .error e := rfl

/-- The check of a node (C++ `LabelParser::validate_ext`): a fork holds exactly the stored label
bits and two references. -/
theorem dictValidateNodeExt_eq (lbl : DictLabel) (n : Nat) :
    dictValidateNodeExt lbl n =
      if n - lbl.len > 0 ∧ (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)
      then .error .dictErr else .ok (n - lbl.len) := by
  unfold dictValidateNodeExt
  by_cases h1 : n - lbl.len > 0
  · by_cases h2 : lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2
    · have h2' : (lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2) = true := by
        rcases h2 with h | h <;> simp [h]
      simp only [h1, if_true, h2', h2, and_self]; rfl
    · have h2' : (lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2) = false := by
        simp only [not_or, Decidable.not_not] at h2; simp [h2.1, h2.2]
      simp only [h1, if_true, h2', h2, and_false, if_false, Bool.false_eq_true]; rfl
  · simp only [h1, if_false, false_and]; rfl

/-- The lookup of `key` from the node `c`, by the node's label: an ill-formed fork is dict_err; a
key that does not start with the label is absent; at a leaf the value is the rest of the node;
at a fork the lookup goes on with the rest of the key in the child its next bit selects. -/
theorem val_lookup_node (r : Cell → Except Excno Cell) (c : Cell) (key : BitString) (lbl : DictLabel)
    (hp : parseDictLabel c key.size r = .ok lbl) :
    val (dictLookupAuxWithCells c key 0 key.size r) =
      if key.size - lbl.len > 0 ∧
          (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2) then
        .error .dictErr
      else if key.extract 0 lbl.len = dictLabelBits lbl then
        (if key.size = lbl.len then .ok (some (lbl.remainder.advanceBits lbl.storedBits).toCellRemaining)
         else val (dictLookupAuxWithCells (lbl.remainder.cell.refs[if key[lbl.len]! then 1 else 0]!)
          (key.extract (lbl.len + 1) key.size) 0 (key.extract (lbl.len + 1) key.size).size r))
      else .ok none := by
  obtain ⟨c', _, _, _, hlen, hsz, _⟩ := parseDictLabel_ok hp
  rw [dictLookupAuxWithCells_eq]
  unfold dictLookupWithCellsStep
  rw [hp]
  dsimp only [bind, Except.bind]
  rw [dictValidateNodeExt_eq]
  have hm := dictLabelMatches_iff lbl key 0 hsz
  simp only [Nat.zero_add] at hm
  by_cases hbad : key.size - lbl.len > 0 ∧
      (lbl.remainder.bitsRemaining ≠ lbl.storedBits ∨ lbl.remainder.refsRemaining ≠ 2)
  · rw [if_pos hbad, if_pos hbad]; rfl
  · rw [if_neg hbad, if_neg hbad]
    dsimp only [pure, Except.pure]
    by_cases hmatch : key.extract 0 lbl.len = dictLabelBits lbl
    · have hm' : dictLabelMatches lbl key 0 = true := hm.mpr ⟨hlen, hmatch⟩
      rw [if_pos hmatch]
      simp only [hm', Bool.not_true, Bool.false_eq_true, if_false]
      by_cases hz : key.size = lbl.len
      · have : key.size - lbl.len = 0 := by omega
        rw [if_pos this, if_pos hz]
        rfl
      · have : ¬ key.size - lbl.len = 0 := by omega
        simp only [this, if_false, hz]
        rw [dif_neg (by omega)]
        simp only [Nat.zero_add]
        rw [lookupAux_shift r _ key (lbl.len + 1) _ (by omega)]
        have hrem : key.size - lbl.len - 1 = (key.extract (lbl.len + 1) key.size).size := by simp; omega
        rw [hrem]
        cases dictLookupAuxWithCells (lbl.remainder.cell.refs[if key[lbl.len]! = true then 1 else 0]!)
          (key.extract (lbl.len + 1) key.size) 0 (key.extract (lbl.len + 1) key.size).size r with
        | error e => rfl
        | ok x => rfl
    · have hm' : dictLabelMatches lbl key 0 = false := by
        cases h : dictLabelMatches lbl key 0
        · rfl
        · exact absurd (hm.mp h).2 hmatch
      rw [if_neg hmatch]
      simp only [hm', Bool.not_false, if_true]
      rfl

/-- The rest of an ordinary cell from its first bits: its other bits and its references. -/
theorem toCellRemaining_after (pre X : BitString) (Y : Array Cell) :
    (Slice.mk (Cell.mkOrdinary (pre ++ X) Y) pre.size 0).toCellRemaining = Cell.mkOrdinary X Y := by
  simp only [Slice.toCellRemaining, Cell.mkOrdinary, Array.size_append]
  congr 1
  · rw [Array.extract_append, Array.extract_empty_of_size_le_start (Nat.le_refl _), Array.empty_append]
    simp only [Nat.sub_self, Nat.add_sub_cancel_left]
    exact Array.extract_eq_self_iff.mpr (Or.inr ⟨rfl, Nat.le_refl _⟩)
  · exact Array.extract_eq_self_iff.mpr (Or.inr ⟨rfl, Nat.le_refl _⟩)
  · simp only [Array.extract_eq_self_iff.mpr (Or.inr ⟨rfl, Nat.le_refl _⟩)]

/-- **The lookup from a node built by a set or a delete** (`Cell.mkOrdinary` of the encoding of its
label `bits`, then the bits `X` and references `Y` of its value or children): as
`val_lookup_node`, with the label read back (`parseDictLabel_encode`). -/
theorem val_lookup_built (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) (bits X : BitString)
    (Y : Array Cell) (key : BitString) (hlen : bits.size ≤ key.size) :
    val (dictLookupAuxWithCells (Cell.mkOrdinary (dictLabelEncode bits bits.size key.size ++ X) Y) key 0
        key.size r) =
      if key.size - bits.size > 0 ∧ (X.size ≠ 0 ∨ Y.size ≠ 2) then .error .dictErr
      else if key.extract 0 bits.size = bits then
        (if key.size = bits.size then .ok (some (Cell.mkOrdinary X Y))
         else val (dictLookupAuxWithCells (Y[if key[bits.size]! then 1 else 0]!)
          (key.extract (bits.size + 1) key.size) 0 (key.extract (bits.size + 1) key.size).size r))
      else .ok none := by
  generalize hN : Cell.mkOrdinary (dictLabelEncode bits bits.size key.size ++ X) Y = N
  have hrN : r N = .ok N := hr N (by rw [← hN]; rfl)
  have hbits : N.bits = dictLabelEncode bits bits.size key.size ++ X := by rw [← hN]; rfl
  have hrefs : N.refs = Y := by rw [← hN]; rfl
  obtain ⟨lbl, hp, hl, hb, hc, hrp, hpos⟩ := parseDictLabel_encode hrN hlen hbits
  rw [val_lookup_node r N key lbl hp, hl, hb]
  have hrem : lbl.remainder = ⟨N, lbl.remainder.bitPos, 0⟩ := by
    rw [← hc, ← hrp]
  have hbr : lbl.remainder.bitsRemaining = lbl.storedBits + X.size := by
    simp only [Slice.bitsRemaining, hc, hbits, Array.size_append]; omega
  have hrr : lbl.remainder.refsRemaining = Y.size := by
    simp only [Slice.refsRemaining, hc, hrefs, hrp, Nat.sub_zero]
  have hpay : (lbl.remainder.advanceBits lbl.storedBits).toCellRemaining = Cell.mkOrdinary X Y := by
    rw [hrem]
    simp only [Slice.advanceBits]
    rw [hpos, ← toCellRemaining_after (dictLabelEncode bits bits.size key.size) X Y, hN]
  rw [hbr, hrr, hpay, hc, hrefs]
  have e : (lbl.storedBits + X.size ≠ lbl.storedBits ∨ Y.size ≠ 2) ↔ (X.size ≠ 0 ∨ Y.size ≠ 2) := by omega
  simp only [e]

end DictMap

end TvmLean

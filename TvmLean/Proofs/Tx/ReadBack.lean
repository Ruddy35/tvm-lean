import TvmLean.Proofs.Tx.Phases

/-!
# Reading back what a writer wrote

`ReadsAs r B R P`: the TL-B read `r` (`Reader`, a `StateT Slice Option`), on a slice whose remaining
bits start with `B` and whose remaining references start with `R`, if it succeeds, consumes exactly
`B` and `R` and returns a value satisfying `P`. It composes along `>>=` (`ReadsAs.bind`); the
primitive reads (`ReadsAs.bits`, `ReadsAs.ref`, `ReadsAs.uint`, `ReadsAs.bool`, `ReadsAs.maybe_none`,
`ReadsAs.maybe_some`, `ReadsAs.varUInt`, `ReadsAs.currencies`, `ReadsAs.addrStd_mkAddr`) are stated
on the bits the writers (`W.uint`, `W.varUInt`, `W.maybeRef`, `Account.mkAddr`) write. A
`VarUInteger n` reads back only below `2 ^ (8 * (n - 1))` (`W.varUInt` writes a wrong length above;
C++ `compute_state` and `Tx.computeState` fail there).

`computeState_readBack`: the account `Tx.computeState` writes from a state `tf`, put in a shard
account (`shardAccountCell`), reads back (`Account.unpack`) as an active account only if `tf` is
active, and then with the code and the data of `tf`. `Tx.computeState` is cut into definitional
pieces for this (`computeState_pieces`: `csAdjust`, `csState`, `Tx.storageStat`, `preW`); the parts it
writes (`StateParts`) fit their fields: the balance, the storage statistics and the due payment
whenever `Tx.computeState` succeeds (C++ `compute_state` checks them with `FAIL_UNLESS`,
`computeState_some`); the address, the dict hash and the fixed prefix length have the shape the
reader needs (`StateParts.Fits`).
-/

namespace TvmLean

theorem natToBits_size (n k : Nat) : (natToBits n k).size = k := by
  simp [natToBits]

private def bstep (acc : Nat) (b : Bool) : Nat := (acc <<< 1) + (if b then 1 else 0)

private theorem foldl_bstep (l : List Bool) (acc : Nat) :
    l.foldl bstep acc = acc * 2 ^ l.length + l.foldl bstep 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (bstep 0 b)]
    simp only [bstep, Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_add, Nat.pow_succ]
    split <;> simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 2] <;> omega

private theorem bitsToNat_eq_foldl (bs : BitString) : bitsToNat bs = bs.toList.foldl bstep 0 := by
  rw [Array.foldl_toList]; rfl

theorem bitsToNat_append (a b : BitString) :
    bitsToNat (a ++ b) = bitsToNat a * 2 ^ b.size + bitsToNat b := by
  rw [bitsToNat_eq_foldl, bitsToNat_eq_foldl, bitsToNat_eq_foldl, Array.toList_append, List.foldl_append,
    foldl_bstep]
  simp

theorem bitsToNat_singleton (b : Bool) : bitsToNat #[b] = if b then 1 else 0 := by
  cases b <;> rfl

theorem natToBits_succ (n k : Nat) : natToBits n (k + 1) = #[n.testBit k] ++ natToBits n k := by
  apply Array.ext
  · simp [natToBits_size]; omega
  · intro i h1 h2
    rcases i with _ | i
    · simp [natToBits]
    · simp [natToBits]
      congr 1
      omega

theorem bitsToNat_natToBits (n k : Nat) : bitsToNat (natToBits n k) = n % 2 ^ k := by
  induction k with
  | zero => simp [natToBits, bitsToNat, Nat.mod_one]
  | succ k ih =>
    rw [natToBits_succ, bitsToNat_append, ih, natToBits_size, bitsToNat_singleton, Nat.mod_pow_succ,
      Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h] <;> omega

theorem bitsToNat_natToBits_of_lt {n k : Nat} (h : n < 2 ^ k) : bitsToNat (natToBits n k) = n := by
  rw [bitsToNat_natToBits, Nat.mod_eq_of_lt h]

end TvmLean

namespace TvmLean.Tx

/-- The bits and references left in a slice, as lists. -/
def Rem (s : Slice) (B : List Bool) (R : List Cell) : Prop :=
  s.bitPos ≤ s.cell.bits.size ∧ s.cell.bits.toList.drop s.bitPos = B ∧
  s.refPos ≤ s.cell.refs.size ∧ s.cell.refs.toList.drop s.refPos = R

theorem Rem.ofCell (c : Cell) : Rem (Slice.ofCell c) c.bits.toList c.refs.toList := by
  simp [Rem, Slice.ofCell]

/-- Reading `r` from a slice whose bits start with `B` and whose references start with `R`, if it
succeeds, gives a value satisfying `P` and consumes exactly `B` and `R`. -/
def ReadsAs {α : Type} (r : Reader α) (B : List Bool) (R : List Cell) (P : α → Prop) : Prop :=
  ∀ (s : Slice) (B' : List Bool) (R' : List Cell) (v : α) (s' : Slice), Rem s (B ++ B') (R ++ R') →
    r s = some (v, s') → P v ∧ Rem s' B' R'

theorem ReadsAs.bind {α β : Type} {r : Reader α} {k : α → Reader β} {B₁ B₂ : List Bool} {R₁ R₂ : List Cell}
    {P : α → Prop} {Q : β → Prop} (h1 : ReadsAs r B₁ R₁ P) (h2 : ∀ x, P x → ReadsAs (k x) B₂ R₂ Q) :
    ReadsAs (r >>= k) (B₁ ++ B₂) (R₁ ++ R₂) Q := by
  intro s B' R' v s' hs hr
  have e : (r >>= k) s = (r s).bind (fun p => k p.1 p.2) := rfl
  rw [e] at hr
  cases h : r s with
  | none => rw [h] at hr; cases hr
  | some p =>
    rw [h] at hr
    obtain ⟨x, s1⟩ := p
    simp only [List.append_assoc] at hs
    obtain ⟨hP, hs1⟩ := h1 s (B₂ ++ B') (R₂ ++ R') x s1 hs h
    exact h2 x hP s1 B' R' v s' hs1 hr

theorem ReadsAs.ret {α : Type} (a : α) : ReadsAs (Pure.pure a : Reader α) [] [] (· = a) := by
  intro s B' R' v s' hs hr
  have e : (Pure.pure a : Reader α) s = some (a, s) := rfl
  rw [e] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨rfl, by simpa using hs⟩

theorem ReadsAs.mono {α : Type} {r : Reader α} {B : List Bool} {R : List Cell} {P Q : α → Prop}
    (h : ReadsAs r B R P) (hPQ : ∀ x, P x → Q x) : ReadsAs r B R Q := by
  intro s B' R' v s' hs hr
  obtain ⟨hp, hs'⟩ := h s B' R' v s' hs hr
  exact ⟨hPQ v hp, hs'⟩

theorem ReadsAs.bits (B : List Bool) : ReadsAs (Reader.bits B.length) B [] (fun v => v.toList = B) := by
  intro s B' R' v s' hs hr
  unfold Reader.bits at hr
  split at hr
  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp only [Slice.haveBits, decide_eq_true_eq] at hb
    obtain ⟨h1, h2, h3, h4⟩ := hs
    have hl : (s.cell.bits.toList.drop s.bitPos).take B.length = B := by rw [h2]; simp
    refine ⟨?_, ?_, ?_, h3, by simpa using h4⟩
    · simp [Slice.readBits]; exact hl
    · simp [Slice.advanceBits]; omega
    · simp only [Slice.advanceBits]
      rw [← List.drop_drop, h2]; simp
  · cases hr

theorem ReadsAs.ref (c : Cell) : ReadsAs Reader.ref [] [c] (· = c) := by
  intro s B' R' v s' hs hr
  unfold Reader.ref at hr
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have hlen : s.refPos < s.cell.refs.size := by
    have := congrArg List.length h4; simp at this; omega
  rw [if_pos (by simp [Slice.haveRefs]; omega)] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  rw [List.drop_eq_getElem_cons (by simp; omega)] at h4
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h4
  refine ⟨?_, h1, by simpa using h2, by simp; omega, by simpa using h4.2⟩
  rw [getElem!_pos s.cell.refs s.refPos hlen]
  simpa using h4.1

end TvmLean.Tx

namespace TvmLean.Tx

theorem ReadsAs.congr {α : Type} {r : Reader α} {B B' : List Bool} {R R' : List Cell} {P : α → Prop}
    (h : ReadsAs r B R P) (hB : B = B') (hR : R = R') : ReadsAs r B' R' P := hB ▸ hR ▸ h

theorem ReadsAs.fail {α : Type} (B : List Bool) (R : List Cell) (P : α → Prop) :
    ReadsAs (Reader.fail : Reader α) B R P := by
  intro s B' R' v s' _ hr
  cases hr

theorem ReadsAs.ite {α : Type} {c : Prop} [Decidable c] {a b : Reader α} {B : List Bool} {R : List Cell}
    {P : α → Prop} (ha : c → ReadsAs a B R P) (hb : ¬c → ReadsAs b B R P) :
    ReadsAs (if c then a else b) B R P := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem ReadsAs.bits' (B : List Bool) (n : Nat) (hn : B.length = n) :
    ReadsAs (Reader.bits n) B [] (fun v => v.toList = B) := hn ▸ ReadsAs.bits B

theorem natToBits_length (x n : Nat) : (natToBits x n).toList.length = n := by
  simp [natToBits_size]

theorem ReadsAs.uint (x n : Nat) : ReadsAs (Reader.uint n) (natToBits x n).toList [] (· = x % 2 ^ n) := by
  have h := ReadsAs.bind (k := fun b => (Pure.pure (bitsToNat b) : Reader Nat)) (B₂ := []) (R₂ := [])
    (Q := (· = x % 2 ^ n)) (ReadsAs.bits' (natToBits x n).toList n (natToBits_length x n))
    (fun b hb => (ReadsAs.ret _).mono (fun y hy => by
      subst hy
      have : b = natToBits x n := Array.toList_inj.mp hb
      rw [this, bitsToNat_natToBits]))
  simpa using h

theorem ReadsAs.uint_of_lt {x n : Nat} (hx : x < 2 ^ n) :
    ReadsAs (Reader.uint n) (natToBits x n).toList [] (· = x) :=
  (ReadsAs.uint x n).mono fun y hy => by rw [hy, Nat.mod_eq_of_lt hx]

theorem ReadsAs.bool (b : Bool) : ReadsAs Reader.bool [b] [] (· = b) := by
  have h := ReadsAs.bind (k := fun v => (Pure.pure v[0]! : Reader Bool)) (B₂ := []) (R₂ := [])
    (Q := (· = b)) (ReadsAs.bits' [b] 1 rfl)
    (fun v hv => (ReadsAs.ret _).mono (fun y hy => by
      subst hy
      have : v = #[b] := Array.toList_inj.mp hv
      rw [this]; rfl))
  simpa using h

end TvmLean.Tx

namespace TvmLean.Tx

theorem ReadsAs.maybe_none {α : Type} (r : Reader α) : ReadsAs (Reader.maybe r) [false] [] (· = none) := by
  unfold Reader.maybe
  have h := ReadsAs.bind (k := fun b => if b = true then (do return some (← r)) else (Pure.pure none : Reader (Option α)))
    (B₂ := []) (R₂ := []) (Q := (· = none)) (ReadsAs.bool false)
    (fun b hb => by subst hb; simpa using ReadsAs.ret (none : Option α))
  simpa using h

theorem ReadsAs.maybe_some {α : Type} {r : Reader α} {B : List Bool} {R : List Cell} {P : α → Prop}
    (h : ReadsAs r B R P) : ReadsAs (Reader.maybe r) (true :: B) R (fun v => ∃ x, v = some x ∧ P x) := by
  unfold Reader.maybe
  have h2 := ReadsAs.bind (k := fun b => if b = true then (do return some (← r)) else (Pure.pure none : Reader (Option α)))
    (B₂ := B) (R₂ := R) (Q := fun v => ∃ x, v = some x ∧ P x) (ReadsAs.bool true)
    (fun b hb => by
      subst hb
      simp only [if_true]
      have h3 := ReadsAs.bind (k := fun x => (Pure.pure (some x) : Reader (Option α))) (B₂ := []) (R₂ := [])
        (Q := fun v => ∃ x, v = some x ∧ P x) h (fun x hx => (ReadsAs.ret _).mono fun y hy => ⟨x, hy, hx⟩)
      simpa using h3)
  simpa using h2

/-- The encoding of `Maybe ^Cell` (`W.maybeRef`): its bits and its references. -/
def maybeRefBits (c : Option Cell) : List Bool := [c.isSome]
def maybeRefRefs (c : Option Cell) : List Cell := c.toList

theorem ReadsAs.maybeRef (c : Option Cell) :
    ReadsAs (Reader.maybe Reader.ref) (maybeRefBits c) (maybeRefRefs c) (· = c) := by
  cases c with
  | none => exact ReadsAs.maybe_none _
  | some c =>
    exact ((ReadsAs.maybe_some (ReadsAs.ref c)).mono fun v ⟨x, hv, hx⟩ => by subst hx; exact hv).congr
      rfl rfl

theorem W.maybeRef_bits (w : W) (c : Option Cell) : (w.maybeRef c).bits.toList = w.bits.toList ++ maybeRefBits c := by
  cases c <;> simp [W.maybeRef, W.bool, W.ref, maybeRefBits]

theorem W.maybeRef_refs (w : W) (c : Option Cell) : (w.maybeRef c).refs.toList = w.refs.toList ++ maybeRefRefs c := by
  cases c <;> simp [W.maybeRef, W.bool, W.ref, maybeRefRefs]

/-- The length written for `VarUInteger n` (`W.varUInt`). -/
def varLen (v : Nat) : Nat := if v = 0 then 0 else (v.log2 + 8) / 8

theorem lt_pow_varLen (v : Nat) : v < 2 ^ (8 * varLen v) := by
  unfold varLen
  split
  · subst_vars; simp
  · rename_i h
    have h1 : v < 2 ^ (v.log2 + 1) := Nat.lt_log2_self
    have h2 : v.log2 + 1 ≤ 8 * ((v.log2 + 8) / 8) := by omega
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)

theorem varLen_lt {v n : Nat} (hv : v < 2 ^ (8 * (n - 1))) (hn : 1 ≤ n) : varLen v < n := by
  unfold varLen
  split
  · omega
  · rename_i h
    have : v.log2 < 8 * (n - 1) := (Nat.log2_lt h).mpr hv
    omega

theorem W.varUInt_bits (w : W) (v n : Nat) :
    (w.varUInt v n).bits.toList =
      w.bits.toList ++ (natToBits (varLen v) (n - 1).log2.succ).toList ++ (natToBits v (8 * varLen v)).toList := by
  simp [W.varUInt, W.uint, varLen]

theorem W.varUInt_refs (w : W) (v n : Nat) : (w.varUInt v n).refs = w.refs := rfl

theorem ReadsAs.lessThan {len n : Nat} (h : len < n) :
    ReadsAs (Reader.lessThan n) (natToBits len (n - 1).log2.succ).toList [] (· = len) := by
  have hk : len < 2 ^ (n - 1).log2.succ := by
    have : n - 1 < 2 ^ ((n - 1).log2 + 1) := Nat.lt_log2_self
    simp only [Nat.succ_eq_add_one]
    omega
  unfold Reader.lessThan
  have h2 := ReadsAs.bind (k := fun v => if v < n then (Pure.pure v : Reader Nat) else Reader.fail) (B₂ := [])
    (R₂ := []) (Q := (· = len)) (ReadsAs.uint_of_lt hk)
    (fun v hv => by
      subst hv
      exact ReadsAs.ite (fun _ => ReadsAs.ret _) (fun _ => ReadsAs.fail _ _ _))
  simpa using h2

theorem ReadsAs.varUInt {v n : Nat} (hv : v < 2 ^ (8 * (n - 1))) (hn : 1 ≤ n) :
    ReadsAs (Reader.varUInt n) ((natToBits (varLen v) (n - 1).log2.succ).toList ++ (natToBits v (8 * varLen v)).toList)
      [] (· = v) := by
  unfold Reader.varUInt
  have h2 := ReadsAs.bind (k := fun len => Reader.uint (8 * len)) (R₁ := []) (R₂ := []) (Q := (· = v))
    (ReadsAs.lessThan (varLen_lt hv hn))
    (fun len hl => by subst hl; exact ReadsAs.uint_of_lt (lt_pow_varLen v))
  simpa using h2

theorem ReadsAs.varUIntStrict {v n : Nat} (hv : v < 2 ^ (8 * (n - 1))) (hn : 1 ≤ n) :
    ReadsAs (Reader.varUIntStrict n)
      ((natToBits (varLen v) (n - 1).log2.succ).toList ++ (natToBits v (8 * varLen v)).toList) [] (· = v) := by
  unfold Reader.varUIntStrict
  have h2 := ReadsAs.bind
    (k := fun len => (do
      let v ← Reader.uint (8 * len)
      if len > 0 && v >>> (8 * len - 8) == 0 then Reader.fail else return v : Reader Nat))
    (R₁ := []) (R₂ := []) (B₂ := (natToBits v (8 * varLen v)).toList) (Q := (· = v))
    (ReadsAs.lessThan (varLen_lt hv hn))
    (fun len hl => by
      subst hl
      have h3 := ReadsAs.bind
        (k := fun x => (if varLen v > 0 && x >>> (8 * varLen v - 8) == 0 then Reader.fail else Pure.pure x : Reader Nat))
        (R₁ := []) (R₂ := []) (B₂ := []) (Q := (· = v)) (ReadsAs.uint_of_lt (lt_pow_varLen v))
        (fun x hx => by
          subst hx
          exact ReadsAs.ite (fun _ => ReadsAs.fail _ _ _) (fun _ => ReadsAs.ret _))
      simpa using h3)
  simpa using h2

end TvmLean.Tx

namespace TvmLean

theorem natToBits_testBit_eq {m n k : Nat} (h : ∀ i < k, m.testBit i = n.testBit i) :
    natToBits m k = natToBits n k := by
  apply Array.ext
  · simp [natToBits_size]
  · intro i h1 h2
    simp [natToBits] at h1 ⊢
    exact h _ (by omega)

theorem natToBits_mod (n k : Nat) : natToBits (n % 2 ^ k) k = natToBits n k :=
  natToBits_testBit_eq fun i hi => by simp [Nat.testBit_mod_two_pow, hi]

theorem natToBits_append (a b j k : Nat) (hb : b < 2 ^ k) :
    natToBits (a * 2 ^ k + b) (j + k) = natToBits a j ++ natToBits b k := by
  induction j with
  | zero =>
    simp only [Nat.zero_add]
    rw [← natToBits_mod, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
    simp [natToBits]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega, natToBits_succ, ih, natToBits_succ, Array.append_assoc]
    congr 2
    rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hb]
    simp only [show ¬(j + k < k) by omega, if_false, Nat.add_sub_cancel]

end TvmLean

namespace TvmLean.Tx

/-- The bits of `VarUInteger n` as `W.varUInt` writes `v`. -/
def varEnc (v n : Nat) : List Bool :=
  (natToBits (varLen v) (n - 1).log2.succ).toList ++ (natToBits v (8 * varLen v)).toList

theorem W.varUInt_enc (w : W) (v n : Nat) : (w.varUInt v n).bits.toList = w.bits.toList ++ varEnc v n := by
  rw [W.varUInt_bits]; simp [varEnc]

theorem ReadsAs.varUInt' {v n : Nat} (hv : v < 2 ^ (8 * (n - 1))) (hn : 1 ≤ n) :
    ReadsAs (Reader.varUInt n) (varEnc v n) [] (· = v) := ReadsAs.varUInt hv hn

theorem ReadsAs.varUIntStrict' {v n : Nat} (hv : v < 2 ^ (8 * (n - 1))) (hn : 1 ≤ n) :
    ReadsAs (Reader.varUIntStrict n) (varEnc v n) [] (· = v) := ReadsAs.varUIntStrict hv hn

theorem ReadsAs.grams {v : Nat} (hv : v < 2 ^ 120) : ReadsAs Reader.grams (varEnc v 16) [] (· = v) :=
  ReadsAs.varUInt' hv (by decide)

theorem ReadsAs.gramsStrict {v : Nat} (hv : v < 2 ^ 120) :
    ReadsAs Reader.gramsStrict (varEnc v 16) [] (· = v) :=
  ReadsAs.varUIntStrict' hv (by decide)

theorem ReadsAs.peek : ReadsAs Reader.peek [] [] (fun _ => True) := by
  intro s B' R' v s' hs hr
  simp only [Reader.peek, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨trivial, by simpa using hs⟩

theorem ReadsAs.currencies {g : Nat} (hg : g < 2 ^ 120) (e : Option Cell) :
    ReadsAs Reader.currencies (varEnc g 16 ++ maybeRefBits e) (maybeRefRefs e)
      (fun c => c.grams = g ∧ c.extra = e) := by
  unfold Reader.currencies
  refine (ReadsAs.bind (B₁ := []) (R₁ := []) (B₂ := varEnc g 16 ++ maybeRefBits e) (R₂ := maybeRefRefs e)
    (P := fun _ => True) ReadsAs.peek fun s _ => ?_).congr (by simp) (by simp)
  refine (ReadsAs.bind (B₂ := maybeRefBits e) (R₁ := []) (R₂ := maybeRefRefs e) (ReadsAs.grams hg)
    fun g' hg' => ?_).congr rfl (by simp)
  subst hg'
  refine (ReadsAs.bind (B₂ := []) (R₂ := []) (ReadsAs.maybeRef e) fun e' he' => ?_).congr (by simp) (by simp)
  subst he'
  exact (ReadsAs.ret _).mono fun c hc => by subst hc; exact ⟨rfl, rfl⟩

theorem ReadsAs.int (x n : Nat) : ReadsAs (Reader.int n) (natToBits x n).toList [] (fun _ => True) := by
  unfold Reader.int
  refine (ReadsAs.bind (B₂ := []) (R₁ := []) (R₂ := []) (ReadsAs.uint x n) fun v _ => ?_).congr (by simp) rfl
  exact (ReadsAs.ret _).mono fun _ _ => trivial

end TvmLean.Tx

namespace TvmLean.Tx

theorem ReadsAs.fail_bind {α β : Type} (k : α → Reader β) (B : List Bool) (R : List Cell) (P : β → Prop) :
    ReadsAs (Reader.fail >>= k) B R P := by
  intro s B' R' v s' _ hr
  cases hr

theorem ReadsAs.pure_bind {α β : Type} (a : α) {k : α → Reader β} {B : List Bool} {R : List Cell} {P : β → Prop}
    (h : ReadsAs (k a) B R P) : ReadsAs (Pure.pure a >>= k) B R P := h

theorem ReadsAs.map {α β : Type} {r : Reader α} {f : α → β} {B : List Bool} {R : List Cell} {P : α → Prop}
    (h : ReadsAs r B R P) : ReadsAs (f <$> r) B R (fun y => ∃ x, P x ∧ y = f x) := by
  intro s B' R' v s' hs hr
  cases h2 : r s with
  | none => simp [Functor.map, StateT.map, h2] at hr
  | some p =>
    simp only [Functor.map, StateT.map, h2, pure] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨hp, hs'⟩ := h s B' R' p.1 p.2 hs h2
    exact ⟨⟨p.1, hp, rfl⟩, hs'⟩

theorem W.cell_bits (w : W) : w.cell.bits = w.bits := rfl
theorem W.cell_refs (w : W) : w.cell.refs = w.refs := rfl

/-- The anycast field as `Account.mkAddr` writes it. -/
def anyEnc : Option BitString → List Bool
  | some p => true :: (natToBits p.size 5).toList ++ p.toList
  | none => [false]

theorem mkAddr_bits (wc : Int) (any : Option BitString) (a : BitString) (lim : Int) :
    (Account.mkAddr wc any a lim).bits.toList =
      if -128 ≤ wc ∧ wc < lim then
        (natToBits 2 2).toList ++ anyEnc any ++
          (natToBits (if wc < 0 then (2 ^ 8 - wc.natAbs) % 2 ^ 8 else wc.toNat) 8).toList ++ a.toList
      else
        (natToBits 3 2).toList ++ anyEnc any ++ (natToBits 256 9).toList ++
          (natToBits (if wc < 0 then (2 ^ 32 - wc.natAbs) % 2 ^ 32 else wc.toNat) 32).toList ++ a.toList := by
  unfold Account.mkAddr
  cases any <;> by_cases h : -128 ≤ wc ∧ wc < lim <;>
    simp [h, W.cell, Cell.mkOrdinary, W.uint, W.bool, W.bitStr, W.int, anyEnc]

theorem mkAddr_refs (wc : Int) (any : Option BitString) (a : BitString) (lim : Int) :
    (Account.mkAddr wc any a lim).refs = #[] := by
  unfold Account.mkAddr
  cases any <;> by_cases h : -128 ≤ wc ∧ wc < lim <;>
    simp [h, W.cell, Cell.mkOrdinary, W.uint, W.bool, W.bitStr, W.int]

theorem ReadsAs.addrStd_mkAddr (wc : Int) (any : Option BitString) (a : BitString) (lim : Int)
    (ha : a.size = 256) (hp : ∀ p, any = some p → p.size < 32) :
    ReadsAs Account.Reader.addrStd (Account.mkAddr wc any a lim).bits.toList [] (fun _ => True) := by
  rw [mkAddr_bits]
  unfold Account.Reader.addrStd
  dsimp only
  split
  · -- `addr_std`
    rename_i hstd
    refine (ReadsAs.bind (B₂ := anyEnc any ++ (natToBits (if wc < 0 then (2 ^ 8 - wc.natAbs) % 2 ^ 8 else wc.toNat) 8).toList ++ a.toList)
      (R₁ := []) (R₂ := []) (ReadsAs.uint_of_lt (x := 2) (n := 2) (by decide)) fun t ht => ?_).congr
      (by simp) rfl
    subst ht
    rw [if_neg (by decide)]
    refine ReadsAs.pure_bind () ?_
    -- the anycast prefix
    have hany : ReadsAs (Reader.maybe (do
        let depth ← Reader.uint 5
        if depth = 0 ∨ depth > 30 then do
          Reader.fail
          Reader.bits depth
        else do
          pure PUnit.unit
          Reader.bits depth)) (anyEnc any) [] (fun _ => True) := by
      cases any with
      | none => exact (ReadsAs.maybe_none _).mono fun _ _ => trivial
      | some p =>
        have hps := hp p rfl
        have hin : ReadsAs (do
            let depth ← Reader.uint 5
            if depth = 0 ∨ depth > 30 then do
              Reader.fail
              Reader.bits depth
            else do
              pure PUnit.unit
              Reader.bits depth) ((natToBits p.size 5).toList ++ p.toList) [] (fun _ => True) := by
          refine (ReadsAs.bind (B₂ := p.toList) (R₁ := []) (R₂ := []) (P := (· = p.size))
            (ReadsAs.uint_of_lt hps) fun d hd => ?_).congr rfl rfl
          subst hd
          refine ReadsAs.ite (fun _ => ReadsAs.fail_bind _ _ _ _) (fun _ => ReadsAs.pure_bind () ?_)
          exact (ReadsAs.bits' p.toList p.size (by simp)).mono fun _ _ => trivial
        exact ((ReadsAs.maybe_some hin).mono fun _ _ => trivial).congr (by simp [anyEnc]) rfl
    refine (ReadsAs.bind (B₂ := (natToBits (if wc < 0 then (2 ^ 8 - wc.natAbs) % 2 ^ 8 else wc.toNat) 8).toList ++
      a.toList) (R₁ := []) (R₂ := []) hany fun pfx _ => ?_).congr (by simp) rfl
    refine (ReadsAs.bind (B₂ := a.toList) (R₁ := []) (R₂ := []) (ReadsAs.int _ 8) fun x _ => ?_).congr rfl rfl
    refine (ReadsAs.bind (B₂ := []) (R₁ := []) (R₂ := []) (ReadsAs.bits' a.toList 256 (by simp [ha]))
      fun y _ => ?_).congr (by simp) rfl
    exact (ReadsAs.ret _).mono fun _ _ => trivial
  · -- `addr_var`: the tag is not 2
    refine (ReadsAs.bind (R₁ := []) (R₂ := []) (B₂ := anyEnc any ++ (natToBits 256 9).toList ++
        (natToBits (if wc < 0 then (2 ^ 32 - wc.natAbs) % 2 ^ 32 else wc.toNat) 32).toList ++ a.toList) (ReadsAs.uint_of_lt (x := 3) (n := 2) (by decide)) fun t ht => ?_).congr
      (by simp) rfl
    subst ht
    rw [if_pos (by decide)]
    exact ReadsAs.fail_bind _ _ _ _

end TvmLean.Tx

namespace TvmLean.Tx

/-! ## Writers as lists of bits -/

theorem W.uint_bits (w : W) (v n : Nat) : (w.uint v n).bits.toList = w.bits.toList ++ (natToBits v n).toList := by
  simp [W.uint]

theorem W.bool_bits (w : W) (b : Bool) : (w.bool b).bits.toList = w.bits.toList ++ [b] := by
  simp [W.bool]

theorem W.bitStr_bits (w : W) (bs : BitString) : (w.bitStr bs).bits.toList = w.bits.toList ++ bs.toList := by
  simp [W.bitStr]

theorem W.slice_bits (w : W) (c : Cell) : (w.slice (Slice.ofCell c)).bits.toList = w.bits.toList ++ c.bits.toList := by
  simp [W.slice, Slice.ofCell, Slice.readBits, Slice.bitsRemaining]

theorem W.slice_refs (w : W) (c : Cell) : (w.slice (Slice.ofCell c)).refs.toList = w.refs.toList ++ c.refs.toList := by
  simp [W.slice, Slice.ofCell]

/-- The `dict_hash` field of `StorageInfo` as `Tx.computeState` writes it. -/
def dictHashEnc : Option BitString → List Bool
  | some h => (natToBits 1 3).toList ++ h.toList
  | none => (natToBits 0 3).toList

/-- `due_payment:(Maybe Grams)` as `Tx.computeState` writes it. -/
def dueEnc (due : Nat) : List Bool := if due ≠ 0 then true :: varEnc due 16 else [false]

/-- `StorageInfo` (the storage used, the dict hash, the last paid time and the due payment) as
`Tx.computeState` writes it. -/
def siEnc (used : StorageUsed) (dh : Option BitString) (lastPaid due : Nat) : List Bool :=
  varEnc used.cells 7 ++ varEnc used.bits 7 ++ dictHashEnc dh ++ (natToBits lastPaid 32).toList ++ dueEnc due

theorem ReadsAs.storageInfo {used : StorageUsed} {dh : Option BitString} {lastPaid due : Nat}
    (hc : used.cells < 2 ^ 48) (hb : used.bits < 2 ^ 48) (hdh : ∀ h, dh = some h → h.size = 256)
    (hdue : due < 2 ^ 120) :
    ReadsAs Account.Reader.storageInfo (siEnc used dh lastPaid due) [] (fun _ => True) := by
  unfold Account.Reader.storageInfo
  refine (ReadsAs.bind (B₂ := varEnc used.bits 7 ++ dictHashEnc dh ++ (natToBits lastPaid 32).toList ++ dueEnc due)
    (R₁ := []) (R₂ := []) (ReadsAs.varUIntStrict' (n := 7) hc (by decide)) fun x _ => ?_).congr
    (by simp [siEnc]) rfl
  refine (ReadsAs.bind (B₂ := dictHashEnc dh ++ (natToBits lastPaid 32).toList ++ dueEnc due)
    (R₁ := []) (R₂ := []) (ReadsAs.varUIntStrict' (n := 7) hb (by decide)) fun y _ => ?_).congr
    (by simp) rfl
  -- the reads after the dict hash
  have hrest : ∀ (z : Option BitString),
      ReadsAs (do
        let lastPaid ← Reader.uint 32
        let due ← Reader.gramsStrict.maybe
        pure (({ cells := x, bits := y } : StorageUsed), z, lastPaid, due.getD 0))
        ((natToBits lastPaid 32).toList ++ dueEnc due) [] (fun _ => True) := by
    intro z
    refine (ReadsAs.bind (B₂ := dueEnc due) (R₁ := []) (R₂ := []) (ReadsAs.uint lastPaid 32) fun l _ => ?_).congr
      rfl rfl
    have hdue' : ReadsAs Reader.gramsStrict.maybe (dueEnc due) [] (fun _ => True) := by
      unfold dueEnc
      split
      · exact ((ReadsAs.maybe_some (ReadsAs.gramsStrict hdue)).mono fun _ _ => trivial).congr rfl rfl
      · exact (ReadsAs.maybe_none _).mono fun _ _ => trivial
    refine (ReadsAs.bind (B₂ := []) (R₁ := []) (R₂ := []) hdue' fun d _ => ?_).congr (by simp) rfl
    exact (ReadsAs.ret _).mono fun _ _ => trivial
  cases dh with
  | none =>
    refine (ReadsAs.bind (B₂ := (natToBits lastPaid 32).toList ++ dueEnc due) (R₁ := []) (R₂ := [])
      (ReadsAs.uint_of_lt (x := 0) (n := 3) (by decide)) fun t ht => ?_).congr (by simp [dictHashEnc]) rfl
    subst ht
    rw [if_neg (by decide), if_pos (by decide)]
    exact ReadsAs.pure_bind none (hrest none)
  | some h =>
    have hh := hdh h rfl
    refine (ReadsAs.bind (B₂ := h.toList ++ (natToBits lastPaid 32).toList ++ dueEnc due) (R₁ := []) (R₂ := [])
      (ReadsAs.uint_of_lt (x := 1) (n := 3) (by decide)) fun t ht => ?_).congr (by simp [dictHashEnc]) rfl
    subst ht
    rw [if_pos (by decide)]
    refine (ReadsAs.bind (B₂ := (natToBits lastPaid 32).toList ++ dueEnc due) (R₁ := []) (R₂ := [])
      (ReadsAs.map (f := some) (ReadsAs.bits' h.toList 256 (by simp [hh]))) fun z _ => ?_).congr (by simp) rfl
    exact hrest z

end TvmLean.Tx

namespace TvmLean.Tx

/-! ## The `StateInit` of an active account -/

/-- `split_depth:(Maybe (## 5))` as `Tx.computeState` writes it (after the tag of `account_active`). -/
def splitEnc (fpl : Nat) : List Bool := if fpl ≠ 0 then true :: (natToBits fpl 5).toList else [false]

/-- `special:(Maybe TickTock)` as `Tx.computeState` writes it. -/
def ttEnc (tick tock : Bool) : List Bool := if tick || tock then [true, tick, tock] else [false]

theorem natToBits_fpl {fpl : Nat} (h : fpl < 32) :
    (natToBits (fpl + 96) 7).toList = true :: true :: (natToBits fpl 5).toList := by
  have := natToBits_append 3 fpl 2 5 h
  rw [show 3 * 2 ^ 5 + fpl = fpl + 96 by omega] at this
  rw [this]
  simp [natToBits]
  decide

theorem ReadsAs.pair_bool (b c : Bool) :
    ReadsAs (do return (← Reader.bool, ← Reader.bool)) [b, c] [] (fun _ => True) := by
  refine (ReadsAs.bind (B₂ := [c]) (R₁ := []) (R₂ := []) (ReadsAs.bool b) fun x _ => ?_).congr rfl rfl
  refine (ReadsAs.bind (B₂ := []) (R₁ := []) (R₂ := []) (ReadsAs.bool c) fun y _ => ?_).congr rfl rfl
  exact (ReadsAs.ret _).mono fun _ _ => trivial

theorem ReadsAs.stateInit (fpl : Nat) (tick tock : Bool) (code data lib : Option Cell) :
    ReadsAs Account.Reader.stateInit
      (splitEnc fpl ++ ttEnc tick tock ++ maybeRefBits code ++ maybeRefBits data ++ maybeRefBits lib)
      (maybeRefRefs code ++ maybeRefRefs data ++ maybeRefRefs lib)
      (fun si => si.code = code ∧ si.data = data ∧ si.library = lib) := by
  unfold Account.Reader.stateInit
  have hsplit : ReadsAs (Reader.maybe (Reader.uint 5)) (splitEnc fpl) [] (fun _ => True) := by
    unfold splitEnc
    split
    · exact ((ReadsAs.maybe_some (ReadsAs.uint fpl 5)).mono fun _ _ => trivial).congr rfl rfl
    · exact (ReadsAs.maybe_none _).mono fun _ _ => trivial
  have htt : ReadsAs (Reader.maybe (do return (← Reader.bool, ← Reader.bool))) (ttEnc tick tock) []
      (fun _ => True) := by
    unfold ttEnc
    split
    · exact ((ReadsAs.maybe_some (ReadsAs.pair_bool tick tock)).mono fun _ _ => trivial).congr rfl rfl
    · exact (ReadsAs.maybe_none _).mono fun _ _ => trivial
  refine (ReadsAs.bind (B₂ := ttEnc tick tock ++ maybeRefBits code ++ maybeRefBits data ++ maybeRefBits lib)
    (R₁ := []) (R₂ := maybeRefRefs code ++ maybeRefRefs data ++ maybeRefRefs lib) hsplit fun x _ => ?_).congr
    (by simp) (by simp)
  refine (ReadsAs.bind (B₂ := maybeRefBits code ++ maybeRefBits data ++ maybeRefBits lib)
    (R₁ := []) (R₂ := maybeRefRefs code ++ maybeRefRefs data ++ maybeRefRefs lib) htt fun y _ => ?_).congr
    (by simp) (by simp)
  refine (ReadsAs.bind (B₂ := maybeRefBits data ++ maybeRefBits lib) (R₂ := maybeRefRefs data ++ maybeRefRefs lib)
    (ReadsAs.maybeRef code) fun c hc => ?_).congr (by simp) (by simp)
  refine (ReadsAs.bind (B₂ := maybeRefBits lib) (R₂ := maybeRefRefs lib)
    (ReadsAs.maybeRef data) fun d hd => ?_).congr (by simp) (by simp)
  refine (ReadsAs.bind (B₂ := []) (R₂ := []) (ReadsAs.maybeRef lib) fun l hl => ?_).congr (by simp) (by simp)
  exact (ReadsAs.ret _).mono fun si hsi => by subst hsi; exact ⟨hc, hd, hl⟩

end TvmLean.Tx

namespace TvmLean.Tx

/-! ## The account `Tx.computeState` writes -/

/-! `Tx.computeState` in pieces: `csAdjust` (the status of an empty uninitialized or deleted
account), `csState` (the transaction as written and the storage), `Tx.storageStat` (the storage
statistics and the dict hash), `preW` (the bits before the storage). `computeState_pieces`: `Tx.computeState`
is these pieces put together (definitionally). -/

/-- The first step of `Tx.computeState`: an empty uninitialized account is not created, an account
deleted with a balance left stays uninitialized. -/
def csAdjust (t : Tx) : Tx :=
  let zero := t.balance = 0 && t.balanceExtra.isNone
  let t := if t.accStatus == .uninit && !t.wasActivated && zero then { t with accStatus := .nonexist, wasCreated := false } else t
  if t.accStatus == .deleted && !zero then { t with accStatus := .uninit } else t

/-- The fixed prefix length `Tx.computeState` writes. -/
def csFpl (t : Tx) : Nat := if t.gv ≥ 10 then t.newFixedPrefixLength else t.account.addrRewriteLength

/-- The tick-tock flags `Tx.computeState` writes (`tick` 2, `tock` 1). -/
def csTT (t : Tx) : Nat := (if t.newTick then 2 else 0) + (if t.newTock then 1 else 0)

/-- The beginning of the storage `Tx.computeState` writes: the last transaction and the balance. -/
def csW (t : Tx) : W := (({} : W).uint t.endLt 64).currencies { grams := t.balance, extra := t.balanceExtra }

/-- The state hash of a frozen account as `Tx.computeState` writes it: of its `StateInit`, if it was
frozen in this transaction. -/
def csFrozenHash (t : Tx) : BitString :=
  let w : W := if csFpl t ≠ 0 then ({} : W).uint (csFpl t + 32) 6 else ({} : W).uint 0 1
  let w := if csTT t ≠ 0 then w.uint (csTT t ||| 4) 3 else w.uint 0 1
  if t.wasFrozen then bytesToBits (((w.maybeRef t.newCode).maybeRef t.newData).maybeRef t.newLibrary).cell.hashBytes
  else t.frozenHash

/-- The transaction as `Tx.computeState` writes it and the builder of its storage
(`AccountStorage`). -/
def csState (t : Tx) : Tx × W :=
  let fpl := csFpl t
  let w := csW t
  if t.accStatus == .uninit then (t, w.uint 0 2)
  else if t.accStatus == .frozen then
    let frozenHash := csFrozenHash t
    let t := { t with frozenHash, newCode := none, newData := none, newLibrary := none }
    if frozenHash == t.account.addrOrig then
      ({ t with accStatus := if t.gv ≥ 13 then .uninit else t.accStatus }, w.uint 0 2)
    else (t, (w.uint 1 2).bitStr frozenHash)
  else
    let w := if fpl ≠ 0 then w.uint (fpl + 96) 7 else w.uint 2 2
    let w := if csTT t ≠ 0 then w.uint (csTT t ||| 4) 3 else w.uint 0 1
    (t, ((w.maybeRef t.newCode).maybeRef t.newData).maybeRef t.newLibrary)

/-- The address `Tx.computeState` writes (the version of `t₀`, the transaction before `csState`). -/
def csAddr (t₀ t : Tx) : Cell := if t₀.gv ≥ 10 then t.myAddr else t.account.myAddr

/-- The bits before the storage of an account (`account$1 addr:MsgAddressInt storage_stat:StorageInfo`),
as `Tx.computeState` writes them. -/
def preW (addr : Cell) (used : StorageUsed) (dictHash : Option BitString) (lastPaid due : Nat) : W :=
  let w : W := ({} : W).bool true |>.slice (Slice.ofCell addr)
  let w := (w.uint7 used.cells).uint7 used.bits
  let w := match dictHash with
    | some h => (w.uint 1 3).bitStr h
    | none => w.uint 0 3
  let w := w.uint lastPaid 32
  if due ≠ 0 then (w.bool true).grams due else w.bool false

set_option maxHeartbeats 2000000 in
/-- `Tx.computeState` in pieces (definitionally the same). -/
theorem computeState_pieces (t : Tx) (sl : SizeLimits) :
    t.computeState sl = (do
      let t := csAdjust t
      if t.accStatus == .nonexist || t.accStatus == .deleted then return (t, (W.bool {} false).cell)
      if t.balance ≥ 2 ^ 120 then none
      let (t', w) := csState t
      let (used, dictHash) ← t'.storageStat sl w.cell
      if used.cells ≥ 2 ^ 48 || used.bits ≥ 2 ^ 48 then none
      if t'.duePayment ≥ 2 ^ 120 then none
      return (t', ((preW (csAddr t t') used dictHash t'.lastPaid t'.duePayment).slice
        (Slice.ofCell w.cell)).cell)) := by
  unfold Tx.computeState csAdjust csState csAddr preW csFpl csTT csW csFrozenHash
  rfl

/-- What `Tx.computeState` writes, when it writes an account (not `account_none`): the transaction
as written, the address, the storage (`AccountStorage`: last transaction, balance, state), the
storage statistics and the dict hash, the fixed prefix length. -/
structure StateParts where
  t : Tx
  addr : Cell
  storage : Cell
  used : StorageUsed
  dictHash : Option BitString
  fpl : Nat

/-- The parts of the account `Tx.computeState` writes; `none` for `account_none` (and where the
update of the storage statistics wraps around). -/
def Tx.computeStateParts (t : Tx) (sl : SizeLimits) : Option StateParts :=
  let t := csAdjust t
  if t.accStatus == .nonexist || t.accStatus == .deleted then none
  else
    let (t', w) := csState t
    match t'.storageStat sl w.cell with
    | none => none
    | some (used, dictHash) =>
      some { t := t', addr := csAddr t t', storage := w.cell, used, dictHash, fpl := csFpl t }

/-- `Tx.computeState` succeeds with the account of its parts, whose balance, storage statistics and
due payment fit their fields (C++ fails otherwise, and so does the model). -/
theorem computeState_some {t : Tx} {sl : SizeLimits} {p : StateParts} (hp : t.computeStateParts sl = some p)
    {t' : Tx} {acc : Cell} (h : t.computeState sl = some (t', acc)) :
    t' = p.t ∧ acc = ((preW p.addr p.used p.dictHash p.t.lastPaid p.t.duePayment).slice
      (Slice.ofCell p.storage)).cell ∧
      (csAdjust t).balance < 2 ^ 120 ∧ p.used.cells < 2 ^ 48 ∧ p.used.bits < 2 ^ 48 ∧
      p.t.duePayment < 2 ^ 120 := by
  rw [computeState_pieces] at h
  revert hp h
  unfold Tx.computeStateParts
  dsimp only
  split
  · intro hp; cases hp
  · generalize csState (csAdjust t) = q
    obtain ⟨t1, w⟩ := q
    dsimp only
    generalize t1.storageStat sl w.cell = r
    cases r with
    | none => intro hp; cases hp
    | some r =>
      obtain ⟨used, dh⟩ := r
      intro hp h
      cases hp
      simp only [bind, Option.bind] at h
      split at h
      · cases h
      · rename_i hbal
        split at h
        · cases h
        · rename_i hcb
          split at h
          · cases h
          · rename_i hdue
            cases h
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hcb
            exact ⟨rfl, rfl, Nat.lt_of_not_le hbal, hcb.1, hcb.2, Nat.lt_of_not_le hdue⟩

theorem computeState_none {t : Tx} {sl : SizeLimits} (hp : t.computeStateParts sl = none) {t' : Tx} {acc : Cell}
    (h : t.computeState sl = some (t', acc)) : acc = (W.bool {} false).cell := by
  rw [computeState_pieces] at h
  revert hp h
  unfold Tx.computeStateParts
  dsimp only
  split
  · intro _ h
    simp only [pure] at h
    cases h
    rfl
  · generalize csState (csAdjust t) = q
    obtain ⟨t1, w⟩ := q
    dsimp only
    generalize t1.storageStat sl w.cell = r
    cases r with
    | some r => intro hp; cases hp
    | none =>
      intro _ h
      simp only [bind, Option.bind] at h
      split at h
      · cases h
      · cases h

end TvmLean.Tx

namespace TvmLean.Tx

/-! ## The storage `Tx.computeState` writes -/

theorem natToBits_two_two : (natToBits 2 2).toList = [true, false] := by simp [natToBits] <;> decide
theorem natToBits_zero_two : (natToBits 0 2).toList = [false, false] := by simp [natToBits] <;> decide
theorem natToBits_one_two : (natToBits 1 2).toList = [false, true] := by simp [natToBits] <;> decide

theorem ttEnc_eq (tick tock : Bool) :
    (if (if tick then 2 else 0) + (if tock then 1 else 0) ≠ 0 then
        (natToBits (((if tick then 2 else 0) + (if tock then 1 else 0)) ||| 4) 3).toList
      else (natToBits 0 1).toList) = ttEnc tick tock := by
  cases tick <;> cases tock <;> simp [natToBits, ttEnc] <;> decide

theorem W.uint_refs (w : W) (v n : Nat) : (w.uint v n).refs = w.refs := rfl
theorem W.bitStr_refs (w : W) (b : BitString) : (w.bitStr b).refs = w.refs := rfl

theorem csW_bits (t : Tx) :
    (csW t).bits.toList = (natToBits t.endLt 64).toList ++ varEnc t.balance 16 ++ maybeRefBits t.balanceExtra := by
  unfold csW
  simp only [W.currencies, W.maybeRef_bits, W.grams, W.varUInt_enc, W.uint_bits]
  simp

theorem csW_refs (t : Tx) : (csW t).refs.toList = maybeRefRefs t.balanceExtra := by
  unfold csW
  simp only [W.currencies, W.maybeRef_refs, W.grams, W.varUInt_refs]
  rfl

theorem tt_bits (w : W) (t : Tx) :
    (if csTT t ≠ 0 then w.uint (csTT t ||| 4) 3 else w.uint 0 1).bits.toList =
      w.bits.toList ++ ttEnc t.newTick t.newTock := by
  rw [← ttEnc_eq]
  unfold csTT
  generalize ((if t.newTick then 2 else 0) + (if t.newTock then 1 else 0)) = n
  split <;> simp [W.uint_bits]

theorem tt_refs (w : W) (t : Tx) :
    (if csTT t ≠ 0 then w.uint (csTT t ||| 4) 3 else w.uint 0 1).refs = w.refs := by
  split <;> rfl

theorem split_bits (w : W) (fpl : Nat) :
    (if fpl ≠ 0 then w.uint (fpl + 96) 7 else w.uint 2 2).bits.toList =
      w.bits.toList ++ (if fpl ≠ 0 then (natToBits (fpl + 96) 7).toList else (natToBits 2 2).toList) := by
  split <;> simp [W.uint_bits]

theorem split_refs (w : W) (fpl : Nat) :
    (if fpl ≠ 0 then w.uint (fpl + 96) 7 else w.uint 2 2).refs = w.refs := by
  split <;> rfl

/-- The fields of the transaction `csState` keeps. -/
theorem csState_fields (t : Tx) :
    (csState t).1.balance = t.balance ∧ (csState t).1.duePayment = t.duePayment ∧
      (csState t).1.lastPaid = t.lastPaid ∧ (csState t).1.gv = t.gv := by
  unfold csState
  dsimp only
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split
    · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The storage `csState` writes: the last transaction, the balance, then the state, which starts
with a one (`account_active`) exactly for an active account. -/
theorem csState_storage (t : Tx) (h : t.accStatus ≠ .nonexist ∧ t.accStatus ≠ .deleted) :
    ∃ S SR, (csState t).2.bits.toList =
        (natToBits t.endLt 64).toList ++ varEnc t.balance 16 ++ maybeRefBits t.balanceExtra ++ S ∧
      (csState t).2.refs.toList = maybeRefRefs t.balanceExtra ++ SR ∧
      ((csState t).1.accStatus = .active → (csState t).1 = t ∧
          S = (if csFpl t ≠ 0 then (natToBits (csFpl t + 96) 7).toList else (natToBits 2 2).toList) ++
            ttEnc t.newTick t.newTock ++ maybeRefBits t.newCode ++ maybeRefBits t.newData ++
            maybeRefBits t.newLibrary ∧
          SR = maybeRefRefs t.newCode ++ maybeRefRefs t.newData ++ maybeRefRefs t.newLibrary) ∧
      ((csState t).1.accStatus ≠ .active → S.head? = some false) := by
  unfold csState
  dsimp only
  split
  · rename_i hu
    refine ⟨[false, false], [], ?_, ?_, ?_, fun _ => rfl⟩
    · simp only [W.uint_bits, csW_bits, natToBits_zero_two]
    · simp only [W.uint_refs, csW_refs, List.append_nil]
    · intro ha; simp at hu; rw [hu] at ha; cases ha
  · split
    · rename_i hf
      split
      · refine ⟨[false, false], [], ?_, ?_, ?_, fun _ => rfl⟩
        · simp only [W.uint_bits, csW_bits, natToBits_zero_two]
        · simp only [W.uint_refs, csW_refs, List.append_nil]
        · intro ha
          simp at hf
          split at ha
          · cases ha
          · rw [hf] at ha; cases ha
      · refine ⟨[false, true] ++ (csFrozenHash t).toList, [], ?_, ?_, ?_, fun _ => rfl⟩
        · simp only [W.bitStr_bits, W.uint_bits, csW_bits, natToBits_one_two, List.append_assoc]
        · simp only [W.bitStr_refs, W.uint_refs, csW_refs, List.append_nil]
        · intro ha
          simp at hf
          rw [hf] at ha; cases ha
    · rename_i hu hf
      refine ⟨_, _, ?_, ?_, fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
      · simp only [W.maybeRef_bits, tt_bits, split_bits, csW_bits, List.append_assoc]
      · simp only [W.maybeRef_refs, tt_refs, split_refs, csW_refs, List.append_assoc]
      · intro ha
        exfalso
        apply ha
        dsimp only
        simp at hu hf
        cases hs : t.accStatus <;>
          first | rfl | exact absurd hs h.1 | exact absurd hs hu | exact absurd hs hf | exact absurd hs h.2

theorem splitEnc_eq {fpl : Nat} (h : fpl < 32) :
    (if fpl ≠ 0 then (natToBits (fpl + 96) 7).toList else (natToBits 2 2).toList) = true :: splitEnc fpl := by
  unfold splitEnc
  split
  · rw [natToBits_fpl h]
  · rw [natToBits_two_two]

/-! ## Slices -/

theorem Rem.readBit0 {s : Slice} {b : Bool} {B : List Bool} {R : List Cell} (h : Rem s (b :: B) R) :
    (s.readBits 1)[0]! = b := by
  obtain ⟨_, h2, _, _⟩ := h
  have e : s.cell.bits.extract s.bitPos (s.bitPos + 1) = #[b] := by
    apply Array.ext'
    rw [Array.toList_extract, List.extract_eq_drop_take, h2]
    simp
  simp only [Slice.readBits, e]
  rfl

theorem Rem.advance1 {s : Slice} {b : Bool} {B : List Bool} {R : List Cell} (h : Rem s (b :: B) R) :
    Rem (s.advanceBits 1) B R := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hl : s.bitPos < s.cell.bits.size := by
    have := congrArg List.length h2
    simp at this
    omega
  refine ⟨by simp [Slice.advanceBits]; omega, ?_, h3, h4⟩
  simp only [Slice.advanceBits]
  rw [← List.drop_drop, h2]
  rfl

theorem Rem.toCellRemaining {s : Slice} {B : List Bool} {R : List Cell} (h : Rem s B R) :
    s.toCellRemaining.bits.toList = B ∧ s.toCellRemaining.refs.toList = R := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Slice.toCellRemaining, Cell.mkOrdinary]
  constructor
  · rw [← h2]; simp only [Array.toList_extract, List.extract_eq_drop_take]
    exact List.take_of_length_le (by simp)
  · rw [← h4]; simp only [Array.toList_extract, List.extract_eq_drop_take]
    exact List.take_of_length_le (by simp)

theorem ReadsAs.runExact {α : Type} {r : Reader α} {B : List Bool} {R : List Cell} {P : α → Prop}
    (h : ReadsAs r B R P) {c : Cell} (hb : c.bits.toList = B) (hr : c.refs.toList = R) {v : α}
    (hv : Reader.runExact r c = some v) : P v := by
  unfold Reader.runExact at hv
  cases hrs : r (Slice.ofCell c) with
  | none => rw [hrs] at hv; cases hv
  | some p =>
    obtain ⟨v', s'⟩ := p
    rw [hrs] at hv
    dsimp only at hv
    split at hv
    · cases hv
      have hs := Rem.ofCell c
      rw [hb, hr] at hs
      exact (h (Slice.ofCell c) [] [] _ s' (by simpa using hs) hrs).1
    · cases hv

end TvmLean.Tx

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-! ## Reading an active account -/

theorem csAdjust_active {t : Tx} (h : (csAdjust t).accStatus = .active) :
    csAdjust t = t ∧ t.accStatus = .active := by
  unfold csAdjust at *
  dsimp only at *
  by_cases c1 : (t.accStatus == .uninit && !t.wasActivated && (decide (t.balance = 0) && t.balanceExtra.isNone)) = true
  · simp only [if_pos c1] at h
    simp at h
  · simp only [if_neg c1] at h ⊢
    by_cases c2 : (t.accStatus == .deleted && !(decide (t.balance = 0) && t.balanceExtra.isNone)) = true
    · simp only [if_pos c2] at h
      simp at h
    · simp only [if_neg c2] at h ⊢
      exact ⟨trivial, h⟩

theorem not_not_eq {b : Bool} (h : ¬(!b) = true) : b = true := by
  cases b <;> simp_all

set_option maxHeartbeats 2000000 in
/-- An account `Account.unpack` reads as active: the reads that lead to it. -/
theorem unpack_active (sa : Cell) (wc : Int) (addr : BitString) (sp : Bool) :
    OKo (fun a : Account => a.status = .active → ∃ acc p storage q state si,
      Reader.runExact (do return (← Reader.ref, ← Reader.bits 256, ← Reader.uint 64)) sa = some (acc, p) ∧
      ((Slice.ofCell acc).readBits 1)[0]! = true ∧
      (do
        let _ ← Reader.bits 1
        let (pfx, awc, addrOrig) ← Account.Reader.addrStd
        return (pfx, awc, addrOrig, ← Account.Reader.storageInfo)) (Slice.ofCell acc) = some (q, storage) ∧
      (∃ v, (do return (← Reader.uint 64, ← Reader.currencies)) storage = some (v, state)) ∧
      (state.readBits 1)[0]! = true ∧
      Reader.runExact Account.Reader.stateInit (state.advanceBits 1).toCellRemaining = some si ∧
      a.code = si.code ∧ a.data = si.data)
      (Account.unpack sa wc addr sp) := by
  unfold Account.unpack
  tx_vcg
  all_goals first
    | (intro h; cases h; done)
    | (intro _; exact ⟨_, _, _, _, _, _, ‹_›, not_not_eq ‹_›, ‹_›, ⟨_, ‹_›⟩, ‹_›, ‹_›, rfl, rfl⟩)

/-! ## The shard account and the bits before the storage -/

/-- The `ShardAccount` of the account `acc` (`account_descr$_ account:^Account
last_trans_hash:bits256 last_trans_lt:uint64`). -/
def shardAccountCell (acc : Cell) (hash : BitString) (lt : Nat) : Cell :=
  (((({} : W).ref acc).bitStr hash).uint lt 64).cell

theorem shardAccount_read {acc : Cell} {hash : BitString} {lt : Nat} (hh : hash.size = 256) {acc' : Cell}
    {x : BitString × Nat}
    (h : Reader.runExact (do return (← Reader.ref, ← Reader.bits 256, ← Reader.uint 64))
      (shardAccountCell acc hash lt) = some (acc', x)) : acc' = acc := by
  have hr : ReadsAs (do return (← Reader.ref, ← Reader.bits 256, ← Reader.uint 64))
      (hash.toList ++ (natToBits lt 64).toList) [acc] (fun r => r.1 = acc) := by
    refine (ReadsAs.bind (B₁ := []) (B₂ := hash.toList ++ (natToBits lt 64).toList) (R₁ := [acc]) (R₂ := [])
      (ReadsAs.ref acc) fun a ha => ?_).congr (by simp) (by simp)
    refine (ReadsAs.bind (B₂ := (natToBits lt 64).toList) (R₁ := []) (R₂ := [])
      (ReadsAs.bits' hash.toList 256 (by simp [hh])) fun b _ => ?_).congr rfl rfl
    refine (ReadsAs.bind (B₂ := []) (R₁ := []) (R₂ := []) (ReadsAs.uint lt 64) fun c _ => ?_).congr (by simp) rfl
    exact (ReadsAs.ret _).mono fun r hr => by subst hr; exact ha
  exact hr.runExact (by simp [shardAccountCell, W.cell_bits, W.uint_bits, W.bitStr_bits, W.ref])
    (by simp [shardAccountCell, W.cell_refs, W.uint, W.bitStr, W.ref]) h

theorem W.bool_refs (w : W) (b : Bool) : (w.bool b).refs = w.refs := rfl

theorem preW_bits (addr : Cell) (used : StorageUsed) (dh : Option BitString) (lp due : Nat) :
    (preW addr used dh lp due).bits.toList = true :: (addr.bits.toList ++ siEnc used dh lp due) := by
  unfold preW siEnc dueEnc dictHashEnc
  dsimp only
  cases dh <;> by_cases hd : due = 0 <;>
    simp [hd, W.uint7, W.grams, W.varUInt_enc, W.uint_bits, W.bool_bits, W.bitStr_bits, W.slice_bits]

theorem preW_refs (addr : Cell) (used : StorageUsed) (dh : Option BitString) (lp due : Nat) :
    (preW addr used dh lp due).refs.toList = addr.refs.toList := by
  unfold preW
  dsimp only
  cases dh <;> by_cases hd : due = 0 <;>
    simp [hd, W.uint7, W.grams, W.varUInt_refs, W.uint_refs, W.bool_refs, W.bitStr_refs, W.slice_refs]

/-- The reads of `Account.unpack` before the storage (`account$1 addr:MsgAddressInt
storage_stat:StorageInfo`). -/
theorem ReadsAs.accountPrefix {wc : Int} {any : Option BitString} {a : BitString} {lim : Int}
    (ha : a.size = 256) (hp : ∀ p, any = some p → p.size < 32)
    {used : StorageUsed} {dh : Option BitString} {lp due : Nat}
    (hc : used.cells < 2 ^ 48) (hb : used.bits < 2 ^ 48) (hdh : ∀ h, dh = some h → h.size = 256)
    (hdue : due < 2 ^ 120) :
    ReadsAs (do
        let _ ← Reader.bits 1
        let (pfx, awc, addrOrig) ← Account.Reader.addrStd
        return (pfx, awc, addrOrig, ← Account.Reader.storageInfo))
      (true :: ((Account.mkAddr wc any a lim).bits.toList ++ siEnc used dh lp due)) [] (fun _ => True) := by
  refine (ReadsAs.bind (B₁ := [true]) (R₁ := []) (R₂ := [])
    (B₂ := (Account.mkAddr wc any a lim).bits.toList ++ siEnc used dh lp due)
    (ReadsAs.bits [true]) fun _ _ => ?_).congr rfl rfl
  refine (ReadsAs.bind (R₁ := []) (R₂ := []) (B₂ := siEnc used dh lp due)
    (ReadsAs.addrStd_mkAddr wc any a lim ha hp) fun x _ => ?_).congr rfl rfl
  obtain ⟨pfx, awc, addrOrig⟩ := x
  dsimp only
  refine (ReadsAs.bind (B₂ := []) (R₁ := []) (R₂ := []) (ReadsAs.storageInfo (lastPaid := lp) hc hb hdh hdue)
    fun y _ => ?_).congr (by simp) rfl
  exact (ReadsAs.ret _).mono fun _ _ => trivial

/-- The reads of `Account.unpack` of the beginning of the storage (`last_trans_lt:uint64
balance:CurrencyCollection`). -/
theorem ReadsAs.ltBalance (endLt : Nat) {g : Nat} (hg : g < 2 ^ 120) (e : Option Cell) :
    ReadsAs (do return (← Reader.uint 64, ← Reader.currencies))
      ((natToBits endLt 64).toList ++ varEnc g 16 ++ maybeRefBits e) (maybeRefRefs e) (fun _ => True) := by
  refine (ReadsAs.bind (B₂ := varEnc g 16 ++ maybeRefBits e) (R₁ := []) (R₂ := maybeRefRefs e)
    (ReadsAs.uint endLt 64) fun _ _ => ?_).congr (by simp) (by simp)
  refine (ReadsAs.bind (B₂ := []) (R₂ := []) (ReadsAs.currencies hg e) fun _ _ => ?_).congr (by simp) (by simp)
  exact (ReadsAs.ret _).mono fun _ _ => trivial

/-! ## Reading back the account `Tx.computeState` writes -/

/-- The parts of the account `Tx.computeState` writes have the shape its reader needs: an address of
`Account.mkAddr` (256 bits, an anycast prefix below 32 bits), a dict hash of 256 bits, the fixed
prefix length below 32 (`## 5`). The balance, the storage statistics and the due payment fit their
fields whenever `Tx.computeState` succeeds (`computeState_some`). -/
structure StateParts.Fits (p : StateParts) : Prop where
  addr : ∃ wc any a lim, p.addr = Account.mkAddr wc any a lim ∧ a.size = 256 ∧ ∀ q, any = some q → q.size < 32
  dictHash : ∀ h, p.dictHash = some h → h.size = 256
  fpl : p.fpl < 32

/-- The account `Tx.computeState` writes from `tf` fits (`StateParts.Fits`), if it is not
`account_none`. -/
def Tx.Fits (tf : Tx) (sl : SizeLimits) : Prop := ∀ p, tf.computeStateParts sl = some p → p.Fits

theorem computeStateParts_some {tf : Tx} {sl : SizeLimits} {p : StateParts} (hp : tf.computeStateParts sl = some p) :
    (csAdjust tf).accStatus ≠ .nonexist ∧ (csAdjust tf).accStatus ≠ .deleted ∧
      p.t = (csState (csAdjust tf)).1 ∧ p.storage = (csState (csAdjust tf)).2.cell ∧ p.fpl = csFpl (csAdjust tf) := by
  revert hp
  unfold Tx.computeStateParts
  dsimp only
  split
  · intro hp; cases hp
  · rename_i hs
    generalize hq : csState (csAdjust tf) = q
    obtain ⟨t', w⟩ := q
    dsimp only
    intro hp
    split at hp
    · cases hp
    · cases hp
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hs
      exact ⟨hs.1, hs.2, rfl, rfl, rfl⟩

/-- **Read-back.** If the shard account of the account `Tx.computeState` writes from `tf` (fitting)
reads back as an active account, `tf` is active and the account's code and data are those of
`tf`. -/
theorem computeState_readBack {tf : Tx} {sl : SizeLimits} {t' : Tx} {acc : Cell}
    (hcs : tf.computeState sl = some (t', acc)) (hf : tf.Fits sl) {hash : BitString}
    (hh : hash.size = 256) (lt : Nat) {wc : Int} {addr : BitString} {sp : Bool} {a : Account}
    (hu : Account.unpack (shardAccountCell acc hash lt) wc addr sp = some a)
    (ha : a.status = .active) :
    tf.accStatus = .active ∧ a.code = tf.newCode ∧ a.data = tf.newData := by
  obtain ⟨acc', x, storage, q, state, si, hsa, hbit, hpre, ⟨v, hcur⟩, hsbit, hsi, hcode, hdata⟩ :=
    OKo_of (unpack_active _ wc addr sp) hu ha
  have hacc := shardAccount_read hh hsa
  cases hp : tf.computeStateParts sl with
  | none =>
    rw [computeState_none hp hcs] at hacc
    subst hacc
    have hr := Rem.ofCell (W.bool {} false).cell
    rw [show (W.bool {} false).cell.bits.toList = [false] from rfl] at hr
    rw [Rem.readBit0 hr] at hbit
    cases hbit
  | some p =>
    have pf := hf p hp
    obtain ⟨hne, hnd, hpt, hps, hpf⟩ := computeStateParts_some hp
    obtain ⟨_, hacc2, hbal', hcells, hbits, hdue⟩ := computeState_some hp hcs
    rw [hacc2] at hacc
    subst hacc
    obtain ⟨awc, any, aa, lim, hpa, hasz, hany⟩ := pf.addr
    -- the account cell: the bits before the storage, then the storage
    have hr0 := Rem.ofCell ((preW p.addr p.used p.dictHash p.t.lastPaid p.t.duePayment).slice
      (Slice.ofCell p.storage)).cell
    rw [W.cell_bits, W.cell_refs, W.slice_bits, W.slice_refs, preW_bits, preW_refs, hpa, mkAddr_refs] at hr0
    have hr1 := (ReadsAs.accountPrefix (lim := lim) hasz hany hcells hbits pf.dictHash hdue
      (Slice.ofCell ((preW p.addr p.used p.dictHash p.t.lastPaid p.t.duePayment).slice (Slice.ofCell p.storage)).cell)
      p.storage.bits.toList p.storage.refs.toList q storage
      (by rw [hpa]; simpa using hr0) hpre).2
    -- the storage
    obtain ⟨S, SR, hSb, hSr, hact, hnact⟩ := csState_storage (csAdjust tf) ⟨hne, hnd⟩
    rw [hps, W.cell_bits, W.cell_refs, hSb, hSr] at hr1
    have hr2 := (ReadsAs.ltBalance (csAdjust tf).endLt hbal' (csAdjust tf).balanceExtra storage S SR v state
      (by simpa using hr1) hcur).2
    by_cases hst : (csState (csAdjust tf)).1.accStatus = .active
    · obtain ⟨hfix, hS, hSR⟩ := hact hst
      rw [hfix] at hst
      obtain ⟨hadj, htf⟩ := csAdjust_active hst
      have hfpl : csFpl (csAdjust tf) < 32 := hpf ▸ pf.fpl
      rw [hS, splitEnc_eq hfpl] at hr2
      have hr3 := Rem.toCellRemaining (Rem.advance1 (by simpa using hr2))
      have hsi' := (ReadsAs.stateInit (csFpl (csAdjust tf)) (csAdjust tf).newTick (csAdjust tf).newTock
        (csAdjust tf).newCode (csAdjust tf).newData (csAdjust tf).newLibrary).runExact
        (by rw [hr3.1]; simp) (by rw [hr3.2, hSR]) hsi
      rw [hadj] at hsi'
      exact ⟨htf, hcode.trans hsi'.1, hdata.trans hsi'.2.1⟩
    · obtain ⟨S', rfl⟩ : ∃ S', S = false :: S' := by
        have := hnact hst
        cases S with
        | nil => cases this
        | cons b S' => simp at this; exact ⟨S', by rw [this]⟩
      rw [Rem.readBit0 hr2] at hsbit
      cases hsbit

end TvmLean.Tx

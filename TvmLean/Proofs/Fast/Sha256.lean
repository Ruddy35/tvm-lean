import TvmLean.Proofs.Fast.Bits

/-!
# SHA-256 on `Nat` words

The model's `sha256Digest` computes on `UInt32` words held in arrays (`w`, `h`), indexed with
`a[i]!` and updated with `set!`. In the kernel a `UInt32` operation goes through the `BitVec` and `Fin`
layers (about 0.5 ms each) and every index walks a list, 4–6 s a block. `sha256DigestFast` computes the
same function on `Nat` words with the kernel's arithmetic (`(a + b) % 2^32`, `&&&`, `^^^`, shifts),
the message schedule with a window of 16 words passed along, the round state as a structure, the
constants as a list: the rounds walk the constants and the schedule once.

`sha256Digest_eq_fast` proves the two equal for every message. The proof relates the model's loops
(in the normal form `sha256Digest_eq_loops`: left folds over `List.range'`) to the fast functions:
`toNat` of every word operation is the `Nat` operation (`toNat_*`), the array `w` after the two
schedule loops holds the fast schedule (`mExt_spec`), the round loop is `rounds` over the constants and
the schedule (`toSt_foldl_mRound`), the block loop is `hashBlocks` over the padded bytes 64 at a time,
the padding is `padN`, the output `outBytes`.
-/

namespace TvmLean.Sha256F

open TvmLean

-- elaborate one declaration at a time (each thread reserves address space; the memory cap is on it)
set_option Elab.async false

/-! ## The model's loops as folds -/

/-- The round state of the model's loop. -/
abbrev RS := MProd UInt32 (MProd UInt32 (MProd UInt32 (MProd UInt32 (MProd UInt32 (MProd UInt32
  (MProd UInt32 UInt32))))))

/-- The model's first schedule loop: the 16 words of the block at `base`. -/
def mInit (padded : Array UInt8) (base : Nat) : Array UInt32 :=
  List.foldl (fun w i => w.set! i (u32FromBytesBE padded[base + i * 4]! padded[base + i * 4 + 1]!
    padded[base + i * 4 + 2]! padded[base + i * 4 + 3]!)) (Array.replicate 64 0) (List.range' 0 16)

/-- The model's second schedule loop. -/
def mExt (w : Array UInt32) : Array UInt32 :=
  List.foldl (fun w i => w.set! i (w[i - 16]! + shaSmallSigma0 w[i - 15]! + w[i - 7]! + shaSmallSigma1 w[i - 2]!))
    w (List.range' 16 48)

/-- A round of the model's loop. -/
def mRound (w : Array UInt32) (r : RS) (i : Nat) : RS :=
  let t1 := r.2.2.2.2.2.2.2 + shaBigSigma1 r.2.2.2.2.1 + shaCh r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 +
    sha256K[i]! + w[i]!
  let t2 := shaBigSigma0 r.1 + shaMaj r.1 r.2.1 r.2.2.1
  ⟨t1 + t2, r.1, r.2.1, r.2.2.1, r.2.2.2.1 + t1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

/-- A block of the model's loop. -/
def mBlock (padded : Array UInt8) (h : Array UInt32) (bi : Nat) : Array UInt32 :=
  let w := mExt (mInit padded (bi * 64))
  let r := List.foldl (fun r i => mRound w r i) ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!, h[5]!, h[6]!, h[7]!⟩
    (List.range' 0 64)
  let h := h.set! 0 (h[0]! + r.1)
  let h := h.set! 1 (h[1]! + r.2.1)
  let h := h.set! 2 (h[2]! + r.2.2.1)
  let h := h.set! 3 (h[3]! + r.2.2.2.1)
  let h := h.set! 4 (h[4]! + r.2.2.2.2.1)
  let h := h.set! 5 (h[5]! + r.2.2.2.2.2.1)
  let h := h.set! 6 (h[6]! + r.2.2.2.2.2.2.1)
  h.set! 7 (h[7]! + r.2.2.2.2.2.2.2)

/-- The model's output loop. -/
def mOut (h : Array UInt32) : Array UInt8 :=
  List.foldl (fun out i =>
    let x : UInt32 := h[i]!
    (((out.push (UInt8.ofNat ((x >>> 24).toNat &&& 255))).push (UInt8.ofNat ((x >>> 16).toNat &&& 255))).push
      (UInt8.ofNat ((x >>> 8).toNat &&& 255))).push (UInt8.ofNat (x.toNat &&& 255))) #[] (List.range' 0 8)

/-- `sha256Digest` with its loops as left folds. -/
theorem sha256Digest_eq_loops (msg : Array UInt8) :
    sha256Digest msg = mOut (List.foldl (fun h bi => mBlock (sha256Pad msg) h bi) sha256Init
      (List.range' 0 ((sha256Pad msg).size / 64))) := by
  simp only [sha256Digest, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, pure_bind,
    Nat.sub_zero, Nat.reduceSub, mOut, mBlock, mExt, mInit, mRound]

/-! ## Word arithmetic on `Nat` -/

/-- Addition modulo `2^32`. The fast forms call the kernel's `Nat` operations directly: through the
instances of the notation each operation costs a few more unfoldings. -/
def add (a b : Nat) : Nat := Nat.mod (Nat.add a b) 4294967296

/-- Rotation right by `n` (`0 < n < 32`) of a word below `2^32`. -/
def rotr (x n : Nat) : Nat := Nat.lor (Nat.shiftRight x n) (Nat.mod (Nat.shiftLeft x (Nat.sub 32 n)) 4294967296)

def bsig0 (x : Nat) : Nat := Nat.xor (Nat.xor (rotr x 2) (rotr x 13)) (rotr x 22)
def bsig1 (x : Nat) : Nat := Nat.xor (Nat.xor (rotr x 6) (rotr x 11)) (rotr x 25)
def ssig0 (x : Nat) : Nat := Nat.xor (Nat.xor (rotr x 7) (rotr x 18)) (Nat.shiftRight x 3)
def ssig1 (x : Nat) : Nat := Nat.xor (Nat.xor (rotr x 17) (rotr x 19)) (Nat.shiftRight x 10)
def ch (x y z : Nat) : Nat := Nat.xor (Nat.land x y) (Nat.land (Nat.sub 4294967295 x) z)
def maj (x y z : Nat) : Nat := Nat.xor (Nat.xor (Nat.land x y) (Nat.land x z)) (Nat.land y z)

theorem add_eq (a b : Nat) : add a b = (a + b) % 4294967296 := rfl
theorem rotr_eq (x n : Nat) : rotr x n = (x >>> n) ||| ((x <<< (32 - n)) % 4294967296) := rfl
theorem bsig0_eq (x : Nat) : bsig0 x = rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22 := rfl
theorem bsig1_eq (x : Nat) : bsig1 x = rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25 := rfl
theorem ssig0_eq (x : Nat) : ssig0 x = rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3) := rfl
theorem ssig1_eq (x : Nat) : ssig1 x = rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10) := rfl
theorem ch_eq (x y z : Nat) : ch x y z = (x &&& y) ^^^ ((4294967295 - x) &&& z) := rfl
theorem maj_eq (x y z : Nat) : maj x y z = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := rfl

theorem toNat_add (a b : UInt32) : (a + b).toNat = add a.toNat b.toNat := by
  simp [add_eq]

theorem toNat_rotr (x : UInt32) (n : Nat) (h0 : 0 < n) (h1 : n < 32) : (u32rotr x n).toNat = rotr x.toNat n := by
  simp only [u32rotr, rotr_eq, UInt32.toNat_or, UInt32.toNat_shiftRight, UInt32.toNat_shiftLeft,
    UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega : 32 - n < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 32 - n < 32)]

theorem toNat_bsig0 (x : UInt32) : (shaBigSigma0 x).toNat = bsig0 x.toNat := by
  simp only [shaBigSigma0, bsig0_eq, UInt32.toNat_xor, toNat_rotr x 2 (by decide) (by decide),
    toNat_rotr x 13 (by decide) (by decide), toNat_rotr x 22 (by decide) (by decide)]

theorem toNat_bsig1 (x : UInt32) : (shaBigSigma1 x).toNat = bsig1 x.toNat := by
  simp only [shaBigSigma1, bsig1_eq, UInt32.toNat_xor, toNat_rotr x 6 (by decide) (by decide),
    toNat_rotr x 11 (by decide) (by decide), toNat_rotr x 25 (by decide) (by decide)]

theorem toNat_ssig0 (x : UInt32) : (shaSmallSigma0 x).toNat = ssig0 x.toNat := by
  simp only [shaSmallSigma0, ssig0_eq, UInt32.toNat_xor, toNat_rotr x 7 (by decide) (by decide),
    toNat_rotr x 18 (by decide) (by decide), UInt32.toNat_shiftRight]
  rfl

theorem toNat_ssig1 (x : UInt32) : (shaSmallSigma1 x).toNat = ssig1 x.toNat := by
  simp only [shaSmallSigma1, ssig1_eq, UInt32.toNat_xor, toNat_rotr x 17 (by decide) (by decide),
    toNat_rotr x 19 (by decide) (by decide), UInt32.toNat_shiftRight]
  rfl

theorem toNat_ch (x y z : UInt32) : (shaCh x y z).toNat = ch x.toNat y.toNat z.toNat := by
  simp only [shaCh, ch_eq, UInt32.toNat_xor, UInt32.toNat_and, UInt32.toNat_not]
  rfl

theorem toNat_maj (x y z : UInt32) : (shaMaj x y z).toNat = maj x.toNat y.toNat z.toNat := by
  simp only [shaMaj, maj_eq, UInt32.toNat_xor, UInt32.toNat_and]

/-! ## Rounds -/

/-- The round state: the eight working variables. -/
structure St where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat

/-- One round with constant `k` and schedule word `w`. -/
def round (s : St) (k w : Nat) : St :=
  let t1 := add (add (add (add s.h (bsig1 s.e)) (ch s.e s.f s.g)) k) w
  let t2 := add (bsig0 s.a) (maj s.a s.b s.c)
  ⟨add t1 t2, s.a, s.b, s.c, add s.d t1, s.e, s.f, s.g⟩

/-- The rounds over the constants and the schedule, in step. -/
def rounds : St → List Nat → List Nat → St
  | s, k :: ks, w :: ws => rounds (round s k w) ks ws
  | s, _, _ => s
termination_by structural _ ks => ks

/-- The model's round state as `Nat` words. -/
def toSt (r : RS) : St :=
  ⟨r.1.toNat, r.2.1.toNat, r.2.2.1.toNat, r.2.2.2.1.toNat, r.2.2.2.2.1.toNat, r.2.2.2.2.2.1.toNat,
    r.2.2.2.2.2.2.1.toNat, r.2.2.2.2.2.2.2.toNat⟩

theorem toSt_mRound (w : Array UInt32) (r : RS) (i : Nat) :
    toSt (mRound w r i) = round (toSt r) (sha256K[i]!).toNat (w[i]!).toNat := by
  simp only [mRound, toSt, round, toNat_add, toNat_bsig0, toNat_bsig1, toNat_ch, toNat_maj]

theorem toSt_foldl_mRound (w : Array UInt32) (r : RS) (k n : Nat) :
    toSt (List.foldl (fun r i => mRound w r i) r (List.range' k n)) =
      rounds (toSt r) ((List.range' k n).map fun i => (sha256K[i]!).toNat)
        ((List.range' k n).map fun i => (w[i]!).toNat) := by
  induction n generalizing k r with
  | zero => simp [rounds]
  | succ n ih => simp only [List.range'_succ, List.foldl_cons, List.map_cons, rounds, ih, toSt_mRound]

/-! ## The message schedule -/

/-- The schedule words after the window `w₀ … w₁₅`, `n` of them (the window passed as arguments: a
list window would be matched element by element at every step). -/
def sched : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → List Nat
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => []
  | n + 1, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 =>
    let x := add (add (add w0 (ssig0 w1)) w9) (ssig1 w14)
    x :: sched n w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 x
termination_by structural n => n

/-- The 48 schedule words after the 16 words of a block. -/
def schedL (ws : List Nat) : List Nat :=
  match ws with
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] =>
    sched 48 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
  | _ => []

/-- The recurrence of the schedule at `i` (`16 ≤ i`). -/
def SchedAt (L : List Nat) (i : Nat) : Prop :=
  L.getD i 0 = add (add (add (L.getD (i - 16) 0) (ssig0 (L.getD (i - 15) 0))) (L.getD (i - 7) 0))
    (ssig1 (L.getD (i - 2) 0))

theorem sched_spec (n : Nat) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Nat) :
    let L := [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] ++
      sched n w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    L.length = 16 + n ∧ ∀ i, 16 ≤ i → i < 16 + n → SchedAt L i := by
  induction n generalizing w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 with
  | zero => exact ⟨by simp [sched], fun i h1 h2 => by omega⟩
  | succ n ih =>
    intro L
    obtain ⟨ihl, ihs⟩ := ih w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      (add (add (add w0 (ssig0 w1)) w9) (ssig1 w14))
    have hL : L = w0 :: ([w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
        add (add (add w0 (ssig0 w1)) w9) (ssig1 w14)] ++ sched n w1 w2 w3 w4 w5 w6 w7 w8 w9 w10
        w11 w12 w13 w14 w15 (add (add (add w0 (ssig0 w1)) w9) (ssig1 w14))) := by
      simp [L, sched]
    rw [hL]
    refine ⟨by simp only [List.length_cons] at ihl ⊢; omega, ?_⟩
    intro i hi1 hi2
    rcases Nat.lt_or_ge i 17 with h | h
    · have : i = 16 := by omega
      subst this
      simp [SchedAt]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have := ihs j (by omega) (by omega)
      simp only [SchedAt] at this ⊢
      rw [List.getD_cons_succ, this, show j + 1 - 16 = (j - 16) + 1 by omega,
        show j + 1 - 15 = (j - 15) + 1 by omega, show j + 1 - 7 = (j - 7) + 1 by omega,
        show j + 1 - 2 = (j - 2) + 1 by omega]
      simp only [List.getD_cons_succ]

theorem sched_spec' (ws : List Nat) (hl : ws.length = 16) :
    (ws ++ schedL ws).length = 64 ∧ ∀ i, 16 ≤ i → i < 64 → SchedAt (ws ++ schedL ws) i := by
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | ⟨w8, _ |
    ⟨w9, _ | ⟨w10, _ | ⟨w11, _ | ⟨w12, _ | ⟨w13, _ | ⟨w14, _ | ⟨w15, _ | ⟨w16, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> try omega
  exact sched_spec 48 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

/-! ## Arrays -/

theorem getElem!_set! {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (v : α) (hi : i < a.size) :
    (a.set! i v)[j]! = if j = i then v else a[j]! := by
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

theorem getD_append_left {α : Type} (l1 l2 : List α) (i : Nat) (d : α) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {α : Type} (l1 l2 : List α) (i : Nat) (d : α) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- The model's array `w` after the second schedule loop holds the fast schedule. -/
theorem mExt_spec (w : Array UInt32) (hw : w.size = 64) (ws : List Nat) (hl : ws.length = 16)
    (h : ∀ j < 16, (w[j]!).toNat = ws.getD j 0) :
    ∀ j < 64, ((mExt w)[j]!).toNat = (ws ++ schedL ws).getD j 0 := by
  obtain ⟨hlen, hS⟩ := sched_spec' ws hl
  have key : ∀ k ≤ 48,
      (List.foldl (fun w i => w.set! i (w[i - 16]! + shaSmallSigma0 w[i - 15]! + w[i - 7]! +
        shaSmallSigma1 w[i - 2]!)) w (List.range' 16 k)).size = 64 ∧
      ∀ j < 16 + k, ((List.foldl (fun w i => w.set! i (w[i - 16]! + shaSmallSigma0 w[i - 15]! + w[i - 7]! +
        shaSmallSigma1 w[i - 2]!)) w (List.range' 16 k))[j]!).toNat = (ws ++ schedL ws).getD j 0 := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨hw, fun j hj => ?_⟩
      show (w[j]!).toNat = _
      rw [h j (by omega), getD_append_left _ _ _ _ (by omega)]
    | succ k ih =>
      obtain ⟨hs, hv⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
      refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs], fun j hj => ?_⟩
      rw [getElem!_set! _ _ _ _ (by omega)]
      split
      · rename_i hj'
        subst hj'
        have := hS (16 + k) (by omega) (by omega)
        simp only [SchedAt] at this
        rw [this, toNat_add, toNat_add, toNat_add, toNat_ssig0, toNat_ssig1, hv _ (by omega), hv _ (by omega),
          hv _ (by omega), hv _ (by omega)]
      · exact hv j (by omega)
  exact (key 48 (Nat.le_refl _)).2

/-! ## The words of a block -/

/-- The words of the block at `base` as the model reads them. -/
def blockWords (padded : Array UInt8) (base : Nat) : List Nat :=
  (List.range' 0 16).map fun i => (u32FromBytesBE padded[base + i * 4]! padded[base + i * 4 + 1]!
    padded[base + i * 4 + 2]! padded[base + i * 4 + 3]!).toNat

theorem blockWords_length (padded : Array UInt8) (base : Nat) : (blockWords padded base).length = 16 := by
  simp [blockWords]

theorem mInit_spec (padded : Array UInt8) (base : Nat) :
    (mInit padded base).size = 64 ∧
      ∀ j < 16, ((mInit padded base)[j]!).toNat = (blockWords padded base).getD j 0 := by
  have key : ∀ k ≤ 16,
      (List.foldl (fun (w : Array UInt32) i => w.set! i (u32FromBytesBE padded[base + i * 4]!
        padded[base + i * 4 + 1]! padded[base + i * 4 + 2]! padded[base + i * 4 + 3]!)) (Array.replicate 64 0)
        (List.range' 0 k)).size = 64 ∧
      ∀ j < k, ((List.foldl (fun (w : Array UInt32) i => w.set! i (u32FromBytesBE padded[base + i * 4]!
        padded[base + i * 4 + 1]! padded[base + i * 4 + 2]! padded[base + i * 4 + 3]!)) (Array.replicate 64 0)
        (List.range' 0 k))[j]!).toNat =
        (blockWords padded base).getD j 0 := by
    intro k hk
    induction k with
    | zero => exact ⟨by simp, fun j hj => by omega⟩
    | succ k ih =>
      obtain ⟨hs, hv⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul, Nat.zero_add]
      refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs], fun j hj => ?_⟩
      rw [getElem!_set! _ _ _ _ (by omega)]
      split
      · rename_i hj'
        subst j
        simp only [blockWords, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range' (by omega : k < 16)]
        simp
      · exact hv j (by omega)
  exact key 16 (Nat.le_refl _)

/-! ## A block -/

/-- The round constants. -/
def K : List Nat :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

set_option maxRecDepth 10000 in
theorem K_eq : (List.range' 0 64).map (fun i => (sha256K[i]!).toNat) = K := by decide +kernel

/-- The compression of the block with words `ws` into the hash state `h`. -/
def compress (h : List Nat) (ws : List Nat) : List Nat :=
  match h with
  | [a, b, c, d, e, f, g, hh] =>
    let s := rounds ⟨a, b, c, d, e, f, g, hh⟩ K (ws ++ schedL ws)
    [add a s.a, add b s.b, add c s.c, add d s.d, add e s.e, add f s.f, add g s.g, add hh s.h]
  | _ => h

theorem schedule_eq (padded : Array UInt8) (base : Nat) :
    (List.range' 0 64).map (fun i => ((mExt (mInit padded base))[i]!).toNat) =
      blockWords padded base ++ schedL (blockWords padded base) := by
  obtain ⟨hs, hv⟩ := mInit_spec padded base
  have he := mExt_spec _ hs _ (blockWords_length padded base) hv
  have hl := (sched_spec' _ (blockWords_length padded base)).1
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    rw [he _ (by simpa using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

theorem mBlock_eq (padded : Array UInt8) (bi : Nat) (h0 h1 h2 h3 h4 h5 h6 h7 : UInt32) :
    mBlock padded #[h0, h1, h2, h3, h4, h5, h6, h7] bi =
      let R := List.foldl (fun r i => mRound (mExt (mInit padded (bi * 64))) r i)
        ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ (List.range' 0 64)
      #[h0 + R.1, h1 + R.2.1, h2 + R.2.2.1, h3 + R.2.2.2.1, h4 + R.2.2.2.2.1, h5 + R.2.2.2.2.2.1,
        h6 + R.2.2.2.2.2.2.1, h7 + R.2.2.2.2.2.2.2] := by
  apply Array.ext'
  simp [mBlock]

theorem mBlock_spec (padded : Array UInt8) (h : Array UInt32) (hh : h.size = 8) (bi : Nat) :
    (mBlock padded h bi).size = 8 ∧
      (mBlock padded h bi).toList.map UInt32.toNat =
        compress (h.toList.map UInt32.toNat) (blockWords padded (bi * 64)) := by
  rcases h with ⟨_ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, _ | ⟨h6, _ | ⟨h7, _ | ⟨h8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hh <;> try omega
  have hr := toSt_foldl_mRound (mExt (mInit padded (bi * 64))) ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ 0 64
  rw [K_eq, schedule_eq] at hr
  rw [mBlock_eq]
  generalize List.foldl (fun r i => mRound (mExt (mInit padded (bi * 64))) r i) _ _ = R at hr ⊢
  simp only [toSt] at hr
  refine ⟨by simp, ?_⟩
  simp only [List.map_cons, List.map_nil, compress]
  rw [← hr]
  simp [add_eq]

/-! ## Bytes to words -/

/-- A big-endian word of four bytes. -/
def word (b0 b1 b2 b3 : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft b0 24) (Nat.shiftLeft b1 16)) (Nat.shiftLeft b2 8)) b3

theorem word_eq (b0 b1 b2 b3 : Nat) : word b0 b1 b2 b3 = (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3 := rfl

theorem shift_byte (x k : Nat) (hx : x < 2 ^ 8) (hk : k ≤ 24) : ((x % 2 ^ 32) <<< k) % 2 ^ 32 = x <<< k := by
  have h1 : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h2 : x * 2 ^ k < 2 ^ 8 * 2 ^ 24 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos k)) (Nat.mul_le_mul_left _ h1)
  rw [Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show x * 2 ^ k < 2 ^ 32 by omega)]

theorem toNat_u32FromBytesBE (b0 b1 b2 b3 : UInt8) :
    (u32FromBytesBE b0 b1 b2 b3).toNat = word b0.toNat b1.toNat b2.toNat b3.toNat := by
  simp only [u32FromBytesBE, word_eq, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_ofNat']
  rw [show UInt32.toNat 24 % 32 = 24 from rfl, show UInt32.toNat 16 % 32 = 16 from rfl,
    show UInt32.toNat 8 % 32 = 8 from rfl, shift_byte _ _ (UInt8.toNat_lt b0) (by decide),
    shift_byte _ _ (UInt8.toNat_lt b1) (by decide), shift_byte _ _ (UInt8.toNat_lt b2) (by decide),
    Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt b3) (by decide))]

/-- The words of a byte list, four bytes each (a partial last word dropped). -/
def words : List Nat → List Nat
  | b0 :: b1 :: b2 :: b3 :: l => word b0 b1 b2 b3 :: words l
  | _ => []
termination_by structural l => l

theorem words_cons4 (b0 b1 b2 b3 : Nat) (L : List Nat) :
    words (b0 :: b1 :: b2 :: b3 :: L) = word b0 b1 b2 b3 :: words L := by
  rw [words]

theorem words_length : ∀ (n : Nat) (L : List Nat), L.length < 4 * n → (words L).length = L.length / 4
  | 0, L, h => absurd h (Nat.not_lt_zero _)
  | n + 1, L, h => by
    match L with
    | b0 :: b1 :: b2 :: b3 :: L' =>
      rw [words_cons4, List.length_cons, words_length n L' (by simp at h; omega)]
      simp only [List.length_cons]
      omega
    | [] => simp [words]
    | [_] => simp [words]
    | [_, _] => simp [words]
    | [_, _, _] => simp [words]

theorem words_getD : ∀ (i : Nat) (L : List Nat), 4 * i + 3 < L.length →
    (words L).getD i 0 = word (L.getD (4 * i) 0) (L.getD (4 * i + 1) 0) (L.getD (4 * i + 2) 0) (L.getD (4 * i + 3) 0)
  | i, b0 :: b1 :: b2 :: b3 :: L', h => by
    cases i with
    | zero => rfl
    | succ i =>
      rw [words_cons4, List.getD_cons_succ, words_getD i L' (by simp at h; omega),
        show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 by omega]
      simp only [List.getD_cons_succ, Nat.add_assoc]
  | _, [], h => by simp at h
  | _, [_], h => by simp at h
  | _, [_, _], h => by simp at h; omega
  | _, [_, _, _], h => by simp at h; omega

theorem getElem!_toNat (a : Array UInt8) (n : Nat) : (a[n]!).toNat = (a.toList.map UInt8.toNat).getD n 0 := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases a[n]? <;> rfl

theorem getD_take_drop (L : List Nat) (b k n : Nat) (h : k < n) :
    ((L.drop b).take n).getD k 0 = L.getD (b + k) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h, List.getElem?_drop]

theorem blockWords_eq (padded : Array UInt8) (base : Nat) (h : base + 64 ≤ padded.size) :
    blockWords padded base = words (((padded.toList.map UInt8.toNat).drop base).take 64) := by
  have hl : (((padded.toList.map UInt8.toNat).drop base).take 64).length = 64 := by simp; omega
  have hw : (words (((padded.toList.map UInt8.toNat).drop base).take 64)).length = 16 := by
    rw [words_length 17 _ (by omega), hl]
  apply List.ext_getElem
  · rw [blockWords_length, hw]
  · intro i h1 h2
    rw [blockWords_length] at h1
    rw [show (words (((padded.toList.map UInt8.toNat).drop base).take 64))[i] =
        (words (((padded.toList.map UInt8.toNat).drop base).take 64)).getD i 0 by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl, words_getD _ _ (by omega)]
    simp only [blockWords, List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    rw [toNat_u32FromBytesBE, getElem!_toNat, getElem!_toNat, getElem!_toNat, getElem!_toNat,
      getD_take_drop _ _ _ _ (by omega), getD_take_drop _ _ _ _ (by omega), getD_take_drop _ _ _ _ (by omega),
      getD_take_drop _ _ _ _ (by omega)]
    simp only [Nat.mul_comm 4 i, Nat.add_assoc]

/-! ## The blocks -/

/-- Hashes `n` blocks of 64 bytes of `l` into the state `h`. -/
def hashBlocks : Nat → List Nat → List Nat → List Nat
  | 0, h, _ => h
  | n + 1, h, l => hashBlocks n (compress h (words (l.take 64))) (l.drop 64)
termination_by structural n => n

theorem blocks_spec (padded : Array UInt8) (n s : Nat) (h : Array UInt32) (hh : h.size = 8)
    (hn : (s + n) * 64 ≤ padded.size) :
    (List.foldl (fun h bi => mBlock padded h bi) h (List.range' s n)).size = 8 ∧
      (List.foldl (fun h bi => mBlock padded h bi) h (List.range' s n)).toList.map UInt32.toNat =
        hashBlocks n (h.toList.map UInt32.toNat) ((padded.toList.map UInt8.toNat).drop (s * 64)) := by
  induction n generalizing s h with
  | zero => exact ⟨hh, by simp [hashBlocks]⟩
  | succ n ih =>
    obtain ⟨hs, hb⟩ := mBlock_spec padded h hh s
    rw [List.range'_succ, List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := ih (s + 1) _ hs (by rw [Nat.add_assoc, Nat.add_comm 1 n]; exact hn)
    refine ⟨ih1, ?_⟩
    rw [ih2, hb, hashBlocks, blockWords_eq _ _ (by rw [Nat.add_mul] at hn; omega), List.drop_drop,
      Nat.add_mul, Nat.one_mul]

/-! ## Padding -/

theorem pushZerosUntilMod_toList (out : Array UInt8) (fuel : Nat) (h : (120 - out.size % 64) % 64 ≤ fuel) :
    (pushZerosUntilMod out 64 56 fuel).toList = out.toList ++ List.replicate ((120 - out.size % 64) % 64) 0 := by
  induction fuel generalizing out with
  | zero =>
    have : (120 - out.size % 64) % 64 = 0 := by omega
    rw [this]; simp [pushZerosUntilMod]
  | succ fuel ih =>
    rw [pushZerosUntilMod]
    by_cases hm : out.size % 64 = 56
    · have : (120 - out.size % 64) % 64 = 0 := by omega
      simp [hm]
    · simp only [ne_eq, hm, not_false_eq_true, if_true]
      rw [ih _ (by simp; omega)]
      have : (120 - out.size % 64) % 64 = (120 - (out.size + 1) % 64) % 64 + 1 := by omega
      rw [this, List.replicate_succ, Array.toList_push, Array.size_push, List.append_assoc, List.singleton_append]

/-- The eight bytes of the message length in bits, big-endian. -/
def lenBytes (bitLen : Nat) : List Nat := (List.range' 0 8).map fun i => (bitLen >>> ((7 - i) * 8)) &&& 255

/-- The padded message: the bytes, `0x80`, zeros up to 56 modulo 64, the length. -/
def padN (m : List Nat) : List Nat :=
  m ++ 128 :: (List.replicate ((120 - (m.length + 1) % 64) % 64) 0 ++ lenBytes (m.length * 8))

theorem toNat_ofNat_and (x : Nat) : (UInt8.ofNat (x &&& 255)).toNat = x &&& 255 := by
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Nat.and_lt_two_pow x (by decide : 255 < 2 ^ 8))]

theorem mod256_and (y : Nat) : y % 256 &&& 255 = y &&& 255 := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod]

theorem pad_spec (msg : Array UInt8) :
    (sha256Pad msg).toList.map UInt8.toNat = padN (msg.toList.map UInt8.toNat) := by
  simp only [sha256Pad, Id.run, Nat.sub_zero, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, pure_bind]
  rw [foldl_push_toList, pushZerosUntilMod_toList _ _ (by omega)]
  simp [padN, lenBytes, mod256_and]

/-! ## Output -/

/-- The digest bytes of the hash state, each word big-endian. -/
def outBytes (h : List Nat) : List UInt8 :=
  h.flatMap fun x => [UInt8.ofNat ((x >>> 24) &&& 255), UInt8.ofNat ((x >>> 16) &&& 255),
    UInt8.ofNat ((x >>> 8) &&& 255), UInt8.ofNat (x &&& 255)]

theorem mOut_spec (h : Array UInt32) (hs : h.size = 8) : (mOut h).toList = outBytes (h.toList.map UInt32.toNat) := by
  rcases h with ⟨_ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, _ | ⟨h6, _ | ⟨h7, _ | ⟨h8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hs <;> try omega
  simp [mOut, outBytes, List.range', UInt32.toNat_shiftRight]

/-! ## SHA-256 -/

/-- The initial hash state. -/
def H0 : List Nat := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

theorem init_eq : sha256Init.toList.map UInt32.toNat = H0 := by decide +kernel

theorem init_size : sha256Init.size = 8 := by decide +kernel

end TvmLean.Sha256F

namespace TvmLean

open Sha256F in
/-- SHA-256 on `Nat` words, the blocks taken 64 bytes at a time from the padded byte list. -/
def sha256DigestFast (msg : Array UInt8) : Array UInt8 :=
  let p := padN (msg.toList.map UInt8.toNat)
  ⟨outBytes (hashBlocks (p.length / 64) H0 p)⟩

open Sha256F in
@[fast_forms]
theorem sha256Digest_eq_fast (msg : Array UInt8) : sha256Digest msg = sha256DigestFast msg := by
  rw [sha256Digest_eq_loops]
  have hp := pad_spec msg
  have hsz : (sha256Pad msg).size = (padN (msg.toList.map UInt8.toNat)).length := by
    rw [← hp]; simp
  obtain ⟨hs, hb⟩ := blocks_spec (sha256Pad msg) ((sha256Pad msg).size / 64) 0 sha256Init init_size
    (by rw [Nat.zero_add]; exact Nat.div_mul_le_self _ _)
  apply Array.ext'
  rw [mOut_spec _ hs, hb, init_eq, hp, hsz]
  simp [sha256DigestFast]

@[fast_repl] theorem sha256Digest_eq_fast_fun : @sha256Digest = @sha256DigestFast := by
  funext msg; exact sha256Digest_eq_fast msg

end TvmLean

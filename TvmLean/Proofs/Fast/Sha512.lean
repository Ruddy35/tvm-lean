import TvmLean.Proofs.Fast.Sha256

/-!
# SHA-512 on `Nat` words

The model's `sha512Digest` (in `Ed25519.verify`, the check of `CHKSIGNU`/`CHKSIGNS`, and in the PRNG)
computes on `UInt64` words held in arrays, about 12 s a block in the kernel. `sha512DigestFast`
computes the same function on `Nat` words with the kernel's arithmetic, as `sha256DigestFast` does for
SHA-256 (`TvmLean/Proofs/Fast/Sha256.lean`): 64-bit words, 80 rounds, a schedule of 64 more words,
blocks of 128 bytes, a length of 16 bytes. `sha512Digest_eq_fast` proves the two equal for every
message, by the same steps.
-/

namespace TvmLean.Sha512F

open TvmLean

set_option Elab.async false

/-! ## The model's loops as folds -/

/-- The round state of the model's loop. -/
abbrev RS := MProd UInt64 (MProd UInt64 (MProd UInt64 (MProd UInt64 (MProd UInt64 (MProd UInt64
  (MProd UInt64 UInt64))))))

/-- The model's first schedule loop: the 16 words of the block at `base`. -/
def mInit (padded : Array UInt8) (base : Nat) : Array UInt64 :=
  List.foldl (fun w i => w.set! i (u64FromBytesBE padded[base + i * 8]! padded[base + i * 8 + 1]!
    padded[base + i * 8 + 2]! padded[base + i * 8 + 3]! padded[base + i * 8 + 4]! padded[base + i * 8 + 5]!
    padded[base + i * 8 + 6]! padded[base + i * 8 + 7]!)) (Array.replicate 80 0) (List.range' 0 16)

/-- The model's second schedule loop. -/
def mExt (w : Array UInt64) : Array UInt64 :=
  List.foldl (fun w i => w.set! i (w[i - 16]! + sha512SmallSigma0 w[i - 15]! + w[i - 7]! +
    sha512SmallSigma1 w[i - 2]!)) w (List.range' 16 64)

/-- A round of the model's loop. -/
def mRound (w : Array UInt64) (r : RS) (i : Nat) : RS :=
  let t1 := r.2.2.2.2.2.2.2 + sha512BigSigma1 r.2.2.2.2.1 + sha512Ch r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 +
    sha512K[i]! + w[i]!
  let t2 := sha512BigSigma0 r.1 + sha512Maj r.1 r.2.1 r.2.2.1
  ⟨t1 + t2, r.1, r.2.1, r.2.2.1, r.2.2.2.1 + t1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

/-- A block of the model's loop. -/
def mBlock (padded : Array UInt8) (h : Array UInt64) (bi : Nat) : Array UInt64 :=
  let w := mExt (mInit padded (bi * 128))
  let r := List.foldl (fun r i => mRound w r i) ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!, h[5]!, h[6]!, h[7]!⟩
    (List.range' 0 80)
  let h := h.set! 0 (h[0]! + r.1)
  let h := h.set! 1 (h[1]! + r.2.1)
  let h := h.set! 2 (h[2]! + r.2.2.1)
  let h := h.set! 3 (h[3]! + r.2.2.2.1)
  let h := h.set! 4 (h[4]! + r.2.2.2.2.1)
  let h := h.set! 5 (h[5]! + r.2.2.2.2.2.1)
  let h := h.set! 6 (h[6]! + r.2.2.2.2.2.2.1)
  h.set! 7 (h[7]! + r.2.2.2.2.2.2.2)

/-- The model's output loop. -/
def mOut (h : Array UInt64) : Array UInt8 :=
  List.foldl (fun out i =>
    let x : UInt64 := h[i]!
    (((((((out.push (UInt8.ofNat ((x >>> 56).toNat &&& 255))).push (UInt8.ofNat ((x >>> 48).toNat &&& 255))).push
      (UInt8.ofNat ((x >>> 40).toNat &&& 255))).push (UInt8.ofNat ((x >>> 32).toNat &&& 255))).push
      (UInt8.ofNat ((x >>> 24).toNat &&& 255))).push (UInt8.ofNat ((x >>> 16).toNat &&& 255))).push
      (UInt8.ofNat ((x >>> 8).toNat &&& 255))).push (UInt8.ofNat (x.toNat &&& 255))) #[] (List.range' 0 8)

/-- `sha512Digest` with its loops as left folds. -/
theorem sha512Digest_eq_loops (msg : Array UInt8) :
    sha512Digest msg = mOut (List.foldl (fun h bi => mBlock (sha512Pad msg) h bi) sha512Init
      (List.range' 0 ((sha512Pad msg).size / 128))) := by
  simp only [sha512Digest, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, pure_bind,
    Nat.sub_zero, Nat.reduceSub, mOut, mBlock, mExt, mInit, mRound]

/-! ## Word arithmetic on `Nat` -/

/-- Addition modulo `2^64`, by the kernel's `Nat` operations called directly. -/
def add (a b : Nat) : Nat := Nat.mod (Nat.add a b) 18446744073709551616

/-- Rotation right by `n` (`0 < n < 64`) of a word below `2^64`. -/
def rotr (x n : Nat) : Nat :=
  Nat.lor (Nat.shiftRight x n) (Nat.mod (Nat.shiftLeft x (Nat.sub 64 n)) 18446744073709551616)

def bsig0 (x : Nat) : Nat := Nat.xor (Nat.xor (rotr x 28) (rotr x 34)) (rotr x 39)
def bsig1 (x : Nat) : Nat := Nat.xor (Nat.xor (rotr x 14) (rotr x 18)) (rotr x 41)
def ssig0 (x : Nat) : Nat := Nat.xor (Nat.xor (rotr x 1) (rotr x 8)) (Nat.shiftRight x 7)
def ssig1 (x : Nat) : Nat := Nat.xor (Nat.xor (rotr x 19) (rotr x 61)) (Nat.shiftRight x 6)
def ch (x y z : Nat) : Nat := Nat.xor (Nat.land x y) (Nat.land (Nat.sub 18446744073709551615 x) z)
def maj (x y z : Nat) : Nat := Nat.xor (Nat.xor (Nat.land x y) (Nat.land x z)) (Nat.land y z)

theorem add_eq (a b : Nat) : add a b = (a + b) % 18446744073709551616 := rfl
theorem rotr_eq (x n : Nat) : rotr x n = (x >>> n) ||| ((x <<< (64 - n)) % 18446744073709551616) := rfl
theorem bsig0_eq (x : Nat) : bsig0 x = rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39 := rfl
theorem bsig1_eq (x : Nat) : bsig1 x = rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41 := rfl
theorem ssig0_eq (x : Nat) : ssig0 x = rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7) := rfl
theorem ssig1_eq (x : Nat) : ssig1 x = rotr x 19 ^^^ rotr x 61 ^^^ (x >>> 6) := rfl
theorem ch_eq (x y z : Nat) : ch x y z = (x &&& y) ^^^ ((18446744073709551615 - x) &&& z) := rfl
theorem maj_eq (x y z : Nat) : maj x y z = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := rfl

theorem toNat_add (a b : UInt64) : (a + b).toNat = add a.toNat b.toNat := by
  simp [add_eq]

theorem toNat_rotr (x : UInt64) (n : Nat) (h0 : 0 < n) (h1 : n < 64) : (u64rotr x n).toNat = rotr x.toNat n := by
  simp only [u64rotr, rotr_eq, UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
    UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega : 64 - n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 64 - n < 64)]

theorem toNat_bsig0 (x : UInt64) : (sha512BigSigma0 x).toNat = bsig0 x.toNat := by
  simp only [sha512BigSigma0, bsig0_eq, UInt64.toNat_xor, toNat_rotr x 28 (by decide) (by decide),
    toNat_rotr x 34 (by decide) (by decide), toNat_rotr x 39 (by decide) (by decide)]

theorem toNat_bsig1 (x : UInt64) : (sha512BigSigma1 x).toNat = bsig1 x.toNat := by
  simp only [sha512BigSigma1, bsig1_eq, UInt64.toNat_xor, toNat_rotr x 14 (by decide) (by decide),
    toNat_rotr x 18 (by decide) (by decide), toNat_rotr x 41 (by decide) (by decide)]

theorem toNat_ssig0 (x : UInt64) : (sha512SmallSigma0 x).toNat = ssig0 x.toNat := by
  simp only [sha512SmallSigma0, ssig0_eq, UInt64.toNat_xor, toNat_rotr x 1 (by decide) (by decide),
    toNat_rotr x 8 (by decide) (by decide), UInt64.toNat_shiftRight]
  rfl

theorem toNat_ssig1 (x : UInt64) : (sha512SmallSigma1 x).toNat = ssig1 x.toNat := by
  simp only [sha512SmallSigma1, ssig1_eq, UInt64.toNat_xor, toNat_rotr x 19 (by decide) (by decide),
    toNat_rotr x 61 (by decide) (by decide), UInt64.toNat_shiftRight]
  rfl

theorem toNat_ch (x y z : UInt64) : (sha512Ch x y z).toNat = ch x.toNat y.toNat z.toNat := by
  simp only [sha512Ch, ch_eq, UInt64.toNat_xor, UInt64.toNat_and, UInt64.toNat_not]
  rfl

theorem toNat_maj (x y z : UInt64) : (sha512Maj x y z).toNat = maj x.toNat y.toNat z.toNat := by
  simp only [sha512Maj, maj_eq, UInt64.toNat_xor, UInt64.toNat_and]

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

theorem toSt_mRound (w : Array UInt64) (r : RS) (i : Nat) :
    toSt (mRound w r i) = round (toSt r) (sha512K[i]!).toNat (w[i]!).toNat := by
  simp only [mRound, toSt, round, toNat_add, toNat_bsig0, toNat_bsig1, toNat_ch, toNat_maj]

theorem toSt_foldl_mRound (w : Array UInt64) (r : RS) (k n : Nat) :
    toSt (List.foldl (fun r i => mRound w r i) r (List.range' k n)) =
      rounds (toSt r) ((List.range' k n).map fun i => (sha512K[i]!).toNat)
        ((List.range' k n).map fun i => (w[i]!).toNat) := by
  induction n generalizing k r with
  | zero => simp [rounds]
  | succ n ih => simp only [List.range'_succ, List.foldl_cons, List.map_cons, rounds, ih, toSt_mRound]

/-! ## The message schedule -/

/-- The schedule words after the window `w₀ … w₁₅`, `n` of them. -/
def sched : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → List Nat
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => []
  | n + 1, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 =>
    let x := add (add (add w0 (ssig0 w1)) w9) (ssig1 w14)
    x :: sched n w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 x
termination_by structural n => n

/-- The 64 schedule words after the 16 words of a block. -/
def schedL (ws : List Nat) : List Nat :=
  match ws with
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] =>
    sched 64 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
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
    (ws ++ schedL ws).length = 80 ∧ ∀ i, 16 ≤ i → i < 80 → SchedAt (ws ++ schedL ws) i := by
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | ⟨w8, _ |
    ⟨w9, _ | ⟨w10, _ | ⟨w11, _ | ⟨w12, _ | ⟨w13, _ | ⟨w14, _ | ⟨w15, _ | ⟨w16, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> try omega
  exact sched_spec 64 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

/-- The model's array `w` after the second schedule loop holds the fast schedule. -/
theorem mExt_spec (w : Array UInt64) (hw : w.size = 80) (ws : List Nat) (hl : ws.length = 16)
    (h : ∀ j < 16, (w[j]!).toNat = ws.getD j 0) :
    ∀ j < 80, ((mExt w)[j]!).toNat = (ws ++ schedL ws).getD j 0 := by
  obtain ⟨hlen, hS⟩ := sched_spec' ws hl
  have key : ∀ k ≤ 64,
      (List.foldl (fun w i => w.set! i (w[i - 16]! + sha512SmallSigma0 w[i - 15]! + w[i - 7]! +
        sha512SmallSigma1 w[i - 2]!)) w (List.range' 16 k)).size = 80 ∧
      ∀ j < 16 + k, ((List.foldl (fun w i => w.set! i (w[i - 16]! + sha512SmallSigma0 w[i - 15]! + w[i - 7]! +
        sha512SmallSigma1 w[i - 2]!)) w (List.range' 16 k))[j]!).toNat = (ws ++ schedL ws).getD j 0 := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨hw, fun j hj => ?_⟩
      show (w[j]!).toNat = _
      rw [h j (by omega), Sha256F.getD_append_left _ _ _ _ (by omega)]
    | succ k ih =>
      obtain ⟨hs, hv⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
      refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs], fun j hj => ?_⟩
      rw [Sha256F.getElem!_set! _ _ _ _ (by omega)]
      split
      · rename_i hj'
        subst hj'
        have := hS (16 + k) (by omega) (by omega)
        simp only [SchedAt] at this
        rw [this, toNat_add, toNat_add, toNat_add, toNat_ssig0, toNat_ssig1, hv _ (by omega), hv _ (by omega),
          hv _ (by omega), hv _ (by omega)]
      · exact hv j (by omega)
  exact (key 64 (Nat.le_refl _)).2

/-! ## The words of a block -/

/-- The words of the block at `base` as the model reads them. -/
def blockWords (padded : Array UInt8) (base : Nat) : List Nat :=
  (List.range' 0 16).map fun i => (u64FromBytesBE padded[base + i * 8]! padded[base + i * 8 + 1]!
    padded[base + i * 8 + 2]! padded[base + i * 8 + 3]! padded[base + i * 8 + 4]! padded[base + i * 8 + 5]!
    padded[base + i * 8 + 6]! padded[base + i * 8 + 7]!).toNat

theorem blockWords_length (padded : Array UInt8) (base : Nat) : (blockWords padded base).length = 16 := by
  simp [blockWords]

theorem mInit_spec (padded : Array UInt8) (base : Nat) :
    (mInit padded base).size = 80 ∧
      ∀ j < 16, ((mInit padded base)[j]!).toNat = (blockWords padded base).getD j 0 := by
  have key : ∀ k ≤ 16,
      (List.foldl (fun (w : Array UInt64) i => w.set! i (u64FromBytesBE padded[base + i * 8]!
        padded[base + i * 8 + 1]! padded[base + i * 8 + 2]! padded[base + i * 8 + 3]! padded[base + i * 8 + 4]!
        padded[base + i * 8 + 5]! padded[base + i * 8 + 6]! padded[base + i * 8 + 7]!)) (Array.replicate 80 0)
        (List.range' 0 k)).size = 80 ∧
      ∀ j < k, ((List.foldl (fun (w : Array UInt64) i => w.set! i (u64FromBytesBE padded[base + i * 8]!
        padded[base + i * 8 + 1]! padded[base + i * 8 + 2]! padded[base + i * 8 + 3]! padded[base + i * 8 + 4]!
        padded[base + i * 8 + 5]! padded[base + i * 8 + 6]! padded[base + i * 8 + 7]!)) (Array.replicate 80 0)
        (List.range' 0 k))[j]!).toNat = (blockWords padded base).getD j 0 := by
    intro k hk
    induction k with
    | zero => exact ⟨by simp, fun j hj => by omega⟩
    | succ k ih =>
      obtain ⟨hs, hv⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul, Nat.zero_add]
      refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs], fun j hj => ?_⟩
      rw [Sha256F.getElem!_set! _ _ _ _ (by omega)]
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
  [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
   0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
   0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
   0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
   0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
   0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
   0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
   0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
   0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
   0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
   0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
   0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
   0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
   0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
   0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
   0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
   0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
   0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
   0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
   0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

set_option maxRecDepth 10000 in
theorem K_eq : (List.range' 0 80).map (fun i => (sha512K[i]!).toNat) = K := by decide +kernel

/-- The compression of the block with words `ws` into the hash state `h`. -/
def compress (h : List Nat) (ws : List Nat) : List Nat :=
  match h with
  | [a, b, c, d, e, f, g, hh] =>
    let s := rounds ⟨a, b, c, d, e, f, g, hh⟩ K (ws ++ schedL ws)
    [add a s.a, add b s.b, add c s.c, add d s.d, add e s.e, add f s.f, add g s.g, add hh s.h]
  | _ => h

theorem schedule_eq (padded : Array UInt8) (base : Nat) :
    (List.range' 0 80).map (fun i => ((mExt (mInit padded base))[i]!).toNat) =
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

theorem mBlock_eq (padded : Array UInt8) (bi : Nat) (h0 h1 h2 h3 h4 h5 h6 h7 : UInt64) :
    mBlock padded #[h0, h1, h2, h3, h4, h5, h6, h7] bi =
      let R := List.foldl (fun r i => mRound (mExt (mInit padded (bi * 128))) r i)
        ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ (List.range' 0 80)
      #[h0 + R.1, h1 + R.2.1, h2 + R.2.2.1, h3 + R.2.2.2.1, h4 + R.2.2.2.2.1, h5 + R.2.2.2.2.2.1,
        h6 + R.2.2.2.2.2.2.1, h7 + R.2.2.2.2.2.2.2] := by
  apply Array.ext'
  simp [mBlock]

theorem mBlock_spec (padded : Array UInt8) (h : Array UInt64) (hh : h.size = 8) (bi : Nat) :
    (mBlock padded h bi).size = 8 ∧
      (mBlock padded h bi).toList.map UInt64.toNat =
        compress (h.toList.map UInt64.toNat) (blockWords padded (bi * 128)) := by
  rcases h with ⟨_ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, _ | ⟨h6, _ | ⟨h7, _ | ⟨h8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hh <;> try omega
  have hr := toSt_foldl_mRound (mExt (mInit padded (bi * 128))) ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ 0 80
  rw [K_eq, schedule_eq] at hr
  rw [mBlock_eq]
  generalize List.foldl (fun r i => mRound (mExt (mInit padded (bi * 128))) r i) _ _ = R at hr ⊢
  simp only [toSt] at hr
  refine ⟨by simp, ?_⟩
  simp only [List.map_cons, List.map_nil, compress]
  rw [← hr]
  simp [add_eq]

/-! ## Bytes to words -/

/-- A big-endian word of eight bytes. -/
def word (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft b0 56) (Nat.shiftLeft b1 48))
    (Nat.shiftLeft b2 40)) (Nat.shiftLeft b3 32)) (Nat.shiftLeft b4 24)) (Nat.shiftLeft b5 16))
    (Nat.shiftLeft b6 8)) b7

theorem word_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    word b0 b1 b2 b3 b4 b5 b6 b7 = (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
      (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7 := rfl

theorem shift_byte (x k : Nat) (hx : x < 2 ^ 8) (hk : k ≤ 56) : ((x % 2 ^ 64) <<< k) % 2 ^ 64 = x <<< k := by
  have h1 : 2 ^ k ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hk
  have h2 : x * 2 ^ k < 2 ^ 8 * 2 ^ 56 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos k)) (Nat.mul_le_mul_left _ h1)
  rw [Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show x * 2 ^ k < 2 ^ 64 by omega)]

theorem toNat_u64FromBytesBE (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (u64FromBytesBE b0 b1 b2 b3 b4 b5 b6 b7).toNat =
      word b0.toNat b1.toNat b2.toNat b3.toNat b4.toNat b5.toNat b6.toNat b7.toNat := by
  simp only [u64FromBytesBE, word_eq, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat']
  rw [show UInt64.toNat 56 % 64 = 56 from rfl, show UInt64.toNat 48 % 64 = 48 from rfl,
    show UInt64.toNat 40 % 64 = 40 from rfl, show UInt64.toNat 32 % 64 = 32 from rfl,
    show UInt64.toNat 24 % 64 = 24 from rfl, show UInt64.toNat 16 % 64 = 16 from rfl,
    show UInt64.toNat 8 % 64 = 8 from rfl,
    shift_byte _ _ (UInt8.toNat_lt b0) (by decide), shift_byte _ _ (UInt8.toNat_lt b1) (by decide),
    shift_byte _ _ (UInt8.toNat_lt b2) (by decide), shift_byte _ _ (UInt8.toNat_lt b3) (by decide),
    shift_byte _ _ (UInt8.toNat_lt b4) (by decide), shift_byte _ _ (UInt8.toNat_lt b5) (by decide),
    shift_byte _ _ (UInt8.toNat_lt b6) (by decide),
    Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt b7) (by decide))]

/-- The words of a byte list, eight bytes each (a partial last word dropped). -/
def words : List Nat → List Nat
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l => word b0 b1 b2 b3 b4 b5 b6 b7 :: words l
  | _ => []
termination_by structural l => l

theorem words_cons8 (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (L : List Nat) :
    words (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: L) = word b0 b1 b2 b3 b4 b5 b6 b7 :: words L := by
  rw [words]

theorem words_length : ∀ (n : Nat) (L : List Nat), L.length < 8 * n → (words L).length = L.length / 8
  | 0, L, h => absurd h (Nat.not_lt_zero _)
  | n + 1, L, h => by
    match L with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: L' =>
      rw [words_cons8, List.length_cons, words_length n L' (by simp at h; omega)]
      simp only [List.length_cons]
      omega
    | [] => simp [words]
    | [_] => simp [words]
    | [_, _] => simp [words]
    | [_, _, _] => simp [words]
    | [_, _, _, _] => simp [words]
    | [_, _, _, _, _] => simp [words]
    | [_, _, _, _, _, _] => simp [words]
    | [_, _, _, _, _, _, _] => simp [words]

theorem words_getD : ∀ (i : Nat) (L : List Nat), 8 * i + 7 < L.length →
    (words L).getD i 0 = word (L.getD (8 * i) 0) (L.getD (8 * i + 1) 0) (L.getD (8 * i + 2) 0)
      (L.getD (8 * i + 3) 0) (L.getD (8 * i + 4) 0) (L.getD (8 * i + 5) 0) (L.getD (8 * i + 6) 0)
      (L.getD (8 * i + 7) 0)
  | i, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: L', h => by
    cases i with
    | zero => rfl
    | succ i =>
      rw [words_cons8, List.getD_cons_succ, words_getD i L' (by simp at h; omega),
        show 8 * (i + 1) = 8 * i + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
      simp only [List.getD_cons_succ, Nat.add_assoc]
  | _, [], h => by simp at h
  | _, [_], h => by simp at h
  | _, [_, _], h => by simp at h; omega
  | _, [_, _, _], h => by simp at h; omega
  | _, [_, _, _, _], h => by simp at h; omega
  | _, [_, _, _, _, _], h => by simp at h; omega
  | _, [_, _, _, _, _, _], h => by simp at h; omega
  | _, [_, _, _, _, _, _, _], h => by simp at h; omega

theorem blockWords_eq (padded : Array UInt8) (base : Nat) (h : base + 128 ≤ padded.size) :
    blockWords padded base = words (((padded.toList.map UInt8.toNat).drop base).take 128) := by
  have hl : (((padded.toList.map UInt8.toNat).drop base).take 128).length = 128 := by simp; omega
  have hw : (words (((padded.toList.map UInt8.toNat).drop base).take 128)).length = 16 := by
    rw [words_length 17 _ (by omega), hl]
  apply List.ext_getElem
  · rw [blockWords_length, hw]
  · intro i h1 h2
    rw [blockWords_length] at h1
    rw [show (words (((padded.toList.map UInt8.toNat).drop base).take 128))[i] =
        (words (((padded.toList.map UInt8.toNat).drop base).take 128)).getD i 0 by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl, words_getD _ _ (by omega)]
    simp only [blockWords, List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    simp only [toNat_u64FromBytesBE, Sha256F.getElem!_toNat]
    rw [Sha256F.getD_take_drop _ _ _ _ (by omega), Sha256F.getD_take_drop _ _ _ _ (by omega),
      Sha256F.getD_take_drop _ _ _ _ (by omega), Sha256F.getD_take_drop _ _ _ _ (by omega),
      Sha256F.getD_take_drop _ _ _ _ (by omega), Sha256F.getD_take_drop _ _ _ _ (by omega),
      Sha256F.getD_take_drop _ _ _ _ (by omega), Sha256F.getD_take_drop _ _ _ _ (by omega)]
    simp only [Nat.mul_comm 8 i, Nat.add_assoc]

/-! ## The blocks -/

/-- Hashes `n` blocks of 128 bytes of `l` into the state `h`. -/
def hashBlocks : Nat → List Nat → List Nat → List Nat
  | 0, h, _ => h
  | n + 1, h, l => hashBlocks n (compress h (words (l.take 128))) (l.drop 128)
termination_by structural n => n

theorem blocks_spec (padded : Array UInt8) (n s : Nat) (h : Array UInt64) (hh : h.size = 8)
    (hn : (s + n) * 128 ≤ padded.size) :
    (List.foldl (fun h bi => mBlock padded h bi) h (List.range' s n)).size = 8 ∧
      (List.foldl (fun h bi => mBlock padded h bi) h (List.range' s n)).toList.map UInt64.toNat =
        hashBlocks n (h.toList.map UInt64.toNat) ((padded.toList.map UInt8.toNat).drop (s * 128)) := by
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

theorem pushZerosUntilMod_toList (out : Array UInt8) (fuel : Nat) (h : (240 - out.size % 128) % 128 ≤ fuel) :
    (pushZerosUntilMod out 128 112 fuel).toList =
      out.toList ++ List.replicate ((240 - out.size % 128) % 128) 0 := by
  induction fuel generalizing out with
  | zero =>
    have : (240 - out.size % 128) % 128 = 0 := by omega
    rw [this]; simp [pushZerosUntilMod]
  | succ fuel ih =>
    rw [pushZerosUntilMod]
    by_cases hm : out.size % 128 = 112
    · have : (240 - out.size % 128) % 128 = 0 := by omega
      simp [hm]
    · simp only [ne_eq, hm, not_false_eq_true, if_true]
      rw [ih _ (by simp; omega)]
      have : (240 - out.size % 128) % 128 = (240 - (out.size + 1) % 128) % 128 + 1 := by omega
      rw [this, List.replicate_succ, Array.toList_push, Array.size_push, List.append_assoc, List.singleton_append]

/-- The sixteen bytes of the message length in bits, big-endian. -/
def lenBytes (bitLen : Nat) : List Nat := (List.range' 0 16).map fun i => (bitLen >>> ((15 - i) * 8)) &&& 255

/-- The padded message: the bytes, `0x80`, zeros up to 112 modulo 128, the length. -/
def padN (m : List Nat) : List Nat :=
  m ++ 128 :: (List.replicate ((240 - (m.length + 1) % 128) % 128) 0 ++ lenBytes (m.length * 8))

theorem pad_spec (msg : Array UInt8) :
    (sha512Pad msg).toList.map UInt8.toNat = padN (msg.toList.map UInt8.toNat) := by
  simp only [sha512Pad, Id.run, Nat.sub_zero, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, pure_bind]
  rw [foldl_push_toList, pushZerosUntilMod_toList _ _ (by omega)]
  simp [padN, lenBytes, Sha256F.mod256_and]

/-! ## Output -/

/-- The digest bytes of the hash state, each word big-endian. -/
def outBytes (h : List Nat) : List UInt8 :=
  h.flatMap fun x => [UInt8.ofNat ((x >>> 56) &&& 255), UInt8.ofNat ((x >>> 48) &&& 255),
    UInt8.ofNat ((x >>> 40) &&& 255), UInt8.ofNat ((x >>> 32) &&& 255), UInt8.ofNat ((x >>> 24) &&& 255),
    UInt8.ofNat ((x >>> 16) &&& 255), UInt8.ofNat ((x >>> 8) &&& 255), UInt8.ofNat (x &&& 255)]

theorem mOut_spec (h : Array UInt64) (hs : h.size = 8) : (mOut h).toList = outBytes (h.toList.map UInt64.toNat) := by
  rcases h with ⟨_ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, _ | ⟨h6, _ | ⟨h7, _ | ⟨h8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hs <;> try omega
  simp [mOut, outBytes, List.range', UInt64.toNat_shiftRight]

/-! ## SHA-512 -/

/-- The initial hash state. -/
def H0 : List Nat :=
  [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
   0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

theorem init_eq : sha512Init.toList.map UInt64.toNat = H0 := by decide +kernel

theorem init_size : sha512Init.size = 8 := by decide +kernel

end TvmLean.Sha512F

namespace TvmLean

open Sha512F in
/-- SHA-512 on `Nat` words, the blocks taken 128 bytes at a time from the padded byte list. -/
def sha512DigestFast (msg : Array UInt8) : Array UInt8 :=
  let p := padN (msg.toList.map UInt8.toNat)
  ⟨outBytes (hashBlocks (p.length / 128) H0 p)⟩

open Sha512F in
@[fast_forms]
theorem sha512Digest_eq_fast (msg : Array UInt8) : sha512Digest msg = sha512DigestFast msg := by
  rw [sha512Digest_eq_loops]
  have hp := pad_spec msg
  have hsz : (sha512Pad msg).size = (padN (msg.toList.map UInt8.toNat)).length := by
    rw [← hp]; simp
  obtain ⟨hs, hb⟩ := blocks_spec (sha512Pad msg) ((sha512Pad msg).size / 128) 0 sha512Init init_size
    (by rw [Nat.zero_add]; exact Nat.div_mul_le_self _ _)
  apply Array.ext'
  rw [mOut_spec _ hs, hb, init_eq, hp, hsz]
  simp [sha512DigestFast]

@[fast_repl] theorem sha512Digest_eq_fast_fun : @sha512Digest = @sha512DigestFast := by
  funext msg; exact sha512Digest_eq_fast msg

end TvmLean

import TvmLean.Model

/-!
# Bit strings and numbers: `natToBits` and `bitsToNat`

The contract data layouts (`TvmLean/Proofs/Contracts/*Spec.lean`) store unsigned integers as
`natToBits n k` (what `STU` stores) and read them back with `bitsToNat` (what `LDU`/`PLDU` read).
These are the facts the round trips of the layouts rest on: `bitsToNat (natToBits n k) = n % 2 ^ k`,
`natToBits (bitsToNat bs) bs.size = bs`, and `bitsToNat bs < 2 ^ bs.size`.
-/

namespace TvmLean

@[simp] theorem natToBits_size (n k : Nat) : (natToBits n k).size = k := by
  simp [natToBits]

@[simp] theorem bitsToNat_empty : bitsToNat #[] = 0 := rfl

theorem bitsToNat_push (bs : BitString) (b : Bool) :
    bitsToNat (bs.push b) = 2 * bitsToNat bs + (if b then 1 else 0) := by
  simp [bitsToNat, Nat.shiftLeft_eq, Nat.mul_comm]

/-- The bits of `n` on `k + 1` digits: those of `n / 2` on `k`, then the lowest bit. -/
theorem natToBits_succ (n k : Nat) :
    natToBits n (k + 1) = (natToBits (n / 2) k).push (n.testBit 0) := by
  apply Array.ext
  · simp
  · intro i h1 _
    simp only [natToBits, Array.getElem_ofFn, Array.getElem_push, Array.size_ofFn]
    split
    · simp only [Nat.testBit_div_two]
      congr 1
      omega
    · have : i = k := by simp at h1; omega
      subst this
      simp

theorem bit_eq_mod_two (n : Nat) : (if n.testBit 0 = true then 1 else 0) = n % 2 := by
  rw [Nat.testBit_zero]; split <;> simp_all <;> omega

/-- `bitsToNat` reads back `natToBits` modulo `2 ^ k`. -/
theorem bitsToNat_natToBits (n k : Nat) : bitsToNat (natToBits n k) = n % 2 ^ k := by
  induction k generalizing n with
  | zero => simp [natToBits, bitsToNat, Nat.mod_one]
  | succ k ih =>
    rw [natToBits_succ, bitsToNat_push, ih, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mod_mul,
      bit_eq_mod_two]
    omega

theorem bitsToNat_natToBits_of_lt {n k : Nat} (h : n < 2 ^ k) : bitsToNat (natToBits n k) = n := by
  rw [bitsToNat_natToBits, Nat.mod_eq_of_lt h]

/-- Every bit string is the `natToBits` of its value on its length. -/
theorem natToBits_bitsToNat (bs : BitString) : natToBits (bitsToNat bs) bs.size = bs := by
  suffices ∀ n (bs : BitString), bs.size = n → natToBits (bitsToNat bs) n = bs from this _ _ rfl
  intro n
  induction n with
  | zero => intro bs h; simp [natToBits, Array.eq_empty_of_size_eq_zero h]
  | succ n ih =>
    intro bs h
    obtain ⟨cs, b, rfl⟩ := Array.exists_push_of_size_eq_add_one h
    simp only [Array.size_push, Nat.add_right_cancel_iff] at h
    rw [natToBits_succ, bitsToNat_push]
    have h1 : (2 * bitsToNat cs + (if b then 1 else 0)) / 2 = bitsToNat cs := by split <;> omega
    have h2 : (2 * bitsToNat cs + (if b then 1 else 0)).testBit 0 = b := by
      rw [Nat.testBit_zero]; cases b <;> simp <;> omega
    rw [h1, h2, ih cs h]

theorem bitsToNat_lt (bs : BitString) : bitsToNat bs < 2 ^ bs.size := by
  rw [← natToBits_bitsToNat bs, bitsToNat_natToBits, natToBits_size]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A bit string of `k` bits is `natToBits` of its value on `k` bits. -/
theorem natToBits_bitsToNat_of_size {bs : BitString} {k : Nat} (h : bs.size = k) :
    natToBits (bitsToNat bs) k = bs := by
  subst h; exact natToBits_bitsToNat bs

theorem bitsToNat_lt_of_size {bs : BitString} {k : Nat} (h : bs.size = k) : bitsToNat bs < 2 ^ k := by
  subst h; exact bitsToNat_lt bs

end TvmLean

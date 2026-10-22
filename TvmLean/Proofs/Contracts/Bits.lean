import TvmLean.Proofs.Basic

/-!
# Bit strings and numbers: `natToBits` and `bitsToNat`

The contract data layouts (`TvmLean/Proofs/Contracts/*Spec.lean`) store unsigned integers as
`natToBits n k` (what `STU` stores) and read them back with `bitsToNat` (what `LDU`/`PLDU` read).
These are the facts the round trips of the layouts rest on: `bitsToNat (natToBits n k) = n % 2 ^ k`,
`natToBits (bitsToNat bs) bs.size = bs`, and `bitsToNat bs < 2 ^ bs.size`.
-/

namespace TvmLean

attribute [simp] natToBits_size

@[simp] theorem bitsToNat_empty : bitsToNat #[] = 0 := rfl

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

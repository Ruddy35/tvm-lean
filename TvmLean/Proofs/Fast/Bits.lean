import TvmLean.Proofs.Fast.Twin
import TvmLean.Model

/-!
# Bit access in a form the kernel evaluates fast

A `BitString` is an `Array Bool`, a list underneath. The kernel evaluates `bs[i]!` and the loop of
`Array.extract` by walking the list from its head for every index, so reading `n` bits at position
`p` costs about `n · p` steps, and converting a cell's bits to bytes (`bitStringToBytesBE`, the data
of a cell hash) is quadratic in the length of the cell. The forms here read the list once, from its
head: `List.drop` to the position, then `List.take` or one pass over what follows.

Each fast form is proved equal to the model's function for all inputs; the theorems marked
`@[fast_repl]` are the replacements the fast twins (`TvmLean/Proofs/Fast/Twin.lean`) make.
-/

universe u

namespace TvmLean

/-! ## Loops in `Id` -/

/-- A `for` loop in `Id` whose body yields in both branches of an `if` is a left fold. -/
theorem forIn_ite_yield {α β : Type} (l : List α) (init : β) (c : α → β → Prop)
    [∀ a b, Decidable (c a b)] (f g : α → β → β) :
    forIn (m := Id) l init (fun a b => if c a b then pure (.yield (f a b)) else pure (.yield (g a b))) =
      pure (l.foldl (fun b a => if c a b then f a b else g a b) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    by_cases h : c a init
    · simp only [h, if_true]; exact ih _
    · simp only [h, if_false]; exact ih _

/-! ## `Array.extract` and `Slice.readBits` -/

/-- `Array.extract` by `List.drop` and `List.take` on the underlying list. -/
def extractFast {α : Type u} (as : Array α) (start stop : Nat) : Array α :=
  ⟨(as.toList.drop start).take (stop - start)⟩

@[fast_repl] theorem extract_eq_fast : @Array.extract.{u} = @extractFast.{u} := by
  funext α as start stop
  apply Array.ext'
  simp [extractFast]

/-- `Array.append` as the append of the lists (the model's appends one element at a time, and each
push copies the list in the kernel). -/
def appendFast {α : Type u} (as bs : Array α) : Array α :=
  ⟨as.toList ++ bs.toList⟩

@[fast_repl] theorem append_eq_fast : @Array.append.{u} = @appendFast.{u} := by
  funext α as bs
  apply Array.ext'
  simp [appendFast]

/-- `Array.ofFn` as `List.ofFn` (one pass; the model's pushes one element at a time). -/
def ofFnFast {α : Type u} {n : Nat} (f : Fin n → α) : Array α :=
  ⟨List.ofFn f⟩

@[fast_repl] theorem ofFn_eq_fast : @Array.ofFn.{u} = @ofFnFast.{u} := by
  funext α n f
  apply Array.ext'
  simp [ofFnFast]

/-- `Slice.readBits` by `List.drop` and `List.take` on the cell's bit list. -/
def Slice.readBitsFast (s : Slice) (n : Nat) : BitString :=
  ⟨(s.cell.bits.toList.drop s.bitPos).take n⟩

@[fast_forms] theorem Slice.readBits_eq_fast (s : Slice) (n : Nat) : s.readBits n = s.readBitsFast n := by
  apply Array.ext'
  simp [Slice.readBits, Slice.readBitsFast]

@[fast_repl] theorem Slice.readBits_eq_fast_fun : @Slice.readBits = @Slice.readBitsFast := by
  funext s n; exact Slice.readBits_eq_fast s n

/-! ## `bitsToNat` -/

/-- `bitsToNat` as a fold over the bit list. -/
def bitsToNatFast (bs : BitString) : Nat :=
  bs.toList.foldl (fun acc b => (acc <<< 1) + (if b then 1 else 0)) 0

@[fast_forms] theorem bitsToNat_eq_fast (bs : BitString) : bitsToNat bs = bitsToNatFast bs := by
  simp [bitsToNat, bitsToNatFast]

@[fast_repl] theorem bitsToNat_eq_fast_fun : @bitsToNat = @bitsToNatFast := by
  funext bs; exact bitsToNat_eq_fast bs

/-! ## Bits to bytes -/

/-- The byte made of the bits of `l` from bit `7 - j` down, at most `n` of them, or-ed into `acc`;
bits past the end of `l` are 0 (as `bs[i]!` reads them). -/
def byteOfBits : List Bool → Nat → Nat → Nat → Nat
  | b :: l, j, n + 1, acc => byteOfBits l (j + 1) n (if b then acc ||| (1 <<< (7 - j)) else acc)
  | _, _, _, acc => acc
termination_by structural l => l

theorem getElem!_eq_headD (bs : BitString) (i : Nat) : bs[i]! = (bs.toList.drop i).headD false := by
  rw [Array.getElem!_eq_getD]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_toList.symm]
  induction bs.toList generalizing i with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero => simp
    | succ i => simp

/-- The model's loop over `j` from `j0`: `byteOfBits` from bit `start + j0`. -/
theorem foldl_bitsToByte (bs : BitString) (start j0 n acc : Nat) :
    List.foldl (fun r j => if bs[start + j]! = true then r ||| 1 <<< (7 - j) else r) acc (List.range' j0 n) =
      byteOfBits (bs.toList.drop (start + j0)) j0 n acc := by
  induction n generalizing j0 acc with
  | zero => cases h : bs.toList.drop (start + j0) <;> simp [byteOfBits]
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons, ih, getElem!_eq_headD]
    cases h : bs.toList.drop (start + j0) with
    | nil =>
      have h' : bs.toList.drop (start + (j0 + 1)) = [] := by
        rw [← Nat.add_assoc, ← List.drop_drop, h, List.drop_nil]
      simp only [h', List.headD_nil, Bool.false_eq_true, if_false, byteOfBits]
    | cons b l =>
      have h' : bs.toList.drop (start + (j0 + 1)) = l := by
        rw [← Nat.add_assoc, ← List.drop_drop, h]; rfl
      simp only [h', List.headD_cons, byteOfBits]

/-- `bitsToByte` by one pass over the bits from `start`. -/
def bitsToByteFast (bs : BitString) (start len : Nat) : UInt8 :=
  UInt8.ofNat (byteOfBits (bs.toList.drop start) 0 len 0)

@[fast_forms] theorem bitsToByte_eq_fast (bs : BitString) (start len : Nat) :
    bitsToByte bs start len = bitsToByteFast bs start len := by
  simp only [bitsToByte, bitsToByteFast, Id.run, Nat.sub_zero, pure_bind]
  rw [forIn_ite_yield (c := fun j _ => bs[start + j]! = true) (f := fun j r => r ||| 1 <<< (7 - j))
    (g := fun _ r => r)]
  exact congrArg UInt8.ofNat ((foldl_bitsToByte bs start 0 len 0).trans (by rw [Nat.add_zero]))

@[fast_repl] theorem bitsToByte_eq_fast_fun : @bitsToByte = @bitsToByteFast := by
  funext bs start len; exact bitsToByte_eq_fast bs start len

/-- `bitsToPaddedLastByte` by one pass over the bits from `start`. -/
def bitsToPaddedLastByteFast (bs : BitString) (start usedBits : Nat) : UInt8 :=
  UInt8.ofNat (byteOfBits (bs.toList.drop start) 0 usedBits 0 ||| (1 <<< (7 - usedBits)))

@[fast_forms] theorem bitsToPaddedLastByte_eq_fast (bs : BitString) (start usedBits : Nat) :
    bitsToPaddedLastByte bs start usedBits = bitsToPaddedLastByteFast bs start usedBits := by
  simp only [bitsToPaddedLastByte, bitsToPaddedLastByteFast, Id.run, Nat.sub_zero, pure_bind]
  rw [forIn_ite_yield (c := fun j _ => bs[start + j]! = true) (f := fun j r => r ||| 1 <<< (7 - j))
    (g := fun _ r => r)]
  exact congrArg (fun x => UInt8.ofNat (x ||| 1 <<< (7 - usedBits)))
    ((foldl_bitsToByte bs start 0 usedBits 0).trans (by rw [Nat.add_zero]))

@[fast_repl] theorem bitsToPaddedLastByte_eq_fast_fun : @bitsToPaddedLastByte = @bitsToPaddedLastByteFast := by
  funext bs start usedBits; exact bitsToPaddedLastByte_eq_fast bs start usedBits

/-- The bytes of a bit list, 8 bits at a time (the first bit the most significant), a partial last
byte dropped. -/
def bytesOfBitList : List Bool → List UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l =>
    UInt8.ofNat (byteOfBits [b0, b1, b2, b3, b4, b5, b6, b7] 0 8 0) :: bytesOfBitList l
  | _ => []
termination_by structural l => l

/-- `bitStringToBytesBE` in one pass over the bit list. -/
def bitStringToBytesBEFast (bs : BitString) : Array UInt8 :=
  ⟨bytesOfBitList bs.toList⟩

theorem foldl_push_toList {α β : Type} (f : α → β) (acc : Array β) (l : List α) :
    (List.foldl (fun b a => b.push (f a)) acc l).toList = acc.toList ++ l.map f := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp

theorem map_byteOfBits_drop (n : Nat) (L : List Bool) (h : L.length / 8 = n) :
    (List.range' 0 n).map (fun i => UInt8.ofNat (byteOfBits (L.drop (i * 8)) 0 8 0)) = bytesOfBitList L := by
  induction n generalizing L with
  | zero =>
    obtain _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, L'⟩⟩⟩⟩⟩⟩⟩⟩ := L <;>
      simp_all [bytesOfBitList] <;> omega
  | succ n ih =>
    obtain _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, L'⟩⟩⟩⟩⟩⟩⟩⟩ := L <;>
      simp at h <;> try omega
    rw [List.range'_succ, List.map_cons, bytesOfBitList, ← ih L' (by omega), List.range'_eq_map_range,
      List.range'_eq_map_range, List.map_map, List.map_map]
    simp only [Nat.zero_mul, List.drop_zero, Nat.zero_add]
    congr 1
    · simp [byteOfBits]
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp, Nat.add_mul, Nat.one_mul]
      rw [← List.drop_drop]
      rfl

@[fast_forms] theorem bitStringToBytesBE_eq_fast (bs : BitString) :
    bitStringToBytesBE bs = bitStringToBytesBEFast bs := by
  apply Array.ext'
  simp only [bitStringToBytesBE, Id.run, Nat.sub_zero, List.forIn_pure_yield_eq_foldl, bind_pure_comp,
    map_pure, pure_bind, bitStringToBytesBEFast]
  rw [foldl_push_toList]
  simp only [List.nil_append, bitsToByte_eq_fast, bitsToByteFast]
  exact map_byteOfBits_drop _ _ (by simp)

@[fast_repl] theorem bitStringToBytesBE_eq_fast_fun : @bitStringToBytesBE = @bitStringToBytesBEFast := by
  funext bs; exact bitStringToBytesBE_eq_fast bs

end TvmLean

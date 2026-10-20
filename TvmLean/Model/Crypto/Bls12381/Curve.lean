import TvmLean.Model.Crypto.Bls12381.Field

/-!
# BLS12-381: G1 and G2

`E1: y² = x³ + 4` over `Fp` and `E2: y² = x³ + 4(1 + i)` over `Fp2`, in Jacobian coordinates, as
blst (TON submodule at 6d960cd) uses them for the `BLS_*` instructions:

* compressed (de)serialization (`e1.c`, `e2.c`: `POINTonE{1,2}_Uncompress_Z`, `blst_p{1,2}_compress`);
* the subgroup checks of `map_to_g{1,2}.c` (`POINTonE1_in_G1`: `σ²(P) = −z²·P`, `POINTonE2_in_G2`:
  `ψ(P) = z·P`, Scott 2021);
* the scalar multiplications of `blst_p{1,2}_mult` (GLV with `σ` on E1, GLS with `ψ` on E2, the
  windows of `ptype##s_mult_w5` with blst's handling of infinity) and of
  `blst_p{1,2}s_mult_pippenger` (`multi_scalar.c`), which is what C++ computes also for points
  outside the subgroup.

Every addition of blst used here is complete (`dadd`, `dadd_affine`, the bucket and batch additions),
so a sum is the group element; where the blst algorithm departs from the plain multiple (its
handling of a point at infinity among the points of a multi-exponentiation, the flags of the
windowed multiplication) the algorithm is followed step by step.
-/

namespace TvmLean.Bls12381

/-- The operations of a field, passed explicitly to the curve arithmetic over `Fp` and `Fp2`. -/
structure Field (α : Type) where
  zero : α
  one : α
  add : α → α → α
  sub : α → α → α
  neg : α → α
  mul : α → α → α
  inv : α → α
  isZero : α → Bool
  eq : α → α → Bool

def fpF : Field Nat where
  zero := 0
  one := 1
  add := Fp.add
  sub := Fp.sub
  neg := Fp.neg
  mul := Fp.mul
  inv := Fp.inv
  isZero := (· == 0)
  eq := (· == ·)

def fp2F : Field Fp2 where
  zero := .zero
  one := .one
  add := Fp2.add
  sub := Fp2.sub
  neg := Fp2.neg
  mul := Fp2.mul
  inv := Fp2.inv
  isZero := Fp2.isZero
  eq := (· == ·)

/-- A point `(x / z², y / z³)`; the point at infinity for `z = 0`. -/
structure Jac (α : Type) where
  x : α
  y : α
  z : α
  deriving Inhabited

/-- An affine point as blst stores it: `(0, 0)` is the point at infinity. -/
structure Aff (α : Type) where
  x : α
  y : α
  deriving Inhabited

namespace Aff

variable {α : Type} [Inhabited α] (F : Field α)

def zero : Aff α := ⟨F.zero, F.zero⟩

/-- `vec_is_zero` of both coordinates: the point at infinity. -/
@[inline] def isZero (a : Aff α) : Bool := F.isZero a.x && F.isZero a.y

end Aff

namespace Jac

variable {α : Type} [Inhabited α] (F : Field α)

def inf : Jac α := ⟨F.one, F.one, F.zero⟩

@[inline] def isInf (q : Jac α) : Bool := F.isZero q.z

def neg (q : Jac α) : Jac α := ⟨q.x, F.neg q.y, q.z⟩

/-- Doubling (dbl-2009-l, `a = 0`); infinity stays infinity (`Z3 = 2 Y1 Z1`). -/
def double (q : Jac α) : Jac α :=
  let a := F.mul q.x q.x
  let b := F.mul q.y q.y
  let c := F.mul b b
  let xb := F.add q.x b
  let d := let t := F.sub (F.sub (F.mul xb xb) a) c; F.add t t
  let e := F.add (F.add a a) a
  let x3 := F.sub (F.mul e e) (F.add d d)
  let c2 := F.add c c
  let c4 := F.add c2 c2
  let c8 := F.add c4 c4
  let y3 := F.sub (F.mul e (F.sub d x3)) c8
  let yz := F.mul q.y q.z
  ⟨x3, y3, F.add yz yz⟩

/-- The sum of any two points (blst's `ptype##_dadd`: doubling and infinity included). -/
def add (q r : Jac α) : Jac α :=
  if isInf F q then r
  else if isInf F r then q
  else
    let z1z1 := F.mul q.z q.z
    let z2z2 := F.mul r.z r.z
    let u1 := F.mul q.x z2z2
    let u2 := F.mul r.x z1z1
    let s1 := F.mul (F.mul q.y r.z) z2z2
    let s2 := F.mul (F.mul r.y q.z) z1z1
    if F.eq u1 u2 then
      if F.eq s1 s2 then double F q else inf F
    else
      let h := F.sub u2 u1
      let rr := F.sub s2 s1
      let h2 := F.mul h h
      let h3 := F.mul h h2
      let u1h2 := F.mul u1 h2
      let x3 := F.sub (F.sub (F.mul rr rr) h3) (F.add u1h2 u1h2)
      let y3 := F.sub (F.mul rr (F.sub u1h2 x3)) (F.mul s1 h3)
      ⟨x3, y3, F.mul (F.mul h q.z) r.z⟩

/-- `blst_p{1,2}_from_affine`: `(0, 0)` is the point at infinity. -/
def ofAff (a : Aff α) : Jac α := if a.isZero F then inf F else ⟨a.x, a.y, F.one⟩

/-- `POINTonE{1,2}_from_Jacobian` / `to_affine`: `(0, 0)` for the point at infinity. -/
def toAff (q : Jac α) : Aff α :=
  if isInf F q then Aff.zero F
  else
    let zi := F.inv q.z
    let zi2 := F.mul zi zi
    ⟨F.mul q.x zi2, F.mul q.y (F.mul zi2 zi)⟩

/-- `POINTonE{1,2}_is_equal`: the same point (two points at infinity are equal). -/
def equal (q r : Jac α) : Bool :=
  if isInf F q || isInf F r then isInf F q && isInf F r
  else
    let z1z1 := F.mul q.z q.z
    let z2z2 := F.mul r.z r.z
    F.eq (F.mul q.x z2z2) (F.mul r.x z1z1) &&
      F.eq (F.mul (F.mul q.y r.z) z2z2) (F.mul (F.mul r.y q.z) z1z1)

/-- `k · q`, double and add from the top bit of `k`. -/
def mulNat (k : Nat) (q : Jac α) : Jac α := Id.run do
  let mut acc := inf F
  for i in [0:k.log2 + 1] do
    acc := double F acc
    if (k >>> (k.log2 - i)) % 2 = 1 then
      acc := add F acc q
  return acc

/-- `k · q` for a signed `k`. -/
def mulInt (k : Int) (q : Jac α) : Jac α :=
  if k < 0 then neg F (mulNat F k.natAbs q) else mulNat F k.natAbs q

/-- `ptype##_precompute_w5`: `[q, 2q, …, 16q]`. -/
def precomputeW5 (q : Jac α) : Array (Jac α) := Id.run do
  let mut t : Array (Jac α) := #[q, double F q]
  for j in [1:8] do
    t := t.push (add F t[j]! t[j - 1]!)
    t := t.push (double F t[j]!)
  return t

end Jac

/-! ## Windows and Booth digits (`ec_mult.h`, `multi_scalar.c`) -/

/-- `booth_encode` of a `(w+1)`-bit window value `v` (its low bit the top bit of the window below):
`(v + 1) / 2`, minus `2^w` when the top bit of `v` is set. -/
def boothDigit (v w : Nat) : Int :=
  let d : Int := Int.ofNat ((v + 1) / 2)
  if (v >>> w) % 2 = 1 then d - Int.ofNat (2 ^ w) else d

/-- The Booth digits of `s` (below `2^bits`) in windows of `w` bits as blst takes them, the top
window (the `bits % w` excess bits, possibly none) first, the window of the low bits last:
`s = Σ dᵢ · 2^(w·(n−1−i))`. -/
def boothDigits (s bits w : Nat) : Array Int := Id.run do
  let window0 := bits % w
  let mut pos := bits - window0
  let wv (pos width : Nat) : Nat :=
    if pos > 0 then (s >>> (pos - 1)) % 2 ^ (width + 1) else (s <<< 1) % 2 ^ (width + 1)
  let mut out : Array Int := #[boothDigit (wv pos window0) w]
  for _ in [0:pos / w] do
    pos := pos - w
    out := out.push (boothDigit (wv pos w) w)
  return out

/-- `ptype##s_mult_w5` (`ec_mult.h`) on the tables `tables[i] = [Pᵢ, 2Pᵢ, …, 16Pᵢ]` and the
scalars (below `2^bits`): the windows from the top, each point's digit gathered from its table and
added with `dadd`, five doublings between windows. A digit 0 gathers the first entry of the table
flagged as infinity; the flags follow blst (`ret_is_inf`, `row_is_inf`, `sum_is_inf`). -/
def multW5 {α : Type} [Inhabited α] (F : Field α) (tables : Array (Array (Jac α))) (scalars : Array Nat)
    (bits : Nat) : Jac α := Id.run do
  let digits := scalars.map (boothDigits · bits 5)
  let nwin := digits[0]!.size
  let gather (i : Nat) (d : Int) : Jac α × Bool :=
    let idx := d.natAbs
    let t := tables[i]![if idx = 0 then 0 else idx - 1]!
    (if d < 0 then Jac.neg F t else t, idx = 0)
  let (r0, inf0) := gather 0 digits[0]![0]!
  let mut ret := r0
  let mut retInf := inf0
  for w in [0:nwin] do
    for i in [(if w = 0 then 1 else 0):scalars.size] do
      let (row, rowInf0) := gather i digits[i]![w]!
      let mut rowInf := rowInf0
      if !(retInf || rowInf) then
        ret := Jac.add F ret row
      let sumInf := Jac.isInf F ret
      retInf := retInf || sumInf
      rowInf := rowInf || sumInf
      if retInf then
        ret := row
      retInf := retInf && rowInf
    if w + 1 < nwin then
      for _ in [0:5] do
        ret := Jac.double F ret
  return if retInf then Jac.inf F else ret

/-- The value of the Booth digits ±1 alone of `s` in the 4-bit windows of
`ptype##s_mult_wbits` over 256 bits (see `multiExp`). -/
def onesOfBooth4 (s : Nat) : Int :=
  (boothDigits s 256 4).foldl (fun acc d => acc * 16 + (if d.natAbs = 1 then d else 0)) 0

/-- `blst_p{1,2}s_mult_pippenger` (`multi_scalar.c`) for two or more points and scalars below `r`,
as C++ `generic_multiexp` calls it (256 bits):

* below 32 points, `ptype##s_precompute_wbits` with 4-bit windows: the table of each point is
  `[P, 2P, …, 8P]`, made affine by one batch inversion over the entries `2P … 8P` of all the
  points (`ptype##s_to_affine_row_wbits`). A point at infinity among them makes the product of
  their `Z` zero, its inverse zero (blst's reciprocal of 0), and every entry `2P … 8P` of every
  point the affine `(0, 0)`, i.e. infinity, while the entries `P` are copied as they are: each
  scalar then counts only through its Booth digits ±1 (`onesOfBooth4`);
* from 32 points, the bucket method, whose additions are all complete: `Σ sᵢ Pᵢ`. -/
def multiExp {α : Type} [Inhabited α] (F : Field α) (pts : Array (Aff α)) (scalars : Array Nat) : Jac α :=
  let quirk := pts.size < 32 && pts.any (·.isZero F)
  Id.run do
    let mut acc := Jac.inf F
    for i in [0:pts.size] do
      let k : Int := if quirk then onesOfBooth4 scalars[i]! else Int.ofNat scalars[i]!
      acc := Jac.add F acc (Jac.mulInt F k (Jac.ofAff F pts[i]!))
    return acc

/-! ## Bytes -/

/-- The big-endian number of `b[lo:hi]`. -/
def beNat (b : Array UInt8) (lo hi : Nat) : Nat :=
  (b.extract lo hi).foldl (fun acc x => acc * 256 + x.toNat) 0

/-- `n` as `len` big-endian bytes. -/
def natToBE (n len : Nat) : Array UInt8 :=
  Array.ofFn (n := len) fun i => UInt8.ofNat (n / 256 ^ (len - 1 - i.1) % 256)

/-- The compressed encoding of the point at infinity: `0xc0` and zeros. -/
def infEncoding (len : Nat) : Array UInt8 := #[0xc0] ++ Array.replicate (len - 1) 0

/-! ## G1 -/

/-- `β`, the cube root of unity of `sigma` (`e1.c`): `σ(x, y) = (β x, y)`. -/
def beta : Nat :=
  0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac

/-- `β²`. -/
def beta2 : Nat := beta * beta % p

/-- `POINTonE1_Uncompress_Z` of 48 bytes (`blst::P1_Affine(in, 48)` first requires the
compression flag): the infinity flag only with every other bit zero; the abscissa with the top
three bits cleared, below `p`; `x³ + 4` a square; the ordinate whose sign (`y > (p−1)/2`) is the
flag `0x20`; the abscissa 0 (`(0, ±2)`, of order 3) refused as `BLST_POINT_NOT_IN_GROUP`. -/
def decodeG1 (b : Array UInt8) : Option (Aff Nat) :=
  if b.size ≠ 48 then none
  else
    let b0 := b[0]!.toNat
    if b0 &&& 0x80 = 0 then none
    else if b0 &&& 0x40 ≠ 0 then
      if b0 &&& 0x3f = 0 && (b.extract 1 48).all (· = 0) then some (Aff.zero fpF) else none
    else
      let x := beNat b 0 48 % 2 ^ 381
      if x ≥ p then none
      else
        match Fp.sqrt? ((x * x % p * x + 4) % p) with
        | none => none
        | some y =>
            let y := if Fp.lexLarge y == (b0 &&& 0x20 ≠ 0) then y else Fp.neg y
            if x = 0 then none else some ⟨x, y⟩

/-- `blst_p1_compress`. -/
def compressG1 (q : Jac Nat) : Array UInt8 :=
  if q.isInf fpF then infEncoding 48
  else
    let a := q.toAff fpF
    let out := natToBE a.x 48
    out.set! 0 (out[0]! ||| 0x80 ||| (if Fp.lexLarge a.y then 0x20 else 0))

/-- `POINTonE1_in_G1`: `σ²(P) = −z²·P`. -/
def inG1 (q : Jac Nat) : Bool :=
  Jac.equal fpF ⟨Fp.mul beta2 q.x, q.y, q.z⟩ (Jac.neg fpF (Jac.mulNat fpF (zAbs * zAbs) q))

/-- `blst_p1_mult` with 255 bits (`blst::P1::mult(Scalar)`), a scalar below `r`:
`POINTonE1_mult_glv`. The scalar is split as `q·z² + rem` (`div_by_zz`), `q·P + rem·(−σ(P))` is
taken by `POINTonE1s_mult_w5` over 128 bits, negated and mapped by `σ²` (`Z·β²`): `rem·P − q·σ²(P)`,
which is `s·P` in G1. -/
def g1Mul (q : Jac Nat) (s : Nat) : Jac Nat :=
  let zz := zAbs * zAbs
  let t0 := Jac.precomputeW5 fpF q
  let t1 := t0.map fun t => ⟨Fp.mul beta t.x, Fp.neg t.y, t.z⟩
  let rr := Jac.neg fpF (multW5 fpF #[t0, t1] #[s / zz, s % zz] 128)
  ⟨Fp.mul beta2 rr.x, rr.y, rr.z⟩

/-! ## G2 -/

/-- `B` of E2: `4 + 4i`. -/
def b2 : Fp2 := ⟨4, 4⟩

/-- `POINTonE2_Uncompress_Z` of 96 bytes: as G1, the abscissa `c1 ‖ c0` (each below `p`, the top
three bits of `c1` cleared), `x³ + 4(1 + i)` a square of `Fp2`, the sign of the imaginary part of
the ordinate (of the real part if it is 0); no check of the abscissa 0. -/
def decodeG2 (b : Array UInt8) : Option (Aff Fp2) :=
  if b.size ≠ 96 then none
  else
    let b0 := b[0]!.toNat
    if b0 &&& 0x80 = 0 then none
    else if b0 &&& 0x40 ≠ 0 then
      if b0 &&& 0x3f = 0 && (b.extract 1 96).all (· = 0) then some (Aff.zero fp2F) else none
    else
      let c1 := beNat b 0 48 % 2 ^ 381
      let c0 := beNat b 48 96
      if c1 ≥ p || c0 ≥ p then none
      else
        let x : Fp2 := ⟨c0, c1⟩
        match Fp2.sqrt? ((x.sqr.mul x).add b2) with
        | none => none
        | some y =>
            let y := if Fp2.lexLarge y == (b0 &&& 0x20 ≠ 0) then y else y.neg
            some ⟨x, y⟩

/-- `blst_p2_compress`. -/
def compressG2 (q : Jac Fp2) : Array UInt8 :=
  if q.isInf fp2F then infEncoding 96
  else
    let a := q.toAff fp2F
    let out := natToBE a.x.c1 48 ++ natToBE a.x.c0 48
    out.set! 0 (out[0]! ||| 0x80 ||| (if Fp2.lexLarge a.y then 0x20 else 0))

/-- `1 / ξ^((p−1)/3)` and `1 / ξ^((p−1)/2)` (`psi`, `e2.c`). -/
def psiX : Fp2 :=
  ⟨0, 0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaad⟩
def psiY : Fp2 :=
  ⟨0x135203e60180a68ee2e9c448d77a2cd91c3dedd930b1cf60ef396489f61eb45e304466cf3e67fa0af1ee7b04121bdea2,
   0x06af0e0437ff400b6831e36d6bd17ffe48395dabc2d3435e77f76e17009241c5ee67992f72ec05f4c81084fbede3cc09⟩

/-- The endomorphism `ψ` (untwist, Frobenius, twist): `(x̄ · psiX, ȳ · psiY)`. -/
def psi (q : Jac Fp2) : Jac Fp2 := ⟨q.x.conj.mul psiX, q.y.conj.mul psiY, q.z.conj⟩

/-- `POINTonE2_in_G2`: `ψ(P) = z·P`. -/
def inG2 (q : Jac Fp2) : Bool := Jac.equal fp2F (psi q) (Jac.neg fp2F (Jac.mulNat fp2F zAbs q))

/-- `blst_p2_mult` with 255 bits, a scalar below `r`: `POINTonE2_mult_gls`. The scalar in base
`|z|` (`div_by_zz`, then `div_by_z` of each half: digits `d0 … d3`), `POINTonE2s_mult_w5` over 64
bits of `d0·P + d1·(−ψ(P)) + d2·ψ²(P) + d3·(−ψ³(P))`, which is `s·P` in G2. -/
def g2Mul (q : Jac Fp2) (s : Nat) : Jac Fp2 :=
  let zz := zAbs * zAbs
  let hi := s / zz
  let lo := s % zz
  let t0 := Jac.precomputeW5 fp2F q
  let t1 := t0.map psi
  let t2 := t1.map psi
  let t3 := t2.map psi
  multW5 fp2F #[t0, t1.map (Jac.neg fp2F), t2, t3.map (Jac.neg fp2F)]
    #[lo % zAbs, lo / zAbs, hi % zAbs, hi / zAbs] 64

/-- `[|z|]·P` (`POINTonE{1,2}_times_minus_z`). -/
def timesMinusZ {α : Type} [Inhabited α] (F : Field α) (q : Jac α) : Jac α := Jac.mulNat F zAbs q

end TvmLean.Bls12381

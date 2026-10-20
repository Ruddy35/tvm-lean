/-!
# BLS12-381: the field tower

The base field `Fp` (values kept below `p`), `Fp2 = Fp[i]/(i² + 1)`, `Fp6 = Fp2[v]/(v³ − ξ)` with
`ξ = 1 + i`, and `Fp12 = Fp6[w]/(w² − v)`: the tower of blst (`third-party/blst/src/fp12_tower.c`
of the TON submodule at 6d960cd), whose Miller loop and final exponentiation `Pairing.lean`
replays operation by operation. Every operation here is the exact field operation, so the results
are the values blst computes (in Montgomery form there, plain here).
-/

namespace TvmLean.Bls12381

/-- The field prime. -/
def p : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- The prime order of G1 and G2 (`bls::get_r` in C++, `BLS_PUSHR`). -/
def r : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- `|z|` for the curve parameter `z = −0xd201000000010000`. -/
def zAbs : Nat := 0xd201000000010000

/-! ## Fp -/

namespace Fp

@[inline] def add (a b : Nat) : Nat := let s := a + b; if s < p then s else s - p
@[inline] def sub (a b : Nat) : Nat := if b ≤ a then a - b else a + p - b
@[inline] def neg (a : Nat) : Nat := if a = 0 then 0 else p - a
@[inline] def mul (a b : Nat) : Nat := a * b % p
@[inline] def sqr (a : Nat) : Nat := a * a % p

/-- `a ^ e`, square and multiply over the bits of `e`. -/
def pow (a e : Nat) : Nat := Id.run do
  let mut acc := 1
  let mut b := a % p
  let mut k := e
  for _ in [0:e.log2 + 1] do
    if k % 2 = 1 then
      acc := acc * b % p
    b := b * b % p
    k := k / 2
  return acc

/-- The inverse (0 for 0, as blst's `reciprocal_fp`). -/
def inv (a : Nat) : Nat := pow a (p - 2)

/-- A square root, if `a` is a square (`p ≡ 3 mod 4`: `a^((p+1)/4)`). -/
def sqrt? (a : Nat) : Option Nat :=
  let y := pow a ((p + 1) / 4)
  if y * y % p = a % p then some y else none

/-- Whether `a` is a square (0 included). -/
def isSquare (a : Nat) : Bool := (sqrt? a).isSome

/-- The "sign" of compressed encodings (bit 1 of blst's `sgn0_pty_mod_384`): `a > (p−1)/2`. -/
@[inline] def lexLarge (a : Nat) : Bool := 2 * a ≥ p

/-- `sgn0` of hash-to-curve (RFC 9380): the parity. -/
@[inline] def sgn0 (a : Nat) : Bool := a % 2 = 1

end Fp

/-! ## Fp2 -/

structure Fp2 where
  c0 : Nat
  c1 : Nat
  deriving BEq, Inhabited, Repr

namespace Fp2

def zero : Fp2 := ⟨0, 0⟩
def one : Fp2 := ⟨1, 0⟩
@[inline] def ofNat (a : Nat) : Fp2 := ⟨a % p, 0⟩
@[inline] def isZero (a : Fp2) : Bool := a.c0 = 0 && a.c1 = 0
@[inline] def add (a b : Fp2) : Fp2 := ⟨Fp.add a.c0 b.c0, Fp.add a.c1 b.c1⟩
@[inline] def sub (a b : Fp2) : Fp2 := ⟨Fp.sub a.c0 b.c0, Fp.sub a.c1 b.c1⟩
@[inline] def neg (a : Fp2) : Fp2 := ⟨Fp.neg a.c0, Fp.neg a.c1⟩
@[inline] def conj (a : Fp2) : Fp2 := ⟨a.c0, Fp.neg a.c1⟩
@[inline] def dbl (a : Fp2) : Fp2 := add a a
@[inline] def mulFp (a : Fp2) (k : Nat) : Fp2 := ⟨a.c0 * k % p, a.c1 * k % p⟩

def mul (a b : Fp2) : Fp2 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  ⟨(t0 + p * p - t1) % p, (a.c0 * b.c1 + a.c1 * b.c0) % p⟩

def sqr (a : Fp2) : Fp2 :=
  ⟨(a.c0 + a.c1) * (a.c0 + p - a.c1) % p, 2 * a.c0 * a.c1 % p⟩

/-- `a · ξ = a · (1 + i)`. -/
@[inline] def mulXi (a : Fp2) : Fp2 := ⟨Fp.sub a.c0 a.c1, Fp.add a.c0 a.c1⟩

/-- The norm `a0² + a1²`. -/
@[inline] def norm (a : Fp2) : Nat := (a.c0 * a.c0 + a.c1 * a.c1) % p

/-- The inverse (0 for 0). -/
def inv (a : Fp2) : Fp2 :=
  let t := Fp.inv (norm a)
  ⟨a.c0 * t % p, Fp.neg (a.c1 * t % p)⟩

def pow (a : Fp2) (e : Nat) : Fp2 := Id.run do
  let mut acc := one
  let mut b := a
  let mut k := e
  for _ in [0:e.log2 + 1] do
    if k % 2 = 1 then
      acc := mul acc b
    b := sqr b
    k := k / 2
  return acc

/-- A square root, if `a` is a square: `a` is a square iff its norm is a square of `Fp`; then
`(a0 ± √(a0² + a1²)) / 2` (whichever is a square) is the square of the real part. -/
def sqrt? (a : Fp2) : Option Fp2 :=
  if a.c1 = 0 then
    match Fp.sqrt? a.c0 with
    | some y => some ⟨y, 0⟩
    | none => (Fp.sqrt? (Fp.neg a.c0)).map fun y => ⟨0, y⟩
  else
    match Fp.sqrt? (norm a) with
    | none => none
    | some s =>
        let half := Fp.inv 2
        let t1 := Fp.mul (Fp.add a.c0 s) half
        let t := if Fp.isSquare t1 then t1 else Fp.mul (Fp.sub a.c0 s) half
        match Fp.sqrt? t with
        | none => none
        | some x0 =>
            let x1 := Fp.mul a.c1 (Fp.inv (Fp.add x0 x0))
            let y : Fp2 := ⟨x0, x1⟩
            if sqr y == a then some y else none

/-- The sign of compressed encodings (bit 1 of blst's `sgn0_pty_mod_384x`): of the imaginary part
unless it is 0, else of the real part. -/
def lexLarge (a : Fp2) : Bool := if a.c1 = 0 then Fp.lexLarge a.c0 else Fp.lexLarge a.c1

/-- `sgn0` of hash-to-curve (RFC 9380, `m = 2`). -/
def sgn0 (a : Fp2) : Bool := Fp.sgn0 a.c0 || (a.c0 = 0 && Fp.sgn0 a.c1)

/-- `ξ = 1 + i`. -/
def xi : Fp2 := ⟨1, 1⟩

end Fp2

/-! ## Fp6 -/

structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
  deriving BEq, Inhabited, Repr

namespace Fp6

def zero : Fp6 := ⟨.zero, .zero, .zero⟩
def one : Fp6 := ⟨.one, .zero, .zero⟩
@[inline] def isZero (a : Fp6) : Bool := a.c0.isZero && a.c1.isZero && a.c2.isZero
@[inline] def add (a b : Fp6) : Fp6 := ⟨a.c0.add b.c0, a.c1.add b.c1, a.c2.add b.c2⟩
@[inline] def sub (a b : Fp6) : Fp6 := ⟨a.c0.sub b.c0, a.c1.sub b.c1, a.c2.sub b.c2⟩
@[inline] def neg (a : Fp6) : Fp6 := ⟨a.c0.neg, a.c1.neg, a.c2.neg⟩
@[inline] def mulFp2 (a : Fp6) (k : Fp2) : Fp6 := ⟨a.c0.mul k, a.c1.mul k, a.c2.mul k⟩

def mul (a b : Fp6) : Fp6 :=
  let t0 := a.c0.mul b.c0
  let t1 := a.c1.mul b.c1
  let t2 := a.c2.mul b.c2
  ⟨((a.c1.mul b.c2).add (a.c2.mul b.c1)).mulXi.add t0,
   ((a.c0.mul b.c1).add (a.c1.mul b.c0)).add t2.mulXi,
   ((a.c0.mul b.c2).add (a.c2.mul b.c0)).add t1⟩

def sqr (a : Fp6) : Fp6 := mul a a

/-- `a · v`. -/
@[inline] def mulByV (a : Fp6) : Fp6 := ⟨a.c2.mulXi, a.c0, a.c1⟩

/-- `inverse_fp6` (0 for 0). -/
def inv (a : Fp6) : Fp6 :=
  let c0 := a.c0.sqr.sub (a.c1.mul a.c2).mulXi
  let c1 := a.c2.sqr.mulXi.sub (a.c0.mul a.c1)
  let c2 := a.c1.sqr.sub (a.c0.mul a.c2)
  let t := (((c1.mul a.c2).add (c2.mul a.c1)).mulXi.add (c0.mul a.c0)).inv
  ⟨c0.mul t, c1.mul t, c2.mul t⟩

end Fp6

/-! ## Fp12 -/

structure Fp12 where
  c0 : Fp6
  c1 : Fp6
  deriving BEq, Inhabited, Repr

namespace Fp12

def zero : Fp12 := ⟨.zero, .zero⟩
def one : Fp12 := ⟨.one, .zero⟩
@[inline] def isOne (a : Fp12) : Bool := a == one

def mul (a b : Fp12) : Fp12 :=
  let t0 := a.c0.mul b.c0
  let t1 := a.c1.mul b.c1
  ⟨t0.add t1.mulByV, ((a.c0.add a.c1).mul (b.c0.add b.c1)).sub (t0.add t1)⟩

def sqr (a : Fp12) : Fp12 := mul a a

/-- `conjugate_fp12`: `a^(p^6)`. -/
@[inline] def conj (a : Fp12) : Fp12 := ⟨a.c0, a.c1.neg⟩

/-- `inverse_fp12` (0 for 0). -/
def inv (a : Fp12) : Fp12 :=
  let t := (a.c0.sqr.sub a.c1.sqr.mulByV).inv
  ⟨a.c0.mul t, (a.c1.mul t).neg⟩

/-- `sqr_fp4`: `(a0 + a1·W)²` for `W² = ξ`. -/
@[inline] private def sqrFp4 (a0 a1 : Fp2) : Fp2 × Fp2 :=
  let t0 := a0.sqr
  let t1 := a1.sqr
  (t1.mulXi.add t0, ((a0.add a1).sqr.sub t0).sub t1)

/-- `cyclotomic_sqr_fp12` (Granger–Scott): the square of an element of the cyclotomic subgroup;
blst's formula, applied as blst applies it. -/
def cyclotomicSqr (a : Fp12) : Fp12 :=
  let (t00, t01) := sqrFp4 a.c0.c0 a.c1.c1
  let (t10, t11) := sqrFp4 a.c1.c0 a.c0.c2
  let (t20, t21) := sqrFp4 a.c0.c1 a.c1.c2
  let r00 := ((t00.sub a.c0.c0).dbl).add t00
  let r01 := ((t10.sub a.c0.c1).dbl).add t10
  let r02 := ((t20.sub a.c0.c2).dbl).add t20
  let t21 := t21.mulXi
  let r10 := ((t21.add a.c1.c0).dbl).add t21
  let r11 := ((t01.add a.c1.c1).dbl).add t01
  let r12 := ((t11.add a.c1.c2).dbl).add t11
  ⟨⟨r00, r01, r02⟩, ⟨r10, r11, r12⟩⟩

/-- `ξ^((p^n − 1)/3)`, `ξ^((2p^n − 2)/3)` and `ξ^((p^n − 1)/6)` for `n = 1, 2, 3`: the
coefficients of the Frobenius maps (`coeffs1`, `coeffs2` of `frobenius_map_fp6`, `coeffs` of
`frobenius_map_fp12`; the unit tests check them against the powers of `ξ`). -/
def frobCoeffs : Array (Fp2 × Fp2 × Fp2) := #[
    (⟨0x0, 0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac⟩,
     ⟨0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaad, 0x0⟩,
     ⟨0x1904d3bf02bb0667c231beb4202c0d1f0fd603fd3cbd5f4f7b2443d784bab9c4f67ea53d63e7813d8d0775ed92235fb8,
      0xfc3e2b36c4e03288e9e902231f9fb854a14787b6c7b36fec0c8ec971f63c5f282d5ac14d6c7ec22cf78a126ddc4af3⟩),
    (⟨0x5f19672fdf76ce51ba69c6076a0f77eaddb3a93be6f89688de17d813620a00022e01fffffffefffe, 0x0⟩,
     ⟨0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac, 0x0⟩,
     ⟨0x5f19672fdf76ce51ba69c6076a0f77eaddb3a93be6f89688de17d813620a00022e01fffffffeffff, 0x0⟩),
    (⟨0x0, 0x1⟩,
     ⟨0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa, 0x0⟩,
     ⟨0x135203e60180a68ee2e9c448d77a2cd91c3dedd930b1cf60ef396489f61eb45e304466cf3e67fa0af1ee7b04121bdea2,
      0x6af0e0437ff400b6831e36d6bd17ffe48395dabc2d3435e77f76e17009241c5ee67992f72ec05f4c81084fbede3cc09⟩)]

private def frobFp2 (a : Fp2) (n : Nat) : Fp2 := if n % 2 = 1 then a.conj else a

private def frobFp6 (a : Fp6) (n : Nat) (c1 c2 : Fp2) : Fp6 :=
  ⟨frobFp2 a.c0 n, (frobFp2 a.c1 n).mul c1, (frobFp2 a.c2 n).mul c2⟩

/-- `frobenius_map_fp12`: `a^(p^n)` for `n = 1, 2, 3`. -/
def frobenius (a : Fp12) (n : Nat) : Fp12 :=
  let (c1, c2, c) := frobCoeffs[n - 1]!
  ⟨frobFp6 a.c0 n c1 c2, (frobFp6 a.c1 n c1 c2).mulFp2 c⟩

end Fp12

end TvmLean.Bls12381

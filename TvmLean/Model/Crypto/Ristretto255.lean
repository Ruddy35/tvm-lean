import TvmLean.Model.Crypto.Ed25519

/-!
ristretto255 (RFC 9496) as C++ uses it through libsodium (the TON submodule at d24faf5,
`crypto_core_ristretto255_*`, `crypto_scalarmult_ristretto255{_base}`) for the `RIST255_*`
instructions: elements are 32-byte encodings, the group law is that of edwards25519
(`Ed25519.Point`), and an encoding is the same for every representative of an element.
-/

namespace TvmLean.Ristretto255

open Ed25519

def sqrtAdMinusOne : Nat := 25063068953384623474111414158702152701244531502492656460079210482610430750235
def invsqrtAMinusD : Nat := 54469307008909316920995813868745141605393597292927456921205312896311721017578
def oneMinusDSq : Nat := 1159843021668779879193775521855586647937357759715417654439879720876111806838
def dMinusOneSq : Nat := 40440834346308536858101042469323190826248399146238708352240133220865137265952

/-- An odd residue (RFC 9496 `IS_NEGATIVE`). -/
def isNeg (x : Nat) : Bool := x % p % 2 = 1

def fneg (x : Nat) : Nat := fsub 0 x

/-- RFC 9496 `CT_ABS`: the even one of `x` and `−x`. -/
def fabs (x : Nat) : Nat := if isNeg x then fneg x else x % p

/-- RFC 9496 `SQRT_RATIO_M1(u, v)`: whether `u / v` is a square, and the even `r` with
`r² = u / v` (or `r² = √−1 · u / v` otherwise; 0 for `u = 0`). -/
def sqrtRatioM1 (u v : Nat) : Bool × Nat :=
  let u := u % p
  let v := v % p
  let v3 := v * v % p * v % p
  let v7 := v3 * v3 % p * v % p
  let r := u * v3 % p * powMod (u * v7 % p) ((p - 5) / 8) p % p
  let check := v * (r * r % p) % p
  let correct := check = u
  let flipped := check = fneg u
  let flippedI := check = fneg u * sqrtM1 % p
  let r := if flipped ∨ flippedI then r * sqrtM1 % p else r
  (correct ∨ flipped, fabs r)

/-- `ristretto255_frombytes` (RFC 9496 decode): `none` for an encoding not below `p`, odd, or not of
an element. -/
def decode (bytes : Array UInt8) : Option Point :=
  let s := leNat bytes
  if s ≥ p ∨ s % 2 = 1 then none
  else
    let ss := s * s % p
    let u1 := fsub 1 ss
    let u2 := (1 + ss) % p
    let u2Sqr := u2 * u2 % p
    let v := fsub (fneg (d * (u1 * u1 % p) % p)) u2Sqr
    let (wasSquare, invsqrt) := sqrtRatioM1 1 (v * u2Sqr % p)
    let denX := invsqrt * u2 % p
    let denY := invsqrt * denX % p * v % p
    let x := fabs (2 * s % p * denX)
    let y := u1 * denY % p
    let t := x * y % p
    if !wasSquare ∨ isNeg t ∨ y = 0 then none else some ⟨x, y, 1, t⟩

/-- `ristretto255_p3_tobytes` (RFC 9496 encode). -/
def encode (q : Point) : Array UInt8 :=
  let u1 := (q.Z + q.Y) * fsub q.Z q.Y % p
  let u2 := q.X * q.Y % p
  let (_, invsqrt) := sqrtRatioM1 1 (u1 * (u2 * u2 % p))
  let den1 := invsqrt * u1 % p
  let den2 := invsqrt * u2 % p
  let zInv := den1 * den2 % p * q.T % p
  let rotate := isNeg (q.T * zInv)
  let x := if rotate then q.Y * sqrtM1 % p else q.X % p
  let y := if rotate then q.X * sqrtM1 % p else q.Y % p
  let denInv := if rotate then den1 * invsqrtAMinusD % p else den2
  let y := if isNeg (x * zInv) then fneg y else y
  natLE32 (fabs (denInv * fsub q.Z y))

/-- `ristretto255_elligator` (RFC 9496 `MAP`). -/
def elligator (t : Nat) : Point :=
  let r := sqrtM1 * (t * t % p) % p
  let u := (r + 1) * oneMinusDSq % p
  let v := fsub (fneg 1) (r * d) * ((r + d) % p) % p
  let (wasSquare, s) := sqrtRatioM1 u v
  let s := if wasSquare then s else fneg (fabs (s * t))
  let c := if wasSquare then fneg 1 else r
  let n := fsub (c * fsub r 1 % p * dMinusOneSq) v
  let w0 := 2 * s * v % p
  let w1 := n * sqrtAdMinusOne % p
  let w2 := fsub 1 (s * s)
  let w3 := (1 + s * s) % p
  ⟨w0 * w3 % p, w2 * w1 % p, w1 * w3 % p, w0 * w2 % p⟩

/-- `crypto_core_ristretto255_from_hash` of 64 bytes: each half without its top bit is mapped, the
sum encoded. -/
def fromHash (h : Array UInt8) : Array UInt8 :=
  let t0 := leNat (h.extract 0 32) % 2 ^ 255 % p
  let t1 := leNat (h.extract 32 64) % 2 ^ 255 % p
  encode ((elligator t0).add (elligator t1))

/-- `crypto_core_ristretto255_is_valid_point`. -/
def isValid (x : Array UInt8) : Bool := (decode x).isSome

/-- `crypto_core_ristretto255_add`: `none` if an operand is not an encoding. -/
def add (x y : Array UInt8) : Option (Array UInt8) := do
  let a ← decode x
  let b ← decode y
  return encode (a.add b)

/-- `crypto_core_ristretto255_sub`. -/
def sub (x y : Array UInt8) : Option (Array UInt8) := do
  let a ← decode x
  let b ← decode y
  return encode (a.add b.neg)

/-- `crypto_scalarmult_ristretto255`: the scalar (little-endian) without its top bit; `none` if the
point is not an encoding or the product is the identity (encoded as zeros). -/
def mul (n x : Array UInt8) : Option (Array UInt8) := do
  let a ← decode x
  let r := encode (Point.mul (leNat n % 2 ^ 255) a)
  if r.all (· = 0) then none else some r

/-- `crypto_scalarmult_ristretto255_base`: the encoding of the product, and whether it is not the
identity (libsodium returns −1 for the identity, after writing its encoding). -/
def mulBase (n : Array UInt8) : Array UInt8 × Bool :=
  let r := encode (Point.mul (leNat n % 2 ^ 255) basePoint)
  (r, !r.all (· = 0))

end TvmLean.Ristretto255

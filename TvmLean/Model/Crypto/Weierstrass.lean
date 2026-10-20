/-!
Short Weierstrass curves `y² = x³ + a x + b` over a prime field: the group law in Jacobian
coordinates and the scalar multiplication, shared by secp256k1 (`ECRECOVER`,
`SECP256K1_XONLY_PUBKEY_TWEAK_ADD`) and P-256 (`P256_CHKSIGNU/S`). The result of every operation is
the group element itself, so the formulas need not be the ones of libsecp256k1 or OpenSSL.
-/

namespace TvmLean.Weierstrass

/-- `b ^ e mod m`, square and multiply over the bits of `e`. -/
def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut x := b % m
  let mut k := e
  for _ in [0:e.log2 + 1] do
    if k % 2 = 1 then
      r := r * x % m
    x := x * x % m
    k := k / 2
  return r

/-- The inverse modulo a prime `m` (0 for 0). -/
def invMod (a m : Nat) : Nat := powMod a (m - 2) m

structure Curve where
  /-- the field prime -/
  p : Nat
  a : Nat
  b : Nat
  /-- the order of the base point (the group order: both curves have cofactor 1) -/
  n : Nat
  gx : Nat
  gy : Nat

/-- A point `(x / z², y / z³)`, the point at infinity for `z = 0`. -/
structure Jac where
  x : Nat
  y : Nat
  z : Nat

def Jac.infinity : Jac := ⟨1, 1, 0⟩

def Jac.ofAffine (x y : Nat) : Jac := ⟨x, y, 1⟩

namespace Curve

variable (c : Curve)

def sub (u v : Nat) : Nat := (u + c.p - v % c.p) % c.p

def gen : Jac := .ofAffine c.gx c.gy

/-- The affine coordinates, `none` for the point at infinity. -/
def toAffine (q : Jac) : Option (Nat × Nat) :=
  if q.z % c.p = 0 then none
  else
    let zi := invMod q.z c.p
    let zi2 := zi * zi % c.p
    some (q.x * zi2 % c.p, q.y * zi2 % c.p * zi % c.p)

def double (q : Jac) : Jac :=
  let p := c.p
  if q.z % p = 0 ∨ q.y % p = 0 then Jac.infinity
  else
    let yy := q.y * q.y % p
    let s := 4 * q.x * yy % p
    let z2 := q.z * q.z % p
    let m := (3 * q.x * q.x + c.a * z2 % p * z2) % p
    let x3 := c.sub (m * m) (2 * s)
    let y3 := c.sub (m * c.sub s x3) (8 * yy * yy)
    ⟨x3, y3, 2 * q.y * q.z % p⟩

def add (q r : Jac) : Jac :=
  let p := c.p
  if q.z % p = 0 then r
  else if r.z % p = 0 then q
  else
    let z1z1 := q.z * q.z % p
    let z2z2 := r.z * r.z % p
    let u1 := q.x * z2z2 % p
    let u2 := r.x * z1z1 % p
    let s1 := q.y * r.z % p * z2z2 % p
    let s2 := r.y * q.z % p * z1z1 % p
    if u1 = u2 then
      if s1 = s2 then c.double q else Jac.infinity
    else
      let h := c.sub u2 u1
      let rr := c.sub s2 s1
      let h2 := h * h % p
      let h3 := h * h2 % p
      let u1h2 := u1 * h2 % p
      let x3 := c.sub (c.sub (rr * rr) h3) (2 * u1h2)
      let y3 := c.sub (rr * c.sub u1h2 x3) (s1 * h3)
      ⟨x3, y3, h * q.z % p * r.z % p⟩

/-- `k · q`, double and add from the top bit of `k`. -/
def mul (k : Nat) (q : Jac) : Jac := Id.run do
  let mut acc := Jac.infinity
  for i in [0:k.log2 + 1] do
    acc := c.double acc
    if (k >>> (k.log2 - i)) % 2 = 1 then
      acc := c.add acc q
  return acc

/-- `u · g + v · q`. -/
def mulAdd (u v : Nat) (q : Jac) : Jac := c.add (c.mul u c.gen) (c.mul v q)

/-- The point with the abscissa `x` (below `p`) and the ordinate of parity `odd`, if `x³ + a x + b`
is a square; for `p ≡ 3 (mod 4)` its square root is `(x³ + a x + b)^((p+1)/4)`. -/
def liftX (x : Nat) (odd : Bool) : Option Jac :=
  let p := c.p
  let rhs := (x * x % p * x + c.a * x + c.b) % p
  let y := powMod rhs ((p + 1) / 4) p
  if y * y % p ≠ rhs then none
  else
    let y := if (y % 2 = 1) = odd then y else (p - y) % p
    some (.ofAffine x y)

end Curve

end TvmLean.Weierstrass

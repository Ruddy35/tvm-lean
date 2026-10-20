import TvmLean.Model.Error.Excno

namespace TvmLean

inductive IntVal : Type
  | nan
  | num (n : Int)
  deriving DecidableEq, Repr

def IntVal.isValid : IntVal → Bool
  | .nan => false
  | .num _ => true

def IntVal.signedFits257 : IntVal → Bool
  | .nan => false
  | .num n =>
      -- [-2^256, 2^256)
      let lo : Int := -((2 : Int) ^ (256 : Nat))
      let hi : Int := (2 : Int) ^ (256 : Nat)
      decide (lo ≤ n ∧ n < hi)

def IntVal.add (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (a + b)
  | _, _ => .nan

def IntVal.sub (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (a - b)
  | _, _ => .nan

def IntVal.mul (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (a * b)
  | _, _ => .nan

def IntVal.min (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (if a ≤ b then a else b)
  | _, _ => .nan

def IntVal.inc (x : IntVal) : IntVal :=
  x.add (.num 1)

def IntVal.dec (x : IntVal) : IntVal :=
  x.sub (.num 1)

def IntVal.equalResult (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => if a = b then .num (-1) else .num 0
  | _, _ => .nan

def IntVal.toBool? (x : IntVal) : Except Excno Bool :=
  match x with
  | .nan => .error .intOv
  | .num n => .ok (n ≠ 0)

/-- C++ `RefInt256 << shift` (refint.cpp:152, `AnyIntView::lshift_any`, bigint.hpp:1611) applied to
NaN, which is a BigInt of no words. A shift of whole words (`shift / 52` of them, at most 5) adds
zero words and makes the value a valid 0; a shorter shift leaves no words (NaN), a longer one
does not fit (NaN). -/
def IntVal.nanLshiftCpp (shift : Nat) : IntVal :=
  if 52 ≤ shift ∧ shift ≤ 311 then .num 0 else .nan

/-- C++ `RefInt256 >> shift` (refint.cpp:157, `AnyIntView::rshift_any`, bigint.hpp:1544) applied to
NaN, rounding down. A shift by 0 keeps NaN; up to 12 bits (`word_bits - word_shift`) the result
is built from no words: 0; a longer shift gives the sign of the value, and the sign of NaN is
`0x80000000` (`sgn`, bigint.hpp:281), negative: -1. -/
def IntVal.nanRshiftCpp (shift : Nat) : IntVal :=
  if shift = 0 then .nan else if shift ≤ 12 then .num 0 else .num (-1)

end TvmLean

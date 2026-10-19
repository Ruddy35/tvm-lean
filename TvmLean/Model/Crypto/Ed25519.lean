import TvmLean.Model.Basics.Bytes

/-!
# Ed25519 signature verification (`CHKSIGNU`, `CHKSIGNS`)

C++ TVM verifies through OpenSSL: `exec_ed25519_check_signature` (`crypto/vm/tonops.cpp`) →
`td::Ed25519::PublicKey::verify_signature` (`crypto/Ed25519.cpp`: `EVP_PKEY_new_raw_public_key`,
`EVP_DigestVerify`) → `ossl_ed25519_verify` (`crypto/ec/curve25519.c` of the OpenSSL submodule):

1. `S` (signature bytes 32..63, little-endian) must be below the group order `L`;
2. the key is decoded by `ge_frombytes_vartime`: `y` is the low 255 bits taken modulo `p` (no
   canonicity check), `x` the square root of `(y² − 1) / (d·y² + 1)` whose parity is the top bit
   (for `x = 0` the top bit is ignored); a key without a square root is rejected. There is no
   small-order check of the key or of `R`;
3. `h = SHA-512(R ‖ key ‖ message) mod L`, with the 32 key bytes as given;
4. the signature is valid iff the canonical encoding of `[S]B − [h]A` equals `R` (the strict
   equation; a non-canonical `R` never matches).

The group law is the complete twisted Edwards addition (`a = −1`, `d` a non-square), so the result
is the group element whatever the order of `A`.
-/

namespace TvmLean.Ed25519

/-- The field prime `2^255 − 19`. -/
def p : Nat := 2 ^ 255 - 19

/-- The prime order of the base point. -/
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- `d = −121665 / 121666 mod p`. -/
def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- A square root of `−1` modulo `p` (`2^((p−1)/4)`). -/
def sqrtM1 : Nat := 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- `b^e mod m` by square-and-multiply over the low `fuel` bits of `e` (all exponents used here
are below `2^256`). -/
def powMod (b e m : Nat) : Nat :=
  go 256 (b % m) e 1
where
  go : Nat → Nat → Nat → Nat → Nat
    | 0, _, _, acc => acc
    | fuel + 1, b, e, acc =>
        if e = 0 then acc
        else go fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

def fsub (a b : Nat) : Nat := (a + p - b % p) % p

/-- A point in extended coordinates: `x = X/Z`, `y = Y/Z`, `x·y = T/Z`. -/
structure Point where
  X : Nat
  Y : Nat
  Z : Nat
  T : Nat

def Point.zero : Point := ⟨0, 1, 1, 0⟩

/-- Complete addition (Hisil–Wong–Carter–Dawson, `a = −1`); also used for doubling. -/
def Point.add (P Q : Point) : Point :=
  let a := fsub P.Y P.X * fsub Q.Y Q.X % p
  let b := (P.Y + P.X) * (Q.Y + Q.X) % p
  let c := 2 * P.T * Q.T % p * d % p
  let dd := 2 * P.Z * Q.Z % p
  let e := fsub b a
  let f := fsub dd c
  let g := (dd + c) % p
  let h := (b + a) % p
  ⟨e * f % p, g * h % p, f * g % p, e * h % p⟩

def Point.neg (P : Point) : Point := ⟨fsub 0 P.X, P.Y, P.Z, fsub 0 P.T⟩

/-- `[s]P` by double-and-add over the 256 low bits of `s`. -/
def Point.mul (s : Nat) (P : Point) : Point :=
  go 256 s P Point.zero
where
  go : Nat → Nat → Point → Point → Point
    | 0, _, _, acc => acc
    | fuel + 1, s, P, acc =>
        if s = 0 then acc
        else go fuel (s / 2) (P.add P) (if s % 2 = 1 then acc.add P else acc)

/-- The `x` with `x² = (y² − 1)/(d·y² + 1)` and parity `sign` (`none` if there is no root);
for the root `0` the sign is ignored, as in OpenSSL (`−0 = 0`). -/
def recoverX (y : Nat) (sign : Bool) : Option Nat :=
  let u := fsub (y * y % p) 1
  let v := (d * (y * y % p) + 1) % p
  let x0 := powMod (u * v % p) ((p - 5) / 8) p * u % p
  let vxx := x0 * x0 % p * v % p
  let x? :=
    if vxx = u then some x0
    else if (vxx + u) % p = 0 then some (x0 * sqrtM1 % p)
    else none
  x?.map fun x => if (x % 2 == 1) == sign then x else fsub 0 x

def leNat (bs : Array UInt8) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

def natLE32 (n : Nat) : Array UInt8 :=
  Array.ofFn (n := 32) fun i => UInt8.ofNat ((n >>> (8 * i.1)) % 256)

/-- OpenSSL `ge_frombytes_vartime`. -/
def decodePoint (key : Array UInt8) : Option Point :=
  let v := leNat key
  let y := v % 2 ^ 255 % p
  (recoverX y (v / 2 ^ 255 % 2 == 1)).map fun x => ⟨x, y, 1, x * y % p⟩

/-- The canonical encoding: `y` below `p`, little-endian, with the parity of `x` in the top bit. -/
def encodePoint (P : Point) : Array UInt8 :=
  let zi := powMod P.Z (p - 2) p
  let x := P.X * zi % p
  let y := P.Y * zi % p
  natLE32 (y + (x % 2) * 2 ^ 255)

def basePoint : Point :=
  let y := 4 * powMod 5 (p - 2) p % p
  match recoverX y false with
  | some x => ⟨x, y, 1, x * y % p⟩
  | none => Point.zero

/-- `ossl_ed25519_verify` for a 32-byte key and a 64-byte signature. -/
def verify (msg key sig : Array UInt8) : Bool :=
  if key.size != 32 || sig.size != 64 then false
  else
    let r := sig.extract 0 32
    let s := leNat (sig.extract 32 64)
    if s ≥ L then false
    else
      match decodePoint key with
      | none => false
      | some A =>
          let h := leNat (sha512Digest (r ++ key ++ msg)) % L
          encodePoint ((Point.mul s basePoint).add (Point.mul h A).neg) == r

end TvmLean.Ed25519

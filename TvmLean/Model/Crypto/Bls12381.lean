import TvmLean.Model.Crypto.Bls12381.HashToCurve
import TvmLean.Model.Crypto.Bls12381.Pairing

/-!
# BLS12-381 operations of the `BLS_*` instructions

C++ `crypto/vm/bls.cpp` on blst (`third-party/blst` at 6d960cd, `bindings/blst.hpp`), function by
function. Points are 48-byte (G1) and 96-byte (G2) compressed encodings; `none` is a blst error,
which C++ turns into `VmError{Excno::unknown}` where it does not return `false`.

* Every point is read by `blst::P{1,2}_Affine(in, len)` / `blst::P{1,2}(in, len)`: the compression
  flag is required (else the length would have to be 96 / 192), then `decodeG1` / `decodeG2`. No
  subgroup check there.
* `blst::P{1,2}::aggregate(affine)` refuses an operand outside the subgroup
  (`BLST_POINT_NOT_IN_GROUP`): the second operand of `g{1,2}_add`, the first of `g{1,2}_sub`, every
  signature but the first of `aggregate`, every key but the first of `fast_aggregate_verify`.
* `g{1,2}_mul` returns the zero point for `x = 0` before reading the point, else multiplies by
  `x mod r` with GLV/GLS (`g1Mul`, `g2Mul`); `g{1,2}_multiexp` of one pair is `g{1,2}_mul`, of none
  the zero point, of more `blst_p{1,2}s_mult_pippenger` (`multiExp`).
* `verify`, `fast_aggregate_verify` (`p2.core_verify(p1, true, msg, DST)`) and `aggregate_verify`
  (a `blst::Pairing`) return `false` on any error; `pairing` (`raw_aggregate`, `finalverify()`)
  throws.
-/

namespace TvmLean.Bls12381

/-- `g1_zero()`: the compressed point at infinity. -/
def g1ZeroBytes : Array UInt8 := infEncoding 48

/-- `g2_zero()`. -/
def g2ZeroBytes : Array UInt8 := infEncoding 96

@[inline] private def j1 (a : Aff Nat) : Jac Nat := Jac.ofAff fpF a
@[inline] private def j2 (a : Aff Fp2) : Jac Fp2 := Jac.ofAff fp2F a

/-- `blst_core_verify_pk_in_g1(pk, sig, true, msg, DST)` (`aggregate.c`):
`PAIRING_Aggregate_PK_in_G1` with both group checks (a signature at infinity is skipped and not
checked; a key at infinity is refused), the pair `(H(msg), pk)`, then `PAIRING_FinalVerify`
against the Miller loop of `(sig, G1)` (1 for a signature at infinity). -/
def coreVerify (pk : Aff Nat) (sig : Aff Fp2) (msg : Array UInt8) : Bool :=
  let sigSet := !sig.isZero fp2F
  if sigSet && !inG2 (j2 sig) then false
  else if pk.isZero fpF then false
  else if !inG1 (j1 pk) then false
  else
    let ctx := (({} : PairingCtx).push ((hashToG2 msg).toAff fp2F) pk).commit
    ctx.finalVerify (if sigSet then millerLoopN #[(sig, g1Gen)] else .one)

/-- `bls::verify`: `false` for a key that does not decode or is at infinity, a signature that does
not decode, or `core_verify` failing. -/
def verify (pub msg sig : Array UInt8) : Bool :=
  match decodeG1 pub with
  | none => false
  | some pk =>
      if pk.isZero fpF then false
      else
        match decodeG2 sig with
        | none => false
        | some s => coreVerify pk s msg

/-- `bls::aggregate`: the sum of the signatures; `none` (a blst error) for none, a signature that
does not decode, or one after the first outside G2. -/
def aggregate (sigs : Array (Array UInt8)) : Option (Array UInt8) := Id.run do
  if sigs.isEmpty then return none
  let mut acc := Jac.inf fp2F
  for i in [0:sigs.size] do
    match decodeG2 sigs[i]! with
    | none => return none
    | some s =>
        if i > 0 && !inG2 (j2 s) then return none
        acc := Jac.add fp2F acc (j2 s)
  return some (compressG2 acc)

/-- `bls::fast_aggregate_verify`: `false` for no key, a key that does not decode or is at infinity,
a key after the first outside G1, a signature that does not decode; else `core_verify` with the sum
of the keys. -/
def fastAggregateVerify (pubs : Array (Array UInt8)) (msg sig : Array UInt8) : Bool := Id.run do
  if pubs.isEmpty then return false
  let mut acc := Jac.inf fpF
  for i in [0:pubs.size] do
    match decodeG1 pubs[i]! with
    | none => return false
    | some pk =>
        if pk.isZero fpF then return false
        if i > 0 && !inG1 (j1 pk) then return false
        acc := Jac.add fpF acc (j1 pk)
  match decodeG2 sig with
  | none => return false
  | some s => return coreVerify (acc.toAff fpF) s msg

/-- `bls::aggregate_verify`: `false` for no pair or a key that does not decode, is outside G1 or at
infinity; each pair `(H(msgᵢ), pkᵢ)` into a `blst::Pairing` (no check of repeated messages), then
the signature (decoded, in G2, else `false`) through `blst_aggregated_in_g2` and `finalverify`. -/
def aggregateVerify (pubs msgs : Array (Array UInt8)) (sig : Array UInt8) : Bool := Id.run do
  if pubs.isEmpty then return false
  let mut ctx : PairingCtx := {}
  for i in [0:pubs.size] do
    match decodeG1 pubs[i]! with
    | none => return false
    | some pk =>
        if !inG1 (j1 pk) || pk.isZero fpF then return false
        ctx := ctx.push ((hashToG2 msgs[i]!).toAff fp2F) pk
  ctx := ctx.commit
  match decodeG2 sig with
  | none => return false
  | some s =>
      if !inG2 (j2 s) then return false
      return ctx.finalVerify (millerLoopN #[(s, g1Gen)])

/-- `bls::g1_add`: `a + b`, `b` in G1. -/
def g1Add (a b : Array UInt8) : Option (Array UInt8) := do
  let pa ← decodeG1 a
  let pb ← decodeG1 b
  if inG1 (j1 pb) then some (compressG1 (Jac.add fpF (j1 pa) (j1 pb))) else none

/-- `bls::g1_sub`: `a − b`, `a` in G1. -/
def g1Sub (a b : Array UInt8) : Option (Array UInt8) := do
  let pb ← decodeG1 b
  let pa ← decodeG1 a
  if inG1 (j1 pa) then some (compressG1 (Jac.add fpF (Jac.neg fpF (j1 pb)) (j1 pa))) else none

/-- `bls::g1_neg`. -/
def g1Neg (a : Array UInt8) : Option (Array UInt8) := do
  let pa ← decodeG1 a
  some (compressG1 (Jac.neg fpF (j1 pa)))

/-- The scalar C++ passes to blst: `x mod r` (`td::RefInt256` `%` rounds to the floor). -/
def scalarOf (x : Int) : Nat := (x % Int.ofNat r).toNat

/-- `bls::g1_mul`: the zero point for `x = 0` (the point not read), else `(x mod r) · p`. -/
def g1MulInt (pt : Array UInt8) (x : Int) : Option (Array UInt8) :=
  if x = 0 then some g1ZeroBytes
  else (decodeG1 pt).map fun q => compressG1 (g1Mul (j1 q) (scalarOf x))

/-- `bls::g1_multiexp`. -/
def g1MultiExp (pts : Array (Array UInt8)) (xs : Array Int) : Option (Array UInt8) :=
  if pts.size = 0 then some g1ZeroBytes
  else if pts.size = 1 then g1MulInt pts[0]! xs[0]!
  else do
    let qs ← pts.mapM decodeG1
    some (compressG1 (multiExp fpF qs (xs.map scalarOf)))

/-- `bls::map_to_g1` of 48 bytes: `blst_fp_from_bendian` (the number taken modulo `p`), then
`blst_map_to_g1`. -/
def mapToG1Bytes (a : Array UInt8) : Array UInt8 := compressG1 (mapToG1 (beNat a 0 48 % p))

/-- `bls::g1_in_group`: `false` for an encoding that does not decode. -/
def g1InGroup (a : Array UInt8) : Bool :=
  match decodeG1 a with
  | none => false
  | some q => inG1 (j1 q)

/-- `bls::g1_is_zero`: the bytes are those of `g1_zero()` (nothing decoded). -/
def g1IsZero (a : Array UInt8) : Bool := a == g1ZeroBytes

/-- `bls::g2_add`: `a + b`, `b` in G2. -/
def g2Add (a b : Array UInt8) : Option (Array UInt8) := do
  let pa ← decodeG2 a
  let pb ← decodeG2 b
  if inG2 (j2 pb) then some (compressG2 (Jac.add fp2F (j2 pa) (j2 pb))) else none

/-- `bls::g2_sub`: `a − b`, `a` in G2. -/
def g2Sub (a b : Array UInt8) : Option (Array UInt8) := do
  let pb ← decodeG2 b
  let pa ← decodeG2 a
  if inG2 (j2 pa) then some (compressG2 (Jac.add fp2F (Jac.neg fp2F (j2 pb)) (j2 pa))) else none

/-- `bls::g2_neg`. -/
def g2Neg (a : Array UInt8) : Option (Array UInt8) := do
  let pa ← decodeG2 a
  some (compressG2 (Jac.neg fp2F (j2 pa)))

/-- `bls::g2_mul`. -/
def g2MulInt (pt : Array UInt8) (x : Int) : Option (Array UInt8) :=
  if x = 0 then some g2ZeroBytes
  else (decodeG2 pt).map fun q => compressG2 (g2Mul (j2 q) (scalarOf x))

/-- `bls::g2_multiexp`. -/
def g2MultiExp (pts : Array (Array UInt8)) (xs : Array Int) : Option (Array UInt8) :=
  if pts.size = 0 then some g2ZeroBytes
  else if pts.size = 1 then g2MulInt pts[0]! xs[0]!
  else do
    let qs ← pts.mapM decodeG2
    some (compressG2 (multiExp fp2F qs (xs.map scalarOf)))

/-- `bls::map_to_g2` of 96 bytes: `c0 ‖ c1`, each taken modulo `p`. -/
def mapToG2Bytes (a : Array UInt8) : Array UInt8 :=
  compressG2 (mapToG2 ⟨beNat a 0 48 % p, beNat a 48 96 % p⟩)

/-- `bls::g2_in_group`. -/
def g2InGroup (a : Array UInt8) : Bool :=
  match decodeG2 a with
  | none => false
  | some q => inG2 (j2 q)

/-- `bls::g2_is_zero`. -/
def g2IsZero (a : Array UInt8) : Bool := a == g2ZeroBytes

/-- `bls::pairing`: each pair decoded (`none`, a blst error, if one does not), no subgroup check,
`raw_aggregate` (a pair of two points at infinity skipped), `commit`, `finalverify()`: whether the
product of the pairings is 1; `false` when no pair was aggregated. -/
def pairing (p1s p2s : Array (Array UInt8)) : Option Bool := do
  let mut ctx : PairingCtx := {}
  for i in [0:p1s.size] do
    let a ← decodeG1 p1s[i]!
    let b ← decodeG2 p2s[i]!
    ctx := ctx.rawAggregate b a
  return ctx.commit.finalVerify .one

end TvmLean.Bls12381

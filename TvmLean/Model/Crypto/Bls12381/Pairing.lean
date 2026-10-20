import TvmLean.Model.Crypto.Bls12381.Curve

/-!
# BLS12-381: the pairing as blst computes it

blst's `pairing.c` and `aggregate.c` (TON submodule at 6d960cd), step by step: the optimal-ate
Miller loop over `|z| = 0xd201000000010000` in Jacobian coordinates (`line_dbl`, `line_add`,
`line_by_Px2`, the lines multiplied in as `xy00z0` elements), conjugated for `z < 0`, and the final
exponentiation of `final_exp` (with blst's cyclotomic squaring). The formulas are blst's, not merely
equivalent ones, so that the inputs C++ passes without checks give what blst gives: a point at
infinity is `(0, 0)` in the loop (a G2 point at infinity makes every line 0, a G1 point at
infinity leaves the lines in `Fp6`), points outside the subgroups go through the same steps, and
the batches of eight pairs of `blst_pairing_raw_aggregate` / `aggregate` are kept (a batch of one
pair with a point at infinity is 1, `miller_loop_n`).
-/

namespace TvmLean.Bls12381

namespace Fp6

/-- `a · (x + y v)`. -/
def mulBy01 (a : Fp6) (x y : Fp2) : Fp6 :=
  ⟨(a.c0.mul x).add (a.c2.mul y).mulXi, (a.c0.mul y).add (a.c1.mul x), (a.c1.mul y).add (a.c2.mul x)⟩

/-- `a · (z v)`. -/
def mulBy1 (a : Fp6) (z : Fp2) : Fp6 := ⟨(a.c2.mul z).mulXi, a.c0.mul z, a.c1.mul z⟩

end Fp6

namespace Fp12

/-- `a²` with two products of `Fp6`. -/
def sqrFast (a : Fp12) : Fp12 :=
  let t := a.c0.mul a.c1
  ⟨((a.c0.add a.c1).mul (a.c0.add a.c1.mulByV)).sub (t.add t.mulByV), t.add t⟩

/-- `mul_by_xy00z0_fp12`: `a · ((x + y v) + (z v) w)`. -/
def mulByLine (a : Fp12) (x y z : Fp2) : Fp12 :=
  let t0 := a.c0.mulBy01 x y
  let t1 := a.c1.mulBy1 z
  ⟨t0.add t1.mulByV, (a.c0.mulBy1 z).add (a.c1.mulBy01 x y)⟩

end Fp12

/-- A line `(l0, l1, l2)`: the element `(l0 + l1 v) + (l2 v) w` of `Fp12`. -/
structure Line where
  l0 : Fp2
  l1 : Fp2
  l2 : Fp2

/-- `line_dbl`: the tangent at `T` and `2T` (dbl-2009-alnr). -/
def lineDbl (t : Jac Fp2) : Line × Jac Fp2 :=
  let a := t.x.sqr
  let b := t.y.sqr
  let zz := t.z.sqr
  let c := b.sqr
  let d := ((((t.x.add b).sqr).sub a).sub c).dbl
  let e := (a.dbl).add a
  let f := e.sqr
  let x3 := (f.sub d).sub d
  let z3 := (((t.y.add t.z).sqr).sub b).sub zz
  let y3 := ((d.sub x3).mul e).sub c.dbl.dbl.dbl
  let l0 := ((((e.add t.x).sqr).sub a).sub f).sub b.dbl.dbl
  (⟨l0, e.mul zz, z3.mul zz⟩, ⟨x3, y3, z3⟩)

/-- `line_add`: the line through `T` and the affine `Q`, and `T + Q` (madd-2007-bl). -/
def lineAdd (t : Jac Fp2) (q : Aff Fp2) : Line × Jac Fp2 :=
  let z1z1 := t.z.sqr
  let u2 := q.x.mul z1z1
  let s2 := (q.y.mul t.z).mul z1z1
  let h := u2.sub t.x
  let hh := h.sqr
  let i := hh.dbl.dbl
  let j := h.mul i
  let rr := (s2.sub t.y).dbl
  let v := t.x.mul i
  let x3 := ((rr.sqr.sub j).sub v).sub v
  let jy := j.mul t.y
  let y3 := (((v.sub x3).mul rr).sub jy).sub jy
  let z3 := (((t.z.add h).sqr).sub z1z1).sub hh
  (⟨((rr.mul q.x).sub (q.y.mul z3)).dbl, rr, z3⟩, ⟨x3, y3, z3⟩)

/-- The Miller loop of one pair as `miller_loop_n` computes it (without the special case of one
pair with a point at infinity): `T = (Q.x, Q.y, 1)`, `Px2 = (−2 P.x, 2 P.y)`, the first doubling's
line as the start, then for the runs 2, 3, 9, 32, 16 of `|z|` an addition and the doublings, each
step squaring the accumulator; conjugated at the end. -/
def millerLoop (q : Aff Fp2) (pp : Aff Nat) : Fp12 := Id.run do
  let px := Fp.neg (Fp.add pp.x pp.x)
  let py := Fp.add pp.y pp.y
  let (l, t1) := lineDbl ⟨q.x, q.y, .one⟩
  let mut t := t1
  let mut f : Fp12 := ⟨⟨l.l0, l.l1.mulFp px, .zero⟩, ⟨.zero, l.l2.mulFp py, .zero⟩⟩
  for k in [2, 3, 9, 32, 16] do
    let (l, t1) := lineAdd t q
    t := t1
    f := f.mulByLine l.l0 (l.l1.mulFp px) (l.l2.mulFp py)
    for _ in [0:k] do
      f := f.sqrFast
      let (l, t1) := lineDbl t
      t := t1
      f := f.mulByLine l.l0 (l.l1.mulFp px) (l.l2.mulFp py)
  return f.conj

/-- `miller_loop_n` of a batch of pairs `(Q, P)`: the product of the loops (the loop of several
pairs runs them side by side, which multiplies to the same element), but 1 for a batch of one pair
with a point at infinity. -/
def millerLoopN (pairs : Array (Aff Fp2 × Aff Nat)) : Fp12 :=
  if pairs.size = 1 && (pairs[0]!.1.isZero fp2F || pairs[0]!.2.isZero fpF) then .one
  else pairs.foldl (fun acc (q, pp) => acc.mul (millerLoop q pp)) .one

/-- `mul_n_sqr`. -/
private def mulNSqr (ret a : Fp12) (n : Nat) : Fp12 := Id.run do
  let mut x := ret.mul a
  for _ in [0:n] do
    x := x.cyclotomicSqr
  return x

/-- `raise_to_z_div_by_2`. -/
def raiseToZDiv2 (a : Fp12) : Fp12 :=
  let x := a.cyclotomicSqr
  let x := mulNSqr x a 2
  let x := mulNSqr x a 3
  let x := mulNSqr x a 9
  let x := mulNSqr x a 32
  let x := mulNSqr x a 15
  x.conj

/-- `raise_to_z`. -/
def raiseToZ (a : Fp12) : Fp12 := (raiseToZDiv2 a).cyclotomicSqr

/-- `final_exp` (from zkcrypto), step by step. -/
def finalExp (f : Fp12) : Fp12 :=
  let ret := f.conj.mul f.inv
  let ret := ret.mul (ret.frobenius 2)
  let y0 := ret.cyclotomicSqr
  let y1 := raiseToZ y0
  let y2 := raiseToZDiv2 y1
  let y3 := ret.conj
  let y1 := (y1.mul y3).conj.mul y2
  let y2 := raiseToZ y1
  let y3 := raiseToZ y2
  let y1 := y1.conj
  let y3 := y3.mul y1
  let y1 := y1.conj.frobenius 3
  let y1 := y1.mul (y2.frobenius 2)
  let y2 := ((raiseToZ y3).mul y0).mul ret
  (y1.mul y2).mul (y3.frobenius 1)

/-- The generators (affine), as `BLS12_381_G1` and `BLS12_381_G2`. -/
def g1Gen : Aff Nat :=
  ⟨0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
   0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1⟩

def g2Gen : Aff Fp2 :=
  ⟨⟨0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
    0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e⟩,
   ⟨0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
    0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be⟩⟩

/-- The pairing context of `aggregate.c` (`PAIRING`): the pairs not yet in a Miller loop (at most
eight, `N_MAX`) and the product of the loops so far (`AGGR_GT_SET` when present). -/
structure PairingCtx where
  pending : Array (Aff Fp2 × Aff Nat) := #[]
  gt : Option Fp12 := none

namespace PairingCtx

private def withLoop (c : PairingCtx) (pairs : Array (Aff Fp2 × Aff Nat)) : PairingCtx :=
  let m := millerLoopN pairs
  { pending := #[], gt := some (match c.gt with | some g => g.mul m | none => m) }

/-- A pair `(Q, P)` into the context; a full batch of eight goes through the Miller loop. -/
def push (c : PairingCtx) (q : Aff Fp2) (pp : Aff Nat) : PairingCtx :=
  let pend := c.pending.push (q, pp)
  if pend.size = 8 then c.withLoop pend else { c with pending := pend }

/-- `blst_pairing_raw_aggregate`: skips a pair of two points at infinity. -/
def rawAggregate (c : PairingCtx) (q : Aff Fp2) (pp : Aff Nat) : PairingCtx :=
  if q.isZero fp2F && pp.isZero fpF then c else c.push q pp

/-- `PAIRING_Commit`. -/
def commit (c : PairingCtx) : PairingCtx := if c.pending.isEmpty then c else c.withLoop c.pending

/-- `PAIRING_FinalVerify` with `gtSig` the element the context is checked against: false without
any Miller loop, else whether `final_exp(conj(gtSig) · GT) = 1`. -/
def finalVerify (c : PairingCtx) (gtSig : Fp12) : Bool :=
  match c.gt with
  | none => false
  | some gt => (finalExp (gtSig.conj.mul gt)).isOne

end PairingCtx

end TvmLean.Bls12381

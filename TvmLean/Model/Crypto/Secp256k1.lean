import TvmLean.Model.Crypto.Weierstrass

/-!
secp256k1 as C++ uses it (crypto/ellcurve/secp256k1.cpp on libsecp256k1, the TON submodule at
acf5c55): `ecrecover` and `xonly_pubkey_tweak_add`. Both return the 65-byte uncompressed
serialization `04 ‖ x ‖ y`, given here as `(x, y)`.
-/

namespace TvmLean.Secp256k1

open Weierstrass

def curve : Curve where
  p := 2 ^ 256 - 2 ^ 32 - 977
  a := 0
  b := 7
  n := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
  gx := 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
  gy := 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

/-- `td::secp256k1::ecrecover` of the hash `h`, the signature `r s` and the recovery id `v`
(each of `h r s` below 2^256):
`v > 3` fails; `secp256k1_ecdsa_recoverable_signature_parse_compact` fails for `r` or `s` not below
the order `n`; `secp256k1_ecdsa_recover` takes the hash modulo `n` and `secp256k1_ecdsa_sig_recover`
fails for `r = 0` or `s = 0`, for the abscissa `r + n` (bit 1 of `v`) not below `p`, for an abscissa
off the curve, and for the point at infinity; the key is `r⁻¹ (s R − h G)` with `R` of the parity of
bit 0 of `v`. -/
def ecrecover (h r s v : Nat) : Option (Nat × Nat) :=
  let c := curve
  if v > 3 ∨ r ≥ c.n ∨ s ≥ c.n ∨ r = 0 ∨ s = 0 then none
  else if v &&& 2 ≠ 0 ∧ r ≥ c.p - c.n then none
  else
    let x := if v &&& 2 ≠ 0 then r + c.n else r
    match c.liftX x (v &&& 1 ≠ 0) with
    | none => none
    | some pt =>
        let rn := invMod r c.n
        let u1 := (c.n - h % c.n * rn % c.n) % c.n
        let u2 := s * rn % c.n
        c.toAffine (c.mulAdd u1 u2 pt)

/-- `td::secp256k1::xonly_pubkey_tweak_add` of the key `x` and the tweak `t` (below 2^256):
`secp256k1_xonly_pubkey_parse` fails for `x` not below `p` and for an abscissa off the curve, and
takes the point of even ordinate; `secp256k1_ec_pubkey_tweak_add_helper` fails for `t` not below the
order and for the point at infinity; the key is `P + t G`. -/
def xonlyPubkeyTweakAdd (x t : Nat) : Option (Nat × Nat) :=
  let c := curve
  if x ≥ c.p ∨ t ≥ c.n then none
  else
    match c.liftX x false with
    | none => none
    | some pt => c.toAffine (c.mulAdd t 1 pt)

end TvmLean.Secp256k1

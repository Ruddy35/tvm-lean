import TvmLean.Model.Cell.Cell
import TvmLean.Model.Crypto.Weierstrass

/-!
P-256 (prime256v1) signature check as C++ does it (`td::p256_check_signature`,
crypto/ellcurve/p256.cpp, on OpenSSL 3.5, the TON submodule): the 33-byte compressed key through
`EVP_PKEY_set1_tls_encodedpoint`, the signature `r ‖ s` DER-encoded, `EVP_DigestVerify` with SHA-256
of the data.
-/

namespace TvmLean.P256

open Weierstrass

def curve : Curve where
  p := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
  a := 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc
  b := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  n := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  gx := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
  gy := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

/-- Whether `sig` (64 bytes: `r ‖ s`) signs `data` under the compressed key `key` (33 bytes).
The key (OpenSSL `ossl_ec_GFp_simple_oct2point`): the first byte 2 or 3 (the parity of the
ordinate), the abscissa below `p` and on the curve. The signature (`ossl_ecdsa_simple_verify_sig`):
`r` and `s` in `[1, n)`, `e` the SHA-256 of the data (256 bits, the bits of `n`: not truncated),
`X = (e s⁻¹) G + (r s⁻¹) Q` not at infinity and `X.x mod n = r`. -/
def verify (data key sig : Array UInt8) : Bool :=
  let c := curve
  let form := key[0]!
  let x := bytesToNatBE (key.extract 1 33)
  let r := bytesToNatBE (sig.extract 0 32)
  let s := bytesToNatBE (sig.extract 32 64)
  if (form ≠ 2 ∧ form ≠ 3) ∨ x ≥ c.p then false
  else
    match c.liftX x (form = 3) with
    | none => false
    | some q =>
        if r = 0 ∨ r ≥ c.n ∨ s = 0 ∨ s ≥ c.n then false
        else
          let e := bytesToNatBE (sha256Digest data)
          let w := invMod s c.n
          match c.toAffine (c.mulAdd (e * w % c.n) (r * w % c.n) q) with
          | none => false
          | some (px, _) => px % c.n = r

end TvmLean.P256

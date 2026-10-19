#!/usr/bin/env python3
"""BLS12-381 test vectors for the BLS_* oracle cases, from py_ecc (pure Python reference of the
IETF BLS signature draft; `G2ProofOfPossession` uses the DST of C++ TVM,
"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_", `crypto/vm/bls.cpp`). Deterministic.

Output lines `kind name hex` (kind: g1 = 48-byte compressed G1 point, g2 = 96-byte compressed G2
point, msg = message bytes, fp / fp2 = field elements for BLS_MAP_TO_G1/G2, sk = scalar), plus
`sig name pk_name msg_name g2hex` for signatures. Consumed by Tests/Harness/Gen/Crypto.lean.
"""
import hashlib

from py_ecc.bls import G2ProofOfPossession as bls
from py_ecc.bls.g2_primitives import G1_to_pubkey, G2_to_signature, pubkey_to_G1, signature_to_G2
from py_ecc.bls.point_compression import compress_G1, compress_G2, decompress_G1, decompress_G2
from py_ecc.optimized_bls12_381 import (FQ, FQ2, G1, G2, Z1, Z2, add, b, b2, curve_order, field_modulus,
                                        is_inf, multiply, neg, normalize)

q = field_modulus


def g1hex(P):
    return G1_to_pubkey(P).hex()


def g2hex(P):
    return G2_to_signature(P).hex()


def sqrt_fq(a):
    y = pow(a, (q + 1) // 4, q)
    return y if y * y % q == a % q else None


def main():
    out = []
    sks = [int.from_bytes(hashlib.sha256(b"tvm-lean bls sk %d" % i).digest(), "big") % curve_order for i in range(4)]
    msgs = [b"", b"abc", b"tvm-lean", bytes(range(100))]
    for i, sk in enumerate(sks):
        out.append(f"sk sk{i} {sk:064x}")
        out.append(f"g1 pk{i} {bls.SkToPk(sk).hex()}")
    for j, m in enumerate(msgs):
        out.append(f"msg m{j} {m.hex() or '-'}")
    for i, sk in enumerate(sks):
        for j, m in enumerate(msgs):
            out.append(f"sig s{i}_{j} pk{i} m{j} {bls.Sign(sk, m).hex()}")
    # aggregates (for BLS_AGGREGATE, FASTAGGREGATEVERIFY: same message; AGGREGATEVERIFY: distinct)
    out.append(f"g2 agg012_m1 {bls.Aggregate([bls.Sign(sk, msgs[1]) for sk in sks[:3]]).hex()}")
    out.append(f"g2 agg_distinct {bls.Aggregate([bls.Sign(sks[i], msgs[i]) for i in range(3)]).hex()}")
    # group elements
    out.append(f"g1 gen {g1hex(G1)}")
    out.append(f"g1 gen2 {g1hex(multiply(G1, 2))}")
    out.append(f"g1 gen7 {g1hex(multiply(G1, 7))}")
    out.append(f"g1 genNeg {g1hex(neg(G1))}")
    out.append(f"g1 zero {g1hex(Z1)}")
    out.append(f"g2 gen {g2hex(G2)}")
    out.append(f"g2 gen2 {g2hex(multiply(G2, 2))}")
    out.append(f"g2 gen7 {g2hex(multiply(G2, 7))}")
    out.append(f"g2 genNeg {g2hex(neg(G2))}")
    out.append(f"g2 zero {g2hex(Z2)}")
    # on the curve, outside the r-subgroup
    x = 1
    while True:
        y = sqrt_fq((x ** 3 + 4) % q)
        if y is not None:
            P = (FQ(x), FQ(y), FQ(1))
            if not is_inf(multiply(P, curve_order)):
                break
        x += 1
    out.append(f"g1 noSubgroup {compress_G1(P).to_bytes(48, 'big').hex()}")
    x = 1
    while True:
        enc = (1 << 383) | x  # compressed flag, sign 0; x as the imaginary part (c1) of x
        try:
            P2 = decompress_G2((enc, 0))
            if not is_inf(multiply(P2, curve_order)):
                break
        except Exception:  # noqa: BLE001
            pass
        x += 1
    z1, z2 = compress_G2(P2)
    out.append(f"g2 noSubgroup {z1.to_bytes(48, 'big').hex()}{z2.to_bytes(48, 'big').hex()}")
    # not on the curve / bad encodings
    xb = 1
    while sqrt_fq((xb ** 3 + 4) % q) is not None:
        xb += 1
    out.append(f"g1 offCurve {((1 << 383) | xb).to_bytes(48, 'big').hex()}")
    out.append(f"g1 noCompressFlag {(int.from_bytes(G1_to_pubkey(G1), 'big') & ~(1 << 383)).to_bytes(48, 'big').hex()}")
    out.append(f"g1 xTooBig {((1 << 383) | q).to_bytes(48, 'big').hex()}")
    out.append(f"g1 infNonzero {((3 << 382) | 1).to_bytes(48, 'big').hex()}")
    gen2 = G2_to_signature(G2)
    k = 1
    while True:
        try:
            decompress_G2(((1 << 383) | 1, k))
        except Exception:  # noqa: BLE001  (no y: not on the curve)
            break
        k += 1
    out.append(f"g2 offCurve {((1 << 383) | 1).to_bytes(48, 'big').hex()}{k.to_bytes(48, 'big').hex()}")
    out.append(f"g2 noCompressFlag {(bytes([gen2[0] & 0x7f]) + gen2[1:]).hex()}")
    # field elements for MAP_TO_G1 / MAP_TO_G2 (big-endian, as blst_fp_from_bendian)
    out.append(f"fp fp0 {bytes(48).hex()}")
    out.append(f"fp fp1 {(1).to_bytes(48, 'big').hex()}")
    out.append(f"fp fpRand {(int.from_bytes(hashlib.sha512(b'fp').digest(), 'big') % q).to_bytes(48, 'big').hex()}")
    out.append(f"fp fpQ {q.to_bytes(48, 'big').hex()}")
    out.append(f"fp fpMax {(2 ** 384 - 1).to_bytes(48, 'big').hex()}")
    out.append(f"fp2 fp2Rand {(int.from_bytes(hashlib.sha512(b'fp2a').digest(), 'big') % q).to_bytes(48, 'big').hex()}"
               f"{(int.from_bytes(hashlib.sha512(b'fp2b').digest(), 'big') % q).to_bytes(48, 'big').hex()}")
    out.append(f"fp2 fp2Zero {bytes(96).hex()}")
    print("\n".join(out))


if __name__ == "__main__":
    main()

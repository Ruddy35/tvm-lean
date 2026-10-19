#!/usr/bin/env python3
"""ristretto255 encodings for the RIST255_* oracle cases (RFC 9496, pure Python, independent of
libsodium which C++ uses). Prints `name hex` lines: encodings of [k]B for small and large k, and
invalid encodings (non-canonical, negative, not on the curve). TVM passes an encoding as the
unsigned big-endian integer of its 32 bytes (`export_bytes(.., false)`)."""
import hashlib
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ed25519_vectors import B, L, add, d, mul, p, SQRTM1  # noqa: E402

INVSQRT_A_MINUS_D = 54469307008909316920995813868745141605393597292927456921205312896311721017578


def is_neg(x):
    return (x % p) & 1


def ct_abs(x):
    x %= p
    return p - x if is_neg(x) else x


def sqrt_ratio_m1(u, v):
    u %= p
    v %= p
    r = u * pow(v, 3, p) * pow(u * pow(v, 7, p), (p - 5) // 8, p) % p
    check = v * r * r % p
    correct = check == u
    flipped = check == (-u) % p
    flipped_i = check == (-u * SQRTM1) % p
    if flipped or flipped_i:
        r = r * SQRTM1 % p
    return correct or flipped, ct_abs(r)


def encode(P):
    x0, y0, z0, t0 = P
    u1 = (z0 + y0) * (z0 - y0) % p
    u2 = x0 * y0 % p
    _, invsqrt = sqrt_ratio_m1(1, u1 * u2 * u2)
    den1 = invsqrt * u1 % p
    den2 = invsqrt * u2 % p
    z_inv = den1 * den2 * t0 % p
    rotate = is_neg(t0 * z_inv)
    if rotate:
        x, y, den_inv = y0 * SQRTM1 % p, x0 * SQRTM1 % p, den1 * INVSQRT_A_MINUS_D % p
    else:
        x, y, den_inv = x0, y0, den2
    if is_neg(x * z_inv):
        y = (-y) % p
    s = ct_abs(den_inv * (z0 - y))
    return int.to_bytes(s, 32, "little")


def decode(b):
    s = int.from_bytes(b, "little")
    if s >= p or is_neg(s):
        return None
    ss = s * s % p
    u1 = (1 - ss) % p
    u2 = (1 + ss) % p
    u2sq = u2 * u2 % p
    v = (-(d * u1 * u1) - u2sq) % p
    ok, invsqrt = sqrt_ratio_m1(1, v * u2sq)
    den_x = invsqrt * u2 % p
    den_y = invsqrt * den_x * v % p
    x = ct_abs(2 * s * den_x)
    y = u1 * den_y % p
    t = x * y % p
    if not ok or is_neg(t) or y == 0:
        return None
    return (x, y, 1, t)


def main():
    assert encode(B).hex() == "e2f2ae0a6abc4e71a884a961c500515f58e30b6aa582dd8db6a65945e08d2d76"
    out = []
    for k in [0, 1, 2, 3, 4, 7, 8, 15]:
        out.append((f"mul{k}", encode(mul(k, B))))
    for i in range(3):
        k = int.from_bytes(hashlib.sha512(b"tvm-lean rist %d" % i).digest(), "little") % L
        out.append((f"rand{i}", encode(mul(k, B))))
    # invalid: s >= p (non-canonical), negative (odd) s, a non-square, and the encoding of B + 1
    out.append(("nonCanonP", int.to_bytes(p, 32, "little")))
    out.append(("nonCanonMax", int.to_bytes(2**255 - 1, 32, "little")))
    out.append(("negative1", int.to_bytes(1, 32, "little")))
    out.append(("highBit", bytes(31) + b"\x80"))
    enc_b = encode(B)
    bad = []
    for j in range(2, 200, 2):
        cand = int.to_bytes(j, 32, "little")
        if decode(cand) is None:
            bad.append(cand)
        if len(bad) == 2:
            break
    out += [(f"notOnCurve{i}", c) for i, c in enumerate(bad)]
    for name, enc in out:
        valid = decode(enc) is not None or enc == bytes(32)
        print(f"{name} {enc.hex()} {1 if valid else 0}")
    assert decode(enc_b) is not None


if __name__ == "__main__":
    main()

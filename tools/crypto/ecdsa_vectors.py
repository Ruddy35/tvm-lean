#!/usr/bin/env python3
"""ECDSA test vectors for the ECRECOVER, SECP256K1_XONLY_PUBKEY_TWEAK_ADD and P256_CHKSIGN{U,S}
oracle cases. Pure Python (short Weierstrass arithmetic), independent of the model and of the
libraries C++ uses (libsecp256k1, OpenSSL); deterministic.

Output lines (consumed by Tests/Harness/Gen/Crypto.lean via gen_lean_vectors.py):
  ecrecover <name> <hash> <v> <r> <s> <expected>        (decimal v; 32-byte hex hash, r, s)
  tweak     <name> <xonly_key> <tweak> <expected>       (32-byte hex)
  p256      <name> <U|S> <key33> <sig64> <data> <0|1>   (data: hex, `-` if empty)
<expected>: the 65-byte uncompressed public key (04 x y) the operation returns, `-` if it fails
(ECRECOVER as at global version 13, where v must be 0..3), computed here with the semantics of
libsecp256k1 (secp256k1_ecdsa_recover, secp256k1_xonly_pubkey_tweak_add) and OpenSSL
(ECDSA verification of SHA-256(data), any s in [1, n-1]).
"""
import hashlib


class Curve:
    def __init__(self, p, a, b, n, gx, gy):
        self.p, self.a, self.b, self.n, self.G = p, a, b, n, (gx, gy)

    def add(self, P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        p = self.p
        if P[0] == Q[0] and (P[1] + Q[1]) % p == 0:
            return None
        if P == Q:
            lam = (3 * P[0] * P[0] + self.a) * pow(2 * P[1], p - 2, p) % p
        else:
            lam = (Q[1] - P[1]) * pow(Q[0] - P[0], p - 2, p) % p
        x = (lam * lam - P[0] - Q[0]) % p
        return (x, (lam * (P[0] - x) - P[1]) % p)

    def mul(self, k, P):
        R = None
        while k:
            if k & 1:
                R = self.add(R, P)
            P = self.add(P, P)
            k >>= 1
        return R

    def lift_x(self, x, odd):
        p = self.p
        y2 = (x * x * x + self.a * x + self.b) % p
        y = pow(y2, (p + 1) // 4, p)  # both primes are 3 mod 4
        if y * y % p != y2:
            return None
        return (x, y if (y & 1) == odd else p - y)

    def sign(self, d, z, k):
        """(r, s, recid) for the hash value z with nonce k."""
        R = self.mul(k, self.G)
        r = R[0] % self.n
        s = pow(k, self.n - 2, self.n) * (z + r * d) % self.n
        recid = (R[1] & 1) | (2 if R[0] >= self.n else 0)
        return r, s, recid


SECP = Curve(2**256 - 2**32 - 977, 0, 7,
             0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
             0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
             0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
P256 = Curve(0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF,
             0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC,
             0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B,
             0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
             0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
             0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5)


def h32(i, tag):
    return hashlib.sha256(b"tvm-lean %s %d" % (tag, i)).digest()


def hx(n, size=32):
    return int.to_bytes(n, size, "big").hex()


def enc65(P):
    return "-" if P is None else "04" + int.to_bytes(P[0], 32, "big").hex() + int.to_bytes(P[1], 32, "big").hex()


def recover(z, v, r, s):
    """libsecp256k1 recovery (signature[64] = v must be 0..3: crypto/ellcurve/secp256k1.cpp)."""
    C = SECP
    if v > 3 or r >= C.n or s >= C.n or r == 0 or s == 0:
        return None
    x = r + (C.n if v & 2 else 0)
    if x >= C.p:
        return None
    R = C.lift_x(x, v & 1)
    if R is None:
        return None
    rinv = pow(r, C.n - 2, C.n)
    return C.add(C.mul(s * rinv % C.n, R), C.mul((-(z % C.n) * rinv) % C.n, C.G))


def tweak_add(x, t):
    """secp256k1_xonly_pubkey_parse + secp256k1_xonly_pubkey_tweak_add."""
    C = SECP
    if x >= C.p:
        return None
    P = C.lift_x(x, 0)
    if P is None or t >= C.n:
        return None
    return C.add(P, C.mul(t, C.G)) if t else P


def p256_verify(key, sig, data):
    C = P256
    if key[0] not in (2, 3):
        return False
    x = int.from_bytes(key[1:], "big")
    if x >= C.p:
        return False
    Q = C.lift_x(x, key[0] & 1)
    if Q is None:
        return False
    r, s = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:], "big")
    if not (0 < r < C.n and 0 < s < C.n):
        return False
    z = int.from_bytes(hashlib.sha256(data).digest(), "big")
    w = pow(s, C.n - 2, C.n)
    X = C.add(C.mul(z * w % C.n, C.G), C.mul(r * w % C.n, Q))
    return X is not None and X[0] % C.n == r


def main():
    out = []
    # ECRECOVER: hash v r s
    for i in range(4):
        d = int.from_bytes(h32(i, b"secp key"), "big") % SECP.n
        z = h32(i, b"secp msg")
        k = int.from_bytes(h32(i, b"secp nonce"), "big") % SECP.n
        r, s, recid = SECP.sign(d, int.from_bytes(z, "big"), k)
        out.append(f"ecrecover valid{i} {z.hex()} {recid} {hx(r)} {hx(s)}")
        if i == 0:
            out.append(f"ecrecover legacy27 {z.hex()} {recid + 27} {hx(r)} {hx(s)}")
            out.append(f"ecrecover wrongRecid {z.hex()} {recid ^ 1} {hx(r)} {hx(s)}")
            out.append(f"ecrecover recid2 {z.hex()} {recid | 2} {hx(r)} {hx(s)}")
            out.append(f"ecrecover recid4 {z.hex()} 4 {hx(r)} {hx(s)}")
            out.append(f"ecrecover v29 {z.hex()} 29 {hx(r)} {hx(s)}")
            out.append(f"ecrecover highS {z.hex()} {recid ^ 1} {hx(r)} {hx(SECP.n - s)}")
            out.append(f"ecrecover wrongHash {h32(99, b'secp msg').hex()} {recid} {hx(r)} {hx(s)}")
            out.append(f"ecrecover r0 {z.hex()} {recid} {hx(0)} {hx(s)}")
            out.append(f"ecrecover s0 {z.hex()} {recid} {hx(r)} {hx(0)}")
            out.append(f"ecrecover rN {z.hex()} {recid} {hx(SECP.n)} {hx(s)}")
            out.append(f"ecrecover sN {z.hex()} {recid} {hx(r)} {hx(SECP.n)}")
            out.append(f"ecrecover rMax {z.hex()} {recid} {hx(2**256 - 1)} {hx(s)}")
            out.append(f"ecrecover hash0 {hx(0)} {recid} {hx(r)} {hx(s)}")
    # an r that is not the x-coordinate of a curve point
    x = 5
    while SECP.lift_x(x, 0) is not None:
        x += 1
    out.append(f"ecrecover rOffCurve {h32(0, b'secp msg').hex()} 0 {hx(x)} {hx(12345)}")
    # SECP256K1_XONLY_PUBKEY_TWEAK_ADD: key tweak
    for i in range(3):
        d = int.from_bytes(h32(i, b"tweak key"), "big") % SECP.n
        P = SECP.mul(d, SECP.G)
        t = int.from_bytes(h32(i, b"tweak"), "big") % SECP.n
        out.append(f"tweak valid{i} {hx(P[0])} {hx(t)}")
    d = int.from_bytes(h32(0, b"tweak key"), "big") % SECP.n
    P = SECP.mul(d, SECP.G)
    de = d if P[1] % 2 == 0 else SECP.n - d  # the even-y point lift_x(P.x) = [de]G
    out.append(f"tweak tweak0 {hx(P[0])} {hx(0)}")
    out.append(f"tweak tweakN {hx(P[0])} {hx(SECP.n)}")
    out.append(f"tweak tweakMax {hx(P[0])} {hx(2**256 - 1)}")
    out.append(f"tweak toInfinity {hx(P[0])} {hx(SECP.n - de)}")
    out.append(f"tweak keyOffCurve {hx(x)} {hx(7)}")
    out.append(f"tweak keyP {hx(SECP.p)} {hx(7)}")
    out.append(f"tweak key0 {hx(0)} {hx(7)}")
    out.append(f"tweak generator {hx(SECP.G[0])} {hx(1)}")
    # P256_CHKSIGNU (data = the 32-byte hash, hashed again with SHA-256 by OpenSSL) and P256_CHKSIGNS
    for i, data in enumerate([h32(0, b"p256 msg"), h32(1, b"p256 msg"), b"", b"abc", bytes(range(127))]):
        d = int.from_bytes(h32(i, b"p256 key"), "big") % P256.n
        Q = P256.mul(d, P256.G)
        key = bytes([2 | (Q[1] & 1)]) + int.to_bytes(Q[0], 32, "big")
        z = int.from_bytes(hashlib.sha256(data).digest(), "big")
        k = int.from_bytes(h32(i, b"p256 nonce"), "big") % P256.n
        r, s, _ = P256.sign(d, z, k)
        kind = "U" if len(data) == 32 else "S"
        sig = int.to_bytes(r, 32, "big") + int.to_bytes(s, 32, "big")
        out.append(f"p256 valid{i} {kind} {key.hex()} {sig.hex()} {data.hex() or '-'}")
        if i == 0:
            hs = int.to_bytes(r, 32, "big") + int.to_bytes(P256.n - s, 32, "big")
            out.append(f"p256 highS {kind} {key.hex()} {hs.hex()} {data.hex()}")
            out.append(f"p256 wrongData {kind} {key.hex()} {sig.hex()} {h32(9, b'p256 msg').hex()}")
            out.append(f"p256 wrongParity {kind} {bytes([key[0] ^ 1]).hex() + key[1:].hex()} {sig.hex()} {data.hex()}")
            out.append(f"p256 prefix04 {kind} {'04' + key[1:].hex()} {sig.hex()} {data.hex()}")
            out.append(f"p256 prefix00 {kind} {'00' + key[1:].hex()} {sig.hex()} {data.hex()}")
            out.append(f"p256 r0 {kind} {key.hex()} {(bytes(32) + sig[32:]).hex()} {data.hex()}")
            out.append(f"p256 s0 {kind} {key.hex()} {(sig[:32] + bytes(32)).hex()} {data.hex()}")
            out.append(f"p256 rN {kind} {key.hex()} {(int.to_bytes(P256.n, 32, 'big') + sig[32:]).hex()} {data.hex()}")
            out.append(f"p256 sN {kind} {key.hex()} {(sig[:32] + int.to_bytes(P256.n, 32, 'big')).hex()} {data.hex()}")
            xo = 1
            while P256.lift_x(xo, 0) is not None:
                xo += 1
            out.append(f"p256 keyOffCurve {kind} {'02' + hx(xo)} {sig.hex()} {data.hex()}")
            out.append(f"p256 keyXp {kind} {'02' + hx(P256.p)} {sig.hex()} {data.hex()}")
    final = []
    for line in out:
        p = line.split()
        if p[0] == "ecrecover":
            exp = enc65(recover(int(p[2], 16), int(p[3]), int(p[4], 16), int(p[5], 16)))
        elif p[0] == "tweak":
            exp = enc65(tweak_add(int(p[2], 16), int(p[3], 16)))
        else:
            data = b"" if p[5] == "-" else bytes.fromhex(p[5])
            exp = "1" if p256_verify(bytes.fromhex(p[3]), bytes.fromhex(p[4]), data) else "0"
        final.append(f"{line} {exp}")
    print("\n".join(final))


if __name__ == "__main__":
    main()

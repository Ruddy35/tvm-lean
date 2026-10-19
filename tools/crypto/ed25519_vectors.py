#!/usr/bin/env python3
"""Ed25519 test vectors for the CHKSIGNU/CHKSIGNS oracle cases.

Independent of the model: pure-Python Ed25519 after RFC 8032 (section 5.1, reference code style).

C++ (crypto/Ed25519.cpp, `Ed25519::PublicKey::verify_signature`) verifies through OpenSSL
(`EVP_DigestVerify` -> `ossl_ed25519_verify`, crypto/ec/curve25519.c): S < L, the public key decoded
without a canonicity or small-order check, h = SHA512(R || A || M) mod L, and the strict equation
ENC([S]B - [h]A) == R. Besides ordinary signatures this script builds signatures that satisfy that
equation for small-order and mixed-order public keys and small-order R (other verifiers, e.g.
libsodium, reject them), and keys with non-canonical encodings.

Output: one line per vector, `name kind key_hex sig_hex msg_hex expected` (expected: 1 = the strict
equation holds, 0 = it does not; an empty message is `-`), consumed by Tests/Harness/Gen/Crypto.lean (pasted as constants).
"""
import hashlib

p = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
d = -121665 * pow(121666, p - 2, p) % p
SQRTM1 = pow(2, (p - 1) // 4, p)


def sha512(b):
    return hashlib.sha512(b).digest()


def inv(x):
    return pow(x, p - 2, p)


# points in extended coordinates (X, Y, Z, T), x = X/Z, y = Y/Z, x*y = T/Z
def add(P, Q):
    A = (P[1] - P[0]) * (Q[1] - Q[0]) % p
    B = (P[1] + P[0]) * (Q[1] + Q[0]) % p
    C = 2 * P[3] * Q[3] * d % p
    D = 2 * P[2] * Q[2] % p
    E, F, G, H = B - A, D - C, D + C, B + A
    return (E * F % p, G * H % p, F * G % p, E * H % p)


def mul(s, P):
    Q = (0, 1, 1, 0)
    while s > 0:
        if s & 1:
            Q = add(Q, P)
        P = add(P, P)
        s >>= 1
    return Q


def neg(P):
    return ((-P[0]) % p, P[1], P[2], (-P[3]) % p)


def eq(P, Q):
    return (P[0] * Q[2] - Q[0] * P[2]) % p == 0 and (P[1] * Q[2] - Q[1] * P[2]) % p == 0


def recover_x(y, sign):
    """x from y as OpenSSL ge_frombytes_vartime does (y already reduced mod p); None if no x."""
    x2 = (y * y - 1) * inv(d * y * y + 1) % p
    x = pow(x2, (p + 3) // 8, p)
    if (x * x - x2) % p != 0:
        x = x * SQRTM1 % p
    if (x * x - x2) % p != 0:
        return None
    if (x & 1) != sign:
        x = (-x) % p
    return x


def decode(b):
    """OpenSSL decoding: low 255 bits as y (not required to be < p), sign bit; None if not on curve."""
    v = int.from_bytes(b, "little")
    y = (v & ((1 << 255) - 1)) % p
    x = recover_x(y, v >> 255)
    if x is None:
        return None
    return (x, y, 1, x * y % p)


def encode(P):
    zi = inv(P[2])
    x, y = P[0] * zi % p, P[1] * zi % p
    return int.to_bytes(y | ((x & 1) << 255), 32, "little")


By = 4 * inv(5) % p
B = (recover_x(By, 0), By, 1, recover_x(By, 0) * By % p)


def secret_expand(seed):
    h = sha512(seed)
    a = int.from_bytes(h[:32], "little")
    a &= (1 << 254) - 8
    a |= 1 << 254
    return a, h[32:]


def public_key(seed):
    a, _ = secret_expand(seed)
    return encode(mul(a, B))


def sign(seed, msg):
    a, prefix = secret_expand(seed)
    A = encode(mul(a, B))
    r = int.from_bytes(sha512(prefix + msg), "little") % L
    R = encode(mul(r, B))
    h = int.from_bytes(sha512(R + A + msg), "little") % L
    s = (r + h * a) % L
    return A, R + int.to_bytes(s, 32, "little")


def verify_strict(key, sig, msg):
    """The equation checked by OpenSSL ossl_ed25519_verify."""
    if len(key) != 32 or len(sig) != 64:
        return False
    s = int.from_bytes(sig[32:], "little")
    if s >= L:
        return False
    A = decode(key)
    if A is None:
        return False
    h = int.from_bytes(sha512(sig[:32] + key + msg), "little") % L
    return encode(add(mul(s, B), neg(mul(h, A)))) == sig[:32]


# the 8-torsion: T8 generates it (order 8)
T8 = decode(bytes.fromhex("26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05"))
TORSION = [mul(k, T8) for k in range(8)]


def forge(key_point_b, mult_a, msgs):
    """A signature over some message of `msgs` for the key `key_point_b` (bytes; the point is
    [mult_a]B + torsion): S = h*mult_a, R the torsion part of -[h]A. Returns (msg, sig) or None."""
    A = decode(key_point_b)
    for msg in msgs:
        for Rt in TORSION:
            R = encode(Rt)
            h = int.from_bytes(sha512(R + key_point_b + msg), "little") % L
            s = h * mult_a % L
            sig = R + int.to_bytes(s, 32, "little")
            if verify_strict(key_point_b, sig, msg):
                return msg, sig
    return None


def msg32(i):
    return hashlib.sha256(b"tvm-lean chksign %d" % i).digest()


def main():
    out = []

    def emit(name, kind, key, sig, msg):
        out.append(f"{name} {kind} {key.hex()} {sig.hex()} {msg.hex() or '-'} {1 if verify_strict(key, sig, msg) else 0}")

    seeds = [hashlib.sha256(b"tvm-lean ed25519 seed %d" % i).digest() for i in range(3)]
    # RFC 8032 test 1 key, test 2 and test 3 messages (CHKSIGNS data)
    rfc_seed = bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
    for i, seed in enumerate(seeds):
        k, sig = sign(seed, msg32(i))
        emit(f"valid{i}", "U", k, sig, msg32(i))
        # wrong message, flipped bits in R and S, wrong key
        emit(f"wrongmsg{i}", "U", k, sig, msg32(i + 100))
        emit(f"flipR{i}", "U", k, bytes([sig[0] ^ 1]) + sig[1:], msg32(i))
        emit(f"flipS{i}", "U", k, sig[:32] + bytes([sig[32] ^ 1]) + sig[33:], msg32(i))
        # S + L: same group element, non-canonical scalar
        sL = int.from_bytes(sig[32:], "little") + L
        if sL < 2**256:
            emit(f"sPlusL{i}", "U", k, sig[:32] + int.to_bytes(sL, 32, "little"), msg32(i))
    for n, m in [(0, b""), (1, bytes.fromhex("72")), (2, bytes.fromhex("af82")),
                 (127, bytes(range(127))), (64, bytes(64)), (100, hashlib.sha512(b"x").digest() * 2)]:
        m = m[:n]
        k, sig = sign(rfc_seed, m)
        emit(f"validS{n}", "S", k, sig, m)
    # small-order keys: canonical encodings of the 8 torsion points, plus non-canonical ones
    for j, T in enumerate(TORSION):
        kb = encode(T)
        f = forge(kb, 0, [msg32(1000 + 8 * j + t) for t in range(64)])
        if f:
            emit(f"smallKey{j}", "U", kb, f[1], f[0])
    for name, kb in [("ncIdentity", int.to_bytes(p + 1, 32, "little")),
                     ("ncY0", int.to_bytes(p, 32, "little")),
                     ("ncY0neg", int.to_bytes(p | (1 << 255), 32, "little")),
                     ("y0neg", int.to_bytes(1 << 255, 32, "little")),
                     ("identityNeg", int.to_bytes(1 | (1 << 255), 32, "little"))]:
        if decode(kb) is None:
            continue
        f = forge(kb, 0, [msg32(2000 + t) for t in range(64)])
        if f:
            emit(name, "U", kb, f[1], f[0])
    # mixed-order key [a]B + T8 with small-order R
    a = 0x1234567890abcdef
    for j in (1, 4):
        kb = encode(add(mul(a, B), TORSION[j]))
        f = forge(kb, a, [msg32(3000 + 8 * j + t) for t in range(64)])
        if f:
            emit(f"mixedKey{j}", "U", kb, f[1], f[0])
    # a point that is not on the curve (no square root): rejected
    y = 2
    while recover_x(y, 0) is not None:
        y += 1
    k, sig = sign(seeds[0], msg32(0))
    emit("offCurveKey", "U", int.to_bytes(y, 32, "little"), sig, msg32(0))
    print("\n".join(out))


if __name__ == "__main__":
    main()

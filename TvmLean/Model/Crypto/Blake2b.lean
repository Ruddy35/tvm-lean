/-!
BLAKE2b-512 (RFC 7693) as C++ computes it for `HASHEXT` (crypto/vm/Hasher.cpp: OpenSSL
`EVP_blake2b512`): no key, a 64-byte digest, 12 rounds.
-/

namespace TvmLean.Blake2b

/-- The initialization vector (the SHA-512 one). -/
def iv : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The message schedule σ of the ten rounds (round `r` uses `sigma[r % 10]`). -/
def sigma : Array (Array Nat) :=
  #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

def rotr (a : UInt64) (n : UInt64) : UInt64 := (a >>> n) ||| (a <<< (64 - n))

/-- The mixing function G on the words `a b c d` of `v` with the message words `x y`. -/
def mix (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 := Id.run do
  let mut v := v
  v := v.set! a (v[a]! + v[b]! + x)
  v := v.set! d (rotr (v[d]! ^^^ v[a]!) 32)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr (v[b]! ^^^ v[c]!) 24)
  v := v.set! a (v[a]! + v[b]! + y)
  v := v.set! d (rotr (v[d]! ^^^ v[a]!) 16)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr (v[b]! ^^^ v[c]!) 63)
  return v

/-- The little-endian 64-bit word of `bytes` at `pos`. -/
def leWord (bytes : ByteArray) (pos : Nat) : UInt64 :=
  (List.range 8).foldl (fun w k => w ||| ((bytes.get! (pos + k)).toUInt64 <<< (8 * k).toUInt64)) 0

/-- The compression function F of the state `h` with the block of 128 bytes of `data` at `pos`,
`t` bytes counted so far, `last` for the final block. -/
def compress (h : Array UInt64) (data : ByteArray) (pos t : Nat) (last : Bool) : Array UInt64 := Id.run do
  let m : Array UInt64 := (Array.range 16).map fun i => leWord data (pos + 8 * i)
  let mut v : Array UInt64 := h ++ iv
  v := v.set! 12 (v[12]! ^^^ t.toUInt64)
  v := v.set! 13 (v[13]! ^^^ (t / 2 ^ 64).toUInt64)
  if last then
    v := v.set! 14 (~~~ v[14]!)
  for r in [0:12] do
    let s := sigma[r % 10]!
    v := mix v 0 4 8 12 m[s[0]!]! m[s[1]!]!
    v := mix v 1 5 9 13 m[s[2]!]! m[s[3]!]!
    v := mix v 2 6 10 14 m[s[4]!]! m[s[5]!]!
    v := mix v 3 7 11 15 m[s[6]!]! m[s[7]!]!
    v := mix v 0 5 10 15 m[s[8]!]! m[s[9]!]!
    v := mix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    v := mix v 2 7 8 13 m[s[12]!]! m[s[13]!]!
    v := mix v 3 4 9 14 m[s[14]!]! m[s[15]!]!
  return (Array.range 8).map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]!

/-- BLAKE2b-512 of `msg`: the blocks of 128 bytes, the last one (possibly partial, zero-padded, or
an empty block for an empty message) compressed as final. -/
def blake2b512 (msg : ByteArray) : ByteArray := Id.run do
  let n := msg.size
  let blocks : Nat := if n = 0 then 1 else (n + 127) / 128
  let data := msg ++ ByteArray.mk (Array.replicate (blocks * 128 - n) 0)
  let mut h : Array UInt64 := iv.set! 0 (iv[0]! ^^^ 0x01010040)
  for b in [0:blocks] do
    let last := b + 1 = blocks
    let t := if last then n else (b + 1) * 128
    h := compress h data (b * 128) t last
  let mut out : Array UInt8 := #[]
  for k in [0:64] do
    out := out.push (h[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8
  return ByteArray.mk out

end TvmLean.Blake2b

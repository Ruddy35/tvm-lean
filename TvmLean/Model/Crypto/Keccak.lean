/-!
Keccak-256 and Keccak-512 as C++ computes them for `HASHEXT` (crypto/vm/Hasher.cpp,
`HasherImplKeccak`, on crypto/keccak/keccak.cpp): the Keccak-f[1600] permutation with 24 rounds, a
capacity of twice the digest, the original Keccak padding (a byte 0x01 after the message, 0x80 in
the last byte of the block: `keccak_digest(…, padding = 1)`), lanes in little-endian order.
-/

namespace TvmLean.Keccak

/-- The round constants of the step ι (keccak.cpp:279-284). -/
def roundConstants : Array UInt64 :=
  #[0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000, 0x000000000000808b,
    0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008a, 0x0000000000000088,
    0x0000000080008009, 0x000000008000000a, 0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation of the lane `x + 5 y` in the step ρ. -/
def rotOffsets : Array Nat :=
  #[0, 1, 62, 28, 27,
    36, 44, 6, 55, 20,
    3, 10, 43, 25, 39,
    41, 45, 15, 21, 8,
    18, 2, 61, 56, 14]

def rotl (a : UInt64) (n : Nat) : UInt64 :=
  if n = 0 then a else (a <<< n.toUInt64) ||| (a >>> (64 - n).toUInt64)

/-- One round (θ, ρ, π, χ, ι) on the 25 lanes, lane `x + 5 y`. -/
def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let c : Array UInt64 := (Array.range 5).map fun x => a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!
  let d : Array UInt64 := (Array.range 5).map fun x => c[(x + 4) % 5]! ^^^ rotl c[(x + 1) % 5]! 1
  let a : Array UInt64 := (Array.range 25).map fun i => a[i]! ^^^ d[i % 5]!
  -- ρ and π: B[y, 2x + 3y] = rot(A[x, y])
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl a[x + 5 * y]! rotOffsets[x + 5 * y]!)
  let a : Array UInt64 := (Array.range 25).map fun i =>
    let x := i % 5
    let y := i / 5
    b[i]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!)
  return a.set! 0 (a[0]! ^^^ rc)

/-- Keccak-f[1600], 24 rounds. -/
def permute (a : Array UInt64) : Array UInt64 :=
  roundConstants.foldl round a

/-- The little-endian 64-bit word of `bytes` at `pos`. -/
def leWord (bytes : ByteArray) (pos : Nat) : UInt64 :=
  (List.range 8).foldl (fun w k => w ||| ((bytes.get! (pos + k)).toUInt64 <<< (8 * k).toUInt64)) 0

/-- The sponge with a block of `rate` bytes (a multiple of 8, below 200) and `outLen` bytes of
output (at most `rate`): the message padded with 0x01 … 0x80 to whole blocks, each block XORed into
the first lanes and permuted, then the first `outLen` bytes of the lanes. -/
def sponge (rate outLen : Nat) (msg : ByteArray) : ByteArray := Id.run do
  let padLen : Nat := rate - msg.size % rate
  let pad : ByteArray :=
    if padLen = 1 then ByteArray.mk #[0x81]
    else ByteArray.mk (#[0x01] ++ Array.replicate (padLen - 2) 0 ++ #[0x80])
  let data := msg ++ pad
  let mut st : Array UInt64 := Array.replicate 25 0
  for blk in [0:data.size / rate] do
    for i in [0:rate / 8] do
      st := st.set! i (st[i]! ^^^ leWord data (blk * rate + 8 * i))
    st := permute st
  let mut out : Array UInt8 := #[]
  for k in [0:outLen] do
    out := out.push (st[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8
  return ByteArray.mk out

/-- Keccak-256: capacity 64 bytes, rate 136. -/
def keccak256 (msg : ByteArray) : ByteArray := sponge 136 32 msg

/-- Keccak-512: capacity 128 bytes, rate 72. -/
def keccak512 (msg : ByteArray) : ByteArray := sponge 72 64 msg

end TvmLean.Keccak

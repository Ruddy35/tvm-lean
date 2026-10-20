import Tests.Harness.Registry
import Tests.Harness.Gen.CryptoVectors

/-!
Oracle cases for the crypto instructions (C++ `tonops.cpp`).

Hash instructions (`exec_compute_hash`, `exec_compute_sha256`, `exec_hash_ext`, `Hasher.cpp`):
HASHCU on ordinary and exotic cells (library, pruned branches, an ordinary cell of level > 0),
HASHSU, HASHBU, SHA256U and HASHEXT{A}{R} with every hash algorithm (sha256, sha512, blake2b,
keccak256, keccak512), the algorithm taken from the stack, invalid algorithms, slices and builders
mixed, data that is not byte-aligned, appending to a builder (and overflowing it), reversed order,
and gas running out between the entries of HASHEXT (`SETGASLIMIT` before it: C++ charges each
entry with `consume_gas`, which throws at the first overrun). Results, exceptions and the per-byte
gas are compared with C++. The digests, computed in Lean, on data of the lengths around the blocks of
each hash (`hashExtLengths`) and on random data (`fuzzFor`).
-/

namespace Tests.Gen.Crypto

open TvmLean

private def iv (n : Int) : Value := .int (.num n)
private def sl (bits : BitString) : Value := .slice (Slice.ofCell (Cell.mkOrdinary bits #[]))
private def bl (bits : BitString) : Value := .builder { bits := bits, refs := #[] }

private def cross (suite : String) (variants : Array (String × Instr)) (stacks : Array (Array Value)) :
    Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for (vl, i) in variants do
    for k in [0:stacks.size] do
      out := out.push
        { name := s!"oracle/{vl}/stack{k}", instr := { name := suite }, program := #[i],
          initStack := stacks[k]! }
  return out

private def bytes (n : Nat) (seed : Nat) : BitString := natToBits (seed % (2 ^ (8 * n))) (8 * n)

private def bitsOfBytes (bs : Array UInt8) : BitString :=
  bs.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

/-- Library cell (exotic type 2, level 0). -/
private def libraryCell : Cell :=
  { bits := natToBits 2 8 ++ natToBits 0x9a9a 256, refs := #[], special := true, levelMask := 0 }

/-- Pruned branch with level mask `mask` (exotic type 1): one hash and one depth per level. -/
private def prunedCell (mask : Nat) (seed : Nat) : Cell :=
  let n := LevelMask.getHashI mask
  let hashes : Array UInt8 := Array.ofFn (n := n * 32) fun i => UInt8.ofNat ((seed + i.1 * 37) % 256)
  let depths : Array UInt8 := Array.ofFn (n := n * 2) fun i => UInt8.ofNat (if i.1 % 2 = 0 then 0 else seed % 200 + i.1)
  { bits := bitsOfBytes (#[1, UInt8.ofNat mask] ++ hashes ++ depths), refs := #[], special := true,
    levelMask := mask }

private def cellPool : Array Cell :=
  let c1 := Cell.mkOrdinary (bytes 4 0xdeadbeef) #[]
  #[ Cell.empty, c1, Cell.mkOrdinary (natToBits 5 3) #[c1, c1], Cell.mkOrdinary (bytes 127 7) #[],
     libraryCell, prunedCell 1 3, prunedCell 7 11,
     -- an ordinary cell of level 1 (its hash is the representation hash, above the pruned level)
     Cell.mkOrdinary (bytes 2 0x1234) #[prunedCell 1 5, c1] ]

/-- Data pieces for HASHEXT: byte-aligned slices and builders of several lengths. -/
private def pieces : Array Value :=
  #[ sl #[], sl (bytes 1 0x61), sl (bytes 32 0x1234567), bl (bytes 3 0x616263), bl (bytes 100 9),
     sl (bytes 127 3) ]

private def unaligned : Value := sl (natToBits 5 3)

/-- HASHEXT stacks: `[builder (append)] x[n-1] .. x[0] n [id (from stack)]`. -/
private def hashExtStacks (append fromStack : Bool) : Array (Array Value) := Id.run do
  let mut out : Array (Array Value) := #[]
  let pre : Array Value := if append then #[bl (bytes 2 0xffee)] else #[]
  let ids : Array Int := if fromStack then #[0, 1, 2, 3, 4, 5, 254, 255, -1] else #[0]
  for idv in ids do
    let post : Array Value := if fromStack then #[iv idv] else #[]
    for n in [0:4] do
      out := out.push (pre ++ (pieces.extract 0 n) ++ #[iv (Int.ofNat n)] ++ post)
    out := out.push (pre ++ #[pieces[2]!, pieces[4]!, pieces[5]!] ++ #[iv 3] ++ post)
    -- a piece that is not a whole number of bytes alone, and completed by the next one
    out := out.push (pre ++ #[unaligned, iv 1] ++ post)
    out := out.push (pre ++ #[unaligned, sl (natToBits 7 3), iv 2] ++ post)
    -- an entry that is neither a slice nor a builder, after a valid one
    out := out.push (pre ++ #[pieces[1]!, iv 7, iv 2] ++ post)
    out := out.push (pre ++ #[pieces[1]!, iv 2] ++ post)
    out := out.push (pre ++ #[iv (-1)] ++ post)
    out := out.push (pre ++ #[.null] ++ post)
  if append then
    -- the digest does not fit into the builder (cell_ov)
    out := out.push #[bl (bytes 125 1), pieces[1]!, iv 1]
    out := out.push #[.null, pieces[1]!, iv 1]
  return out

/-- HASHEXT with the gas limit lowered by `SETGASLIMIT` right before it, swept over the limits
around the per-entry charges (`(i+1) + bytes/bytes_per_gas` after each entry): data of three
127-byte entries, then an entry that is not a slice. C++ throws out_of_gas at the first entry
that overruns the limit; the non-slice entry is never reached. -/
private def hashExtGasCases (suite : String) (append rev : Bool) : Array OracleCase := Id.run do
  let big := sl (bytes 127 5)
  let entries : Array Value := if rev then #[.null, big, big, big] else #[big, big, big, .null]
  let pre : Array Value := if append then #[bl #[]] else #[]
  let mut out : Array OracleCase := #[]
  for id in [0, 4] do
    for lim in [84:142] do
      out := out.push
        { name := s!"oracle/gas/id{id}/limit{lim}", instr := { name := suite },
          program := #[.pushInt (.num (Int.ofNat lim)), .tonEnvOp .setGasLimit, .cryptoOp (.hashExt id append rev)],
          initStack := pre ++ entries ++ #[iv 4] }
      out := out.push
        { name := s!"oracle/gas-valid/id{id}/limit{lim}", instr := { name := suite },
          program := #[.pushInt (.num (Int.ofNat lim)), .tonEnvOp .setGasLimit, .cryptoOp (.hashExt id append rev)],
          initStack := pre ++ #[big, big, big, iv 3] }
  return out

/-- `n` bytes of varying content. -/
private def noise (n seed : Nat) : BitString :=
  bitsOfBytes (Array.ofFn (n := n) fun i => UInt8.ofNat ((seed * 131 + i.1 * 197 + i.1 * i.1 * 7) % 256))

/-- Data lengths in bytes around the blocks of the hashes, where the padding takes one more byte,
a few, or a whole block: 64 bytes of SHA-256, 128 of SHA-512 and BLAKE2b, 136 of Keccak-256, 72 of
Keccak-512. -/
private def hashExtLengths : Array Nat :=
  #[55, 56, 63, 64, 65, 70, 71, 72, 73, 111, 112, 119, 120, 127, 128, 129, 134, 135, 136, 137, 143,
    144, 145, 255, 256, 257, 271, 272, 273, 1000]

/-- HASHEXT with every algorithm on data of each length of `hashExtLengths`, in entries of at most
127 bytes. -/
private def hashExtLengthCases (suite : String) (append rev : Bool) : Array OracleCase := Id.run do
  let pre : Array Value := if append then #[bl #[]] else #[]
  let mut out : Array OracleCase := #[]
  for len in hashExtLengths do
    let entries : Array Value := (Array.range ((len + 126) / 127)).map fun j =>
      sl (noise (Nat.min 127 (len - 127 * j)) (len + j))
    for id in [0:5] do
      out := out.push
        { name := s!"oracle/len{len}/id{id}", instr := { name := suite },
          program := #[.cryptoOp (.hashExt id append rev)],
          initStack := pre ++ entries ++ #[iv (Int.ofNat entries.size)] }
  return out

private def hashExtVariants (append rev : Bool) : Array (String × Instr) :=
  #[0, 1, 2, 3, 4].map (fun id => (s!"id{id}", Instr.cryptoOp (.hashExt id append rev)))

private def hashExtCases (suite : String) (append rev : Bool) : Array OracleCase :=
  cross suite (hashExtVariants append rev) (hashExtStacks append false) ++
    cross suite #[("id-from-stack", .cryptoOp (.hashExt 255 append rev))] (hashExtStacks append true) ++
    hashExtGasCases suite append rev ++ hashExtLengthCases suite append rev


/-! ### Ed25519 (`CHKSIGNU`, `CHKSIGNS`) -/

private def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

private def hexBytes (h : String) : Array UInt8 := Id.run do
  let cs := h.toList.toArray
  let mut out : Array UInt8 := #[]
  for i in [0:cs.size / 2] do
    out := out.push (UInt8.ofNat (hexVal cs[2 * i]! * 16 + hexVal cs[2 * i + 1]!))
  return out

private def hexInt (h : String) : Int := Int.ofNat ((hexBytes h).foldl (fun acc b => acc * 256 + b.toNat) 0)

private def hexSlice (h : String) : Value := sl (bitsOfBytes (hexBytes h))

/-- CHKSIGNU/CHKSIGNS stacks for every vector of `tools/crypto/ed25519_vectors.py` (ordinary
signatures, corrupted ones, and signatures satisfying the strict equation of OpenSSL for small-order,
non-canonical and mixed-order keys): `hash sig key` / `data sig key`. A 32-byte message is both a
CHKSIGNU hash and a CHKSIGNS data slice. -/
private def chkSignVectorStacks (fromSlice : Bool) : Array (String × Array Value) :=
  CryptoVectors.ed25519.filterMap fun (name, kind, key, sig, msg, _) =>
    let k := iv (hexInt key)
    if fromSlice then some (name, #[hexSlice msg, hexSlice sig, k])
    else if kind == "U" then some (name, #[iv (hexInt msg), hexSlice sig, k])
    else none

/-- Errors in the order C++ checks them: underflow (3 entries), types of key, signature, data;
the data (unaligned slice / hash out of range), then the signature length, then the key range. -/
private def chkSignErrStacks (fromSlice : Bool) : Array (String × Array Value) :=
  let (_, _, key, sig, msg, _) := CryptoVectors.ed25519[0]!
  let k := iv (hexInt key)
  let s := hexSlice sig
  let d : Value := if fromSlice then hexSlice msg else iv (hexInt msg)
  let shortSig := sl (bytes 63 1)
  let badData : Value := if fromSlice then unaligned else iv (-(2 ^ 256))
  #[("empty", #[]), ("two", #[s, k]), ("two-bad", #[.null, .null]),
    ("key-null", #[d, s, .null]), ("key-slice", #[d, s, s]), ("sig-int", #[d, iv 1, k]),
    ("data-null", #[.null, s, k]), ("data-type", #[if fromSlice then iv 1 else s, s, k]),
    ("bad-data", #[badData, s, k]), ("bad-data-short-sig", #[badData, shortSig, k]),
    ("short-sig", #[d, shortSig, k]), ("short-sig-bad-key", #[d, shortSig, iv (-1)]),
    ("key-neg", #[d, s, iv (-1)]), ("key-min", #[d, s, iv (-(2 ^ 256))]), ("key-nan", #[d, s, .int .nan]),
    ("long-sig", #[d, hexSlice (sig ++ "00ff"), k]), ("key-0", #[d, s, iv 0]), ("key-1", #[d, s, iv 1]),
    ("key-2^255", #[d, s, iv (2 ^ 255)])] ++
    (if fromSlice then #[("data-127", #[sl (bytes 127 9), s, k]), ("data-empty", #[sl #[], s, k])]
     else #[("hash-nan", #[.int .nan, s, k]), ("hash-neg", #[iv (-5), s, k])])

private def chkSignInstr (fromSlice : Bool) : Instr :=
  .cryptoOp (if fromSlice then .chkSignS else .chkSignU)

/-- Twelve checks in a row: the first ten are free, then each costs `chksgn_gas_price`
(`VmState::register_chksgn_call`); weak keys count too. -/
private def chkSignCounterCase (suite : String) (fromSlice : Bool) : OracleCase :=
  let stacks := (chkSignVectorStacks fromSlice).extract 0 12
  { name := "oracle/counter12", instr := { name := suite },
    program := (Array.replicate stacks.size #[chkSignInstr fromSlice, .pop 0]).flatten,
    initStack := (stacks.map (·.2)).reverse.flatten }

/-- The free checks are counted as free gas (`consume_free_gas`), which `RUNVM` with isolated gas
(mode 128) charges to the parent before starting the child (`vm.cpp`, `run_child_vm`); without
isolation the counter and the free gas pass to the child and back. -/
private def chkSignFreeGasCases (suite : String) (fromSlice : Bool) : Array OracleCase := Id.run do
  let stacks := (chkSignVectorStacks fromSlice).extract 0 11
  let child : Array Value := #[iv 0, .slice (Slice.ofCell Cell.empty)]
  let mut out : Array OracleCase := #[]
  for k in [1, 10, 11] do
    let st := stacks.extract 0 k
    for mode in [0, 128] do
      out := out.push
        { name := s!"oracle/free-gas/checks{k}/runvm{mode}", instr := { name := suite },
          program := (Array.replicate k #[chkSignInstr fromSlice, .pop 0]).flatten ++ #[.contExt (.runvm mode)],
          initStack := child ++ (st.map (·.2)).reverse.flatten }
  -- a check inside the child: counted in the child, the counter and free gas come back
  for mode in [0, 128] do
    let (_, inner) := stacks[0]!
    let childCode : Cell :=
      match assembleCp0 [chkSignInstr fromSlice] with
      | .ok c => c
      | .error _ => Cell.empty
    out := out.push
      { name := s!"oracle/free-gas/in-child/runvm{mode}", instr := { name := suite },
        program := #[.contExt (.runvm mode), .pop 0, .pop 0, .contExt (.runvm 128)],
        initStack := child ++ inner ++ #[iv 3, .slice (Slice.ofCell childCode)] }
  return out

private def chkSignCases (suite : String) (fromSlice : Bool) : Array OracleCase :=
  ((chkSignVectorStacks fromSlice) ++ (chkSignErrStacks fromSlice)).map (fun (name, st) =>
    { name := s!"oracle/{name}", instr := { name := suite }, program := #[chkSignInstr fromSlice],
      initStack := st }) ++
  #[chkSignCounterCase suite fromSlice] ++ chkSignFreeGasCases suite fromSlice


/-! ### Curve and pairing instructions (`tonops.cpp`, `crypto/ellcurve`, `crypto/vm/bls.cpp`) -/

private def ext (op : CryptoExtInstr) : Instr := .cryptoOp (.ext op)

/-- Cases running `program` on each named stack. -/
private def named (suite : String) (program : Array Instr) (stacks : Array (String × Array Value)) :
    Array OracleCase :=
  stacks.map fun (name, st) =>
    { name := s!"oracle/{name}", instr := { name := suite }, program := program, initStack := st }

/-- The instruction with its gas limit set by `SETGASLIMIT` to `limits` (around its price). -/
private def gasLimitCases (suite : String) (i : Instr) (st : Array Value) (limits : List Nat) :
    Array OracleCase :=
  limits.toArray.map fun lim =>
    { name := s!"oracle/gas/limit{lim}", instr := { name := suite },
      program := #[.pushInt (.num (Int.ofNat lim)), .tonEnvOp .setGasLimit, i], initStack := st }

private def lookupHex (tbl : Array (String × String)) (n : String) : String :=
  match tbl.find? (fun e => e.1 == n) with
  | some e => e.2
  | none => ""

/-- `ECRECOVER`: `hash v r s` → `h x1 x2 -1` or `0`. -/
private def ecrecoverCases (suite : String) : Array OracleCase :=
  let vec := CryptoVectors.ecrecover.map fun (name, h, v, r, s, _) =>
    (name, #[iv (hexInt h), iv (Int.ofNat v), iv (hexInt r), iv (hexInt s)])
  let (_, h, v, r, s, _) := CryptoVectors.ecrecover[0]!
  let (H, V, R, S) := (iv (hexInt h), iv (Int.ofNat v), iv (hexInt r), iv (hexInt s))
  let errs : Array (String × Array Value) :=
    #[("empty", #[]), ("three", #[V, R, S]), ("three-null", #[.null, .null, .null]),
      ("s-null", #[H, V, R, .null]), ("r-slice", #[H, V, sl #[], S]), ("v-null", #[H, .null, R, S]),
      ("hash-null", #[.null, V, R, S]), ("v-256", #[H, iv 256, R, S]), ("v-neg", #[H, iv (-1), R, S]),
      ("v-nan", #[H, .int .nan, R, S]), ("r-neg", #[H, V, iv (-1), S]), ("s-neg", #[H, V, R, iv (-1)]),
      ("hash-neg", #[iv (-1), V, R, S]), ("r-nan", #[H, V, .int .nan, S]), ("hash-nan", #[.int .nan, V, R, S]),
      ("r-neg-s-neg", #[H, V, iv (-1), iv (-1)]), ("s-neg-hash-neg", #[iv (-1), V, R, iv (-1)]),
      ("v-256-r-neg", #[H, iv 256, iv (-1), S]), ("r-2^256-1", #[H, V, iv (2 ^ 256 - 1), S])]
  -- bit 1 of `v`: the abscissa `r + n`, for `r` below `p - n` (2 and 4: on the curve, 3: off it;
  -- `p - n`: refused); `R = ±G` with `s = h`: the key `r⁻¹ (s R − h G)` at infinity for `+G`
  let c := Secp256k1.curve
  let small : Array (String × Array Value) :=
    #[("r2-v2", #[H, iv 2, iv 2, S]), ("r2-v3", #[H, iv 3, iv 2, S]), ("r4-v2", #[H, iv 2, iv 4, S]),
      ("r3-v2", #[H, iv 2, iv 3, S]), ("r-p-n-v2", #[H, iv 2, iv (Int.ofNat (c.p - c.n)), S]),
      ("r-p-n-1-v3", #[H, iv 3, iv (Int.ofNat (c.p - c.n - 1)), S]),
      ("to-infinity", #[iv 5, iv 0, iv (Int.ofNat c.gx), iv 5]),
      ("minus-g", #[iv 5, iv 1, iv (Int.ofNat c.gx), iv 5])]
  named suite #[ext .ecrecover] (vec ++ errs ++ small) ++
    gasLimitCases suite (ext .ecrecover) #[H, V, R, S] [1584, 1585, 1586, 1587]

/-- `SECP256K1_XONLY_PUBKEY_TWEAK_ADD`: `key tweak` → `h x1 x2 -1` or `0`. -/
private def xonlyCases (suite : String) : Array OracleCase :=
  let vec := CryptoVectors.xonlyTweak.map fun (name, k, t, _) => (name, #[iv (hexInt k), iv (hexInt t)])
  let (_, k, t, _) := CryptoVectors.xonlyTweak[0]!
  let (K, T) := (iv (hexInt k), iv (hexInt t))
  let errs : Array (String × Array Value) :=
    #[("empty", #[]), ("one", #[K]), ("one-null", #[.null]), ("tweak-null", #[K, .null]), ("key-null", #[.null, T]),
      ("key-neg", #[iv (-1), T]), ("tweak-neg", #[K, iv (-1)]), ("key-neg-tweak-neg", #[iv (-1), iv (-1)]),
      ("key-nan", #[.int .nan, T]), ("tweak-nan", #[K, .int .nan]), ("key-2^256-1", #[iv (2 ^ 256 - 1), T])]
  named suite #[ext .secp256k1XonlyPubkeyTweakAdd] (vec ++ errs) ++
    gasLimitCases suite (ext .secp256k1XonlyPubkeyTweakAdd) #[K, T] [1334, 1335, 1336, 1337]

/-- P-256 with the key `G` (`03 ‖ G.x`) or `−G` (`02 ‖ G.x`) and `e` the SHA-256 of 32 bytes of data:
`r = −e`, `s = 1` (`e G + r G` at infinity), `r = e`, `s = 1` with `−G` (at infinity) and with `G`
(the sum of equal points), and a valid signature of the private key 1 with the nonce 2. -/
private def p256GeneratorKey (fromSlice : Bool) : Array (String × Array Value) := Id.run do
  let c := P256.curve
  let data : Array UInt8 := Array.ofFn (n := 32) fun i => UInt8.ofNat (i.1 * 7 + 1)
  let e := bytesToNatBE (sha256Digest data) % c.n
  let d : Value := if fromSlice then sl (bitsOfBytes data) else iv (Int.ofNat (bytesToNatBE data))
  let key (form : UInt8) : Value := sl (bitsOfBytes (#[form] ++ natToBytesBEFixed c.gx 32))
  let sig (r s : Nat) : Value := sl (bitsOfBytes (natToBytesBEFixed r 32 ++ natToBytesBEFixed s 32))
  let r2 := match c.toAffine (c.mul 2 c.gen) with | some (x, _) => x % c.n | none => 0
  let s2 := Weierstrass.invMod 2 c.n * (e + r2) % c.n
  return #[("g-to-infinity", #[d, sig ((c.n - e) % c.n) 1, key 3]),
    ("minus-g-to-infinity", #[d, sig e 1, key 2]), ("g-doubling", #[d, sig e 1, key 3]),
    ("g-valid", #[d, sig r2 s2, key 3]), ("minus-g-invalid", #[d, sig r2 s2, key 2])]

/-- `P256_CHKSIGNU` (`hash sig key`) and `P256_CHKSIGNS` (`data sig key`); key and signature are
slices of 33 and 64 bytes. -/
private def p256Cases (suite : String) (fromSlice : Bool) : Array OracleCase :=
  let i := ext (if fromSlice then .p256ChkSignS else .p256ChkSignU)
  let vec := CryptoVectors.p256.filterMap fun (name, kind, key, sig, data, _) =>
    if fromSlice then some (name, #[hexSlice data, hexSlice sig, hexSlice key])
    else if kind == "U" then some (name, #[iv (hexInt data), hexSlice sig, hexSlice key])
    else none
  let (_, _, key, sig, data, _) := CryptoVectors.p256[0]!
  let (D, S, K) := (if fromSlice then hexSlice data else iv (hexInt data), hexSlice sig, hexSlice key)
  let badData : Value := if fromSlice then unaligned else iv (-1)
  let errs : Array (String × Array Value) :=
    #[("empty", #[]), ("two", #[S, K]), ("two-null", #[.null, .null]), ("key-int", #[D, S, iv 1]),
      ("sig-int", #[D, iv 1, K]), ("data-null", #[.null, S, K]), ("bad-data", #[badData, S, K]),
      ("bad-data-short-sig", #[badData, sl (bytes 63 1), K]), ("short-sig", #[D, sl (bytes 63 1), K]),
      ("short-key", #[D, S, sl (bytes 32 1)]), ("short-sig-short-key", #[D, sl (bytes 63 1), sl (bytes 32 1)]),
      ("long-sig-key", #[D, hexSlice (sig ++ "ff"), hexSlice (key ++ "ff")])] ++
    (if fromSlice then #[("data-127", #[sl (bytes 127 9), S, K]), ("data-empty", #[sl #[], S, K])]
     else #[("hash-nan", #[.int .nan, S, K]), ("hash-2^256-1", #[iv (2 ^ 256 - 1), S, K])])
  named suite #[i] (vec ++ errs ++ p256GeneratorKey fromSlice) ++
    gasLimitCases suite i #[D, S, K] [3584, 3585, 3586, 3587]

private def ristValid : Array (String × Int) :=
  (CryptoVectors.ristretto.filter (·.2.2)).map fun (n, e, _) => (n, hexInt e)

private def ristInvalid : Array (String × Int) :=
  (CryptoVectors.ristretto.filter (fun e => !e.2.2)).map fun (n, e, _) => (n, hexInt e)

private def rist255L : Int := 2 ^ 252 + 27742317777372353535851937790883648493

/-- `RIST255_FROMHASH`: `x1 x2` (two 256-bit halves of a 512-bit hash) → the point. -/
private def ristFromHashCases (suite : String) : Array OracleCase :=
  named suite #[ext .rist255FromHash]
    #[("zero", #[iv 0, iv 0]), ("small", #[iv 1, iv 2]), ("max", #[iv (2 ^ 256 - 1), iv (2 ^ 256 - 1)]),
      ("rand", #[iv (hexInt "8ce8cdc1a1fae96e4a6ce3e5e6cc8ce6c0b4d0b0cf2d2f6f8b1a7a0c3e6d1f42"),
                 iv (hexInt "1f3a5c7e9b0d2f4a6c8e0b2d4f6a8c0e2b4d6f8a0c2e4b6d8f0a2c4e6b8d0f2a")]),
      ("empty", #[]), ("one", #[iv 1]), ("x1-neg", #[iv (-1), iv 0]), ("x2-neg", #[iv 0, iv (-1)]),
      ("x1-nan", #[.int .nan, iv 0]), ("x2-null", #[iv 0, .null]), ("x1-null", #[.null, iv 0]),
      ("both-neg", #[iv (-1), iv (-1)])] ++
    gasLimitCases suite (ext .rist255FromHash) #[iv 1, iv 2] [684, 685, 686, 687]

/-- `RIST255_VALIDATE` / `RIST255_QVALIDATE`: `x`. -/
private def ristValidateCases (suite : String) (quiet : Bool) : Array OracleCase :=
  named suite #[ext (if quiet then .rist255Qvalidate else .rist255Validate)]
    ((ristValid ++ ristInvalid).map (fun (n, x) => (n, #[iv x])) ++
      #[("neg", #[iv (-1)]), ("nan", #[.int .nan]), ("null", #[.null]), ("empty", #[]),
        ("2^256-1", #[iv (2 ^ 256 - 1)])])

/-- `RIST255_{Q}ADD` / `RIST255_{Q}SUB`: `x y`. -/
private def ristAddSubCases (suite : String) (op : CryptoExtInstr) : Array OracleCase :=
  let v := ristValid
  let pairs : Array (String × Array Value) :=
    #[(0, 1), (1, 2), (2, 1), (3, 3), (1, 0), (0, 0), (8, 9), (9, 10)].filterMap fun (a, b) =>
      if a < v.size && b < v.size then some (s!"{v[a]!.1}-{v[b]!.1}", #[iv v[a]!.2, iv v[b]!.2]) else none
  let bad : Array (String × Array Value) :=
    ristInvalid.map (fun (n, x) => (s!"x-{n}", #[iv x, iv v[1]!.2])) ++
      ristInvalid.map (fun (n, y) => (s!"y-{n}", #[iv v[1]!.2, iv y])) ++
      #[("empty", #[]), ("one", #[iv v[1]!.2]), ("one-null", #[.null]), ("x-neg", #[iv (-1), iv v[1]!.2]),
        ("y-neg", #[iv v[1]!.2, iv (-1)]), ("x-nan", #[.int .nan, iv v[1]!.2]), ("y-null", #[iv v[1]!.2, .null])]
  named suite #[ext op] (pairs ++ bad)

/-- `RIST255_{Q}MUL`: `x n` (n reduced modulo l; zero cases differ between versions). -/
private def ristMulCases (suite : String) (quiet : Bool) : Array OracleCase :=
  let v := ristValid
  let ns : Array (String × Int) :=
    #[("0", 0), ("1", 1), ("2", 2), ("7", 7), ("l", rist255L), ("l+1", rist255L + 1), ("l-1", rist255L - 1),
      ("-1", -1), ("2^256-1", 2 ^ 256 - 1), ("-2^256", -(2 ^ 256))]
  let good := (#[1, 2, 0, 8].filter (· < v.size)).flatMap fun a =>
    ns.map fun (nn, n) => (s!"{v[a]!.1}-n{nn}", #[iv v[a]!.2, iv n])
  let bad : Array (String × Array Value) :=
    ristInvalid.flatMap (fun (n, x) => #[(s!"{n}-n1", #[iv x, iv 1]), (s!"{n}-n0", #[iv x, iv 0]),
      (s!"{n}-nl", #[iv x, iv rist255L])]) ++
      #[("x-nan-n0", #[.int .nan, iv 0]), ("x-nan-n1", #[.int .nan, iv 1]), ("n-nan", #[iv v[1]!.2, .int .nan]),
        ("x-neg-n1", #[iv (-1), iv 1]), ("x-neg-n0", #[iv (-1), iv 0]), ("empty", #[]), ("one", #[iv 1]),
        ("one-null", #[.null]), ("x-null", #[.null, iv 1]), ("n-null", #[iv v[1]!.2, .null])]
  named suite #[ext (if quiet then .rist255Qmul else .rist255Mul)] (good ++ bad)

/-- `RIST255_{Q}MULBASE`: `n`. -/
private def ristMulBaseCases (suite : String) (quiet : Bool) : Array OracleCase :=
  named suite #[ext (if quiet then .rist255QmulBase else .rist255MulBase)]
    #[("0", #[iv 0]), ("1", #[iv 1]), ("2", #[iv 2]), ("l", #[iv rist255L]), ("l+3", #[iv (rist255L + 3)]),
      ("l-1", #[iv (rist255L - 1)]), ("-1", #[iv (-1)]), ("2^256-1", #[iv (2 ^ 256 - 1)]),
      ("-2^256", #[iv (-(2 ^ 256))]), ("nan", #[.int .nan]), ("null", #[.null]), ("empty", #[])]

/-! #### BLS12-381 -/

/-- Encodings beyond the py_ecc vectors of `CryptoVectors`: on E1 the abscissa 0 (`(0, ±2)`, of
order 3, refused by `POINTonE1_Uncompress_Z`), the infinity flag with the sign flag, and a point of
order 11 (the point of abscissa 5, sign 0, times `h₁·r/11²`); on E2 the imaginary part `p`
(`xTooBig`), the real part `p`, the infinity flag with a nonzero bit or with the sign flag, the
abscissa 0 (off the curve), and points of order 13 and 23 (the point of abscissa `1 + i`, sign 0,
times `h₂·r/13²` and `h₂·r/23²`; the unit tests check the orders). The small orders reach the flags
of blst's windowed multiplication (`ptype##s_mult_w5`). -/
private def blsExtraG1 : Array (String × String) :=
  #[("xZero", "80" ++ String.join (List.replicate 47 "00")), ("infSign", "e0" ++ String.join (List.replicate 47 "00")),
    ("order11", "a00b9529a7b23788075a6c33c7b77b3dcf4da4f58af5310f32e739a6c653a5a8f7cf7f19a297bd6a8f3f19ea82cf9419")]

private def blsExtraG2 : Array (String × String) :=
  let zeros (n : Nat) := String.join (List.replicate n "00")
  let pHex := "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"
  #[("xTooBig", "9a" ++ pHex.drop 2 ++ zeros 48), ("c0TooBig", "80" ++ zeros 47 ++ pHex),
    ("infNonzero", "c0" ++ zeros 94 ++ "01"), ("infSign", "e0" ++ zeros 95), ("xZero", "80" ++ zeros 95),
    ("order13", "832762e5199990da7d4ebc6409c2fdae09b25206fa89dded0a23c05406588284278c22ea15e6d03cee69a68b7d4704a4" ++
      "043ff79d06a80add8340a1a548d700c5ffeef5b14a3e246834d320e323d9fcc76bae16f9f2763ab556905843518bc0c2"),
    ("order23", "a1c8529db7e45f16111c0c95106d37fb89a90afb348c9082db6d49fc34ee0077501c7ac278ed112708313a28768cc52c" ++
      "0503fbc16c24192886d4bb5c5f791e3c3448dc4e19f0ca8d0bcd6cf6cbe9ccd602478cafaf1d7847458df499807d8ae2")]

private def g1v (n : String) : Value := hexSlice (lookupHex (CryptoVectors.blsG1 ++ blsExtraG1) n)
private def g2v (n : String) : Value := hexSlice (lookupHex (CryptoVectors.blsG2 ++ blsExtraG2) n)
private def msgv (n : String) : Value := hexSlice (lookupHex CryptoVectors.blsMsg n)
private def sigv (i j : Nat) : Value :=
  match CryptoVectors.blsSig.find? (fun e => e.1 == s!"s{i}_{j}") with
  | some (_, _, _, h) => hexSlice h
  | none => sl #[]
private def pkv (i : Nat) : Value := g1v s!"pk{i}"
private def blsR : Int := 52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- Encodings refused or outside the subgroup: a point of E1 outside G1, an abscissa off the curve,
no compression flag, the abscissa `p`, the infinity flag with a nonzero bit or with the sign flag, the
abscissa 0 (`(0, ±2)`, refused by `POINTonE1_Uncompress_Z` as not in the group). -/
private def g1Bad : Array String :=
  #["noSubgroup", "offCurve", "noCompressFlag", "xTooBig", "infNonzero", "xZero", "infSign"]
/-- As `g1Bad` for G2: the imaginary part `c1 = p`, the real part `c0 = p`, the abscissa 0 (off the
curve: `4(1 + i)` is not a square). -/
private def g2Bad : Array String :=
  #["noSubgroup", "offCurve", "noCompressFlag", "xTooBig", "c0TooBig", "infNonzero", "infSign", "xZero"]

private def g1GenB : Array UInt8 := hexBytes (lookupHex CryptoVectors.blsG1 "gen")
private def g2GenB : Array UInt8 := hexBytes (lookupHex CryptoVectors.blsG2 "gen")
private def blsBytesV (b : Array UInt8) : Value := sl (bitsOfBytes b)
private def sigBytes (i j : Nat) : Array UInt8 :=
  match CryptoVectors.blsSig.find? (fun e => e.1 == s!"s{i}_{j}") with
  | some (_, _, _, h) => hexBytes h
  | none => #[]
private def sigv0 (j : Nat) : Array UInt8 := sigBytes 0 j
private def sigv1 (j : Nat) : Array UInt8 := sigBytes 1 j

/-- The sum of signatures (`Bls12381.aggregate`, the model's own; C++ judges the cases using it). -/
private def blsAggOf (sigs : Array (Array UInt8)) : Array UInt8 := (Bls12381.aggregate sigs).getD #[]

/-- `−pk0`. -/
private def blsNegPk0 : Value :=
  blsBytesV ((Bls12381.g1Neg (hexBytes (lookupHex CryptoVectors.blsG1 "pk0"))).getD #[])

/-- `k · H(m)`, the signature of `m` by the key `k`. -/
private def blsSign (k : Nat) (m : Array UInt8) : Bls12381.Jac Bls12381.Fp2 :=
  Bls12381.g2Mul (Bls12381.hashToG2 m) k

/-- `n` pairs `pk m` of the keys `2, 3, …` and one-byte messages, and their aggregate signature. -/
private def blsAvSet (n : Nat) : Array Value × Value :=
  let ks := (Array.range n).map fun i => (i + 2, #[UInt8.ofNat (0x40 + i)])
  let st := ks.flatMap fun (k, m) =>
    #[blsBytesV ((Bls12381.g1MulInt g1GenB (Int.ofNat k)).getD #[]), blsBytesV m]
  let sig := ks.foldl (fun acc (k, m) => Bls12381.Jac.add Bls12381.fp2F acc (blsSign k m))
    (Bls12381.Jac.inf Bls12381.fp2F)
  (st, blsBytesV (Bls12381.compressG2 sig))

/-- `2k` pairs whose pairings multiply to 1: `k` times `e(2a, b) e(−a, 2b)`. -/
private def blsPairsOne (k : Nat) : Array Value :=
  (Array.range k).flatMap fun _ => #[g1v "gen2", g2v "gen", g1v "genNeg", g2v "gen2"]

private def blsVerifyCases (suite : String) : Array OracleCase :=
  let valid := (#[(0, 0), (0, 1), (1, 2), (2, 3), (3, 1)] : Array (Nat × Nat)).map fun (i, j) =>
    (s!"pk{i}-m{j}", #[pkv i, msgv s!"m{j}", sigv i j])
  let wrong : Array (String × Array Value) :=
    #[("wrong-msg", #[pkv 0, msgv "m1", sigv 0 2]), ("wrong-pk", #[pkv 1, msgv "m1", sigv 0 1]),
      ("pk-zero", #[g1v "zero", msgv "m1", sigv 0 1]), ("sig-zero", #[pkv 0, msgv "m1", g2v "zero"]),
      ("unaligned-msg", #[pkv 0, unaligned, sigv 0 1]), ("short-sig", #[pkv 0, msgv "m1", sl (bytes 95 1)]),
      ("short-pk", #[sl (bytes 47 1), msgv "m1", sigv 0 1]), ("empty", #[]), ("two", #[msgv "m1", sigv 0 1]),
      ("pk-int", #[iv 1, msgv "m1", sigv 0 1])] ++
    g1Bad.map (fun b => (s!"pk-{b}", #[g1v b, msgv "m1", sigv 0 1])) ++
    g2Bad.map (fun b => (s!"sig-{b}", #[pkv 0, msgv "m1", g2v b]))
  named suite #[ext .blsVerify] (valid ++ wrong) ++
    gasLimitCases suite (ext .blsVerify) #[pkv 0, msgv "m1", sigv 0 1] [61100, 61101, 61102, 61103]

private def blsAggregateCases (suite : String) : Array OracleCase :=
  named suite #[ext .blsAggregate]
    #[("one", #[sigv 0 1, iv 1]), ("two", #[sigv 0 1, sigv 1 1, iv 2]), ("three", #[sigv 0 1, sigv 1 1, sigv 2 1, iv 3]),
      ("zero-sig", #[sigv 0 1, g2v "zero", iv 2]), ("n0", #[sigv 0 1, iv 0]), ("n-too-big", #[sigv 0 1, iv 2]),
      ("n-neg", #[iv (-1)]), ("empty", #[]), ("n-only", #[iv 1]), ("short", #[sl (bytes 95 1), iv 1]),
      ("not-slice", #[iv 5, iv 1]),
      -- `bls::aggregate` checks the subgroup of every signature but the first (`P2::aggregate`)
      ("nosub-first", #[g2v "noSubgroup", sigv 0 1, iv 2]), ("nosub-only", #[g2v "noSubgroup", iv 1]),
      ("order13-first", #[g2v "order13", sigv 0 1, iv 2]), ("zero-first", #[g2v "zero", sigv 0 1, iv 2]),
      ("zero-only", #[g2v "zero", iv 1]), ("zero-zero", #[g2v "zero", g2v "zero", iv 2]),
      ("same-twice", #[sigv 0 1, sigv 0 1, iv 2])] ++
    named suite #[ext .blsAggregate] (g2Bad.map (fun b => (s!"bad-{b}", #[sigv 0 1, g2v b, iv 2])))

private def blsFastAggVerifyCases (suite : String) : Array OracleCase :=
  let agg := g2v "agg012_m1"
  named suite #[ext .blsFastAggregateVerify]
    (#[("valid3", #[pkv 0, pkv 1, pkv 2, iv 3, msgv "m1", agg]), ("one", #[pkv 0, iv 1, msgv "m1", sigv 0 1]),
      ("wrong-msg", #[pkv 0, pkv 1, pkv 2, iv 3, msgv "m2", agg]), ("missing-pk", #[pkv 0, pkv 1, iv 2, msgv "m1", agg]),
      ("n0", #[iv 0, msgv "m1", agg]), ("pk-zero", #[g1v "zero", iv 1, msgv "m1", g2v "zero"]),
      ("n-too-big", #[pkv 0, iv 2, msgv "m1", agg]), ("empty", #[]), ("two", #[msgv "m1", agg]),
      ("unaligned-msg", #[pkv 0, iv 1, unaligned, sigv 0 1]), ("short-sig", #[pkv 0, iv 1, msgv "m1", sl (bytes 95 1)])] ++
     g1Bad.map (fun b => (s!"pk-{b}", #[g1v b, iv 1, msgv "m1", sigv 0 1])) ++
     g2Bad.map (fun b => (s!"sig-{b}", #[pkv 0, iv 1, msgv "m1", g2v b])) ++
     -- keys summing to infinity (refused by core_verify), the same key twice, a key off the subgroup
     -- first (not checked by P1::aggregate, then by core_verify) and later
     #[("keys-cancel", #[pkv 0, blsNegPk0, iv 2, msgv "m1", g2v "zero"]),
       ("keys-cancel-sig", #[pkv 0, blsNegPk0, iv 2, msgv "m1", sigv 0 1]),
       ("same-key-twice", #[pkv 0, pkv 0, iv 2, msgv "m1", blsBytesV (blsAggOf #[sigv0 1, sigv0 1])]),
       ("pk-nosub-first", #[g1v "noSubgroup", pkv 0, iv 2, msgv "m1", sigv 0 1]),
       ("pk-nosub-second", #[pkv 0, g1v "noSubgroup", iv 2, msgv "m1", sigv 0 1]),
       ("pk-zero-second", #[pkv 0, g1v "zero", iv 2, msgv "m1", sigv 0 1])])

private def blsAggVerifyCases (suite : String) : Array OracleCase :=
  let agg := g2v "agg_distinct"
  named suite #[ext .blsAggregateVerify]
    (#[("valid3", #[pkv 0, msgv "m0", pkv 1, msgv "m1", pkv 2, msgv "m2", iv 3, agg]),
      ("one", #[pkv 0, msgv "m1", iv 1, sigv 0 1]),
      ("swapped", #[pkv 1, msgv "m0", pkv 0, msgv "m1", pkv 2, msgv "m2", iv 3, agg]),
      ("n0", #[iv 0, agg]), ("n-too-big", #[pkv 0, msgv "m1", iv 2, agg]), ("empty", #[]), ("one-entry", #[agg]),
      ("unaligned-msg", #[pkv 0, unaligned, iv 1, sigv 0 1]), ("pk-zero", #[g1v "zero", msgv "m1", iv 1, sigv 0 1])] ++
     g1Bad.map (fun b => (s!"pk-{b}", #[g1v b, msgv "m1", iv 1, sigv 0 1])) ++
     g2Bad.map (fun b => (s!"sig-{b}", #[pkv 0, msgv "m1", iv 1, g2v b])) ++
     -- repeated messages (blst's Pairing does not refuse them), a signature at infinity (in G2, its
     -- Miller loop 1), and 8, 9, 16 pairs: the batches of eight of blst's pairing context
     #[("dup-msg", #[pkv 0, msgv "m1", pkv 1, msgv "m1", iv 2, blsBytesV (blsAggOf #[sigv0 1, sigv1 1])]),
       ("sig-zero", #[pkv 0, msgv "m1", iv 1, g2v "zero"]),
       ("sig-order13", #[pkv 0, msgv "m1", iv 1, g2v "order13"])] ++
     (#[8, 9, 16] : Array Nat).flatMap fun n =>
       let (st, sig) := blsAvSet n
       #[(s!"n{n}", st ++ #[iv (Int.ofNat n), sig]), (s!"n{n}-wrong-sig", st ++ #[iv (Int.ofNat n), sigv 0 1])])

/-- Group operations on G1 (`g2 = false`) or G2. -/
private def blsGroupCases (suite : String) (g2 : Bool) : Array OracleCase :=
  let pt : String → Value := if g2 then g2v else g1v
  let bad := if g2 then g2Bad else g1Bad
  let size : Nat := if g2 then 96 else 48
  let pts : Array String := #["gen", "gen2", "gen7", "zero"]
  let opAdd : CryptoExtInstr := if g2 then .blsG2Add else .blsG1Add
  let opSub : CryptoExtInstr := if g2 then .blsG2Sub else .blsG1Sub
  let opNeg : CryptoExtInstr := if g2 then .blsG2Neg else .blsG1Neg
  let opMul : CryptoExtInstr := if g2 then .blsG2Mul else .blsG1Mul
  let opMulti : CryptoExtInstr := if g2 then .blsG2MultiExp else .blsG1MultiExp
  let opZero : CryptoExtInstr := if g2 then .blsG2Zero else .blsG1Zero
  let opIn : CryptoExtInstr := if g2 then .blsG2InGroup else .blsG1InGroup
  let opIs : CryptoExtInstr := if g2 then .blsG2IsZero else .blsG1IsZero
  let smallPts : Array String := if g2 then #["noSubgroup", "order13", "order23"] else #["noSubgroup", "order11"]
  let suffix := suite.drop 7  -- after "BLS_G1_" / "BLS_G2_"
  let common : Array (String × Array Value) :=
    #[("empty", #[]), ("int", #[iv 1]), ("short", #[sl (bytes (size - 1) 1)]), ("null", #[.null])]
  match suffix with
  | "ADD" | "SUB" =>
      named suite #[ext (if suffix == "ADD" then opAdd else opSub)]
        ((pts.flatMap fun a => pts.map fun b => (s!"{a}-{b}", #[pt a, pt b])) ++
          bad.map (fun b => (s!"bad-{b}", #[pt "gen", pt b])) ++ bad.map (fun b => (s!"{b}-bad", #[pt b, pt "gen"])) ++
          #[("one", #[pt "gen"]), ("empty", #[]), ("int", #[pt "gen", iv 1]), ("short", #[pt "gen", sl (bytes (size - 1) 1)])])
  | "NEG" =>
      named suite #[ext opNeg] (pts.map (fun a => (a, #[pt a])) ++ bad.map (fun b => (s!"bad-{b}", #[pt b])) ++ common)
  | "MUL" =>
      named suite #[ext opMul]
        ((#["gen", "gen7", "zero"].flatMap fun a =>
            (#[("0", 0), ("1", 1), ("2", 2), ("r", blsR), ("r+1", blsR + 1), ("-1", -1), ("2^256-1", 2 ^ 256 - 1),
               ("-2^256", -(2 ^ 256))] : Array (String × Int)).map fun (xn, x) => (s!"{a}-x{xn}", #[pt a, iv x])) ++
          bad.flatMap (fun b => #[(s!"bad-{b}-x0", #[pt b, iv 0]), (s!"bad-{b}-x1", #[pt b, iv 1])]) ++
          -- off the subgroup: GLV (E1) and GLS (E2) give `rem·P − q·σ²(P)` / the ψ digits, not `x·P`;
          -- the small orders reach the flags of the windowed multiplication
          (smallPts.flatMap fun a =>
            (#[("2^200+7", 2 ^ 200 + 7), ("r-1", blsR - 1), ("-5", -5), ("2^128+3", 2 ^ 128 + 3),
               ("rand", 0x5c3f1d2e8a7b6c5d4e3f2a1b0c9d8e7f6a5b4c3d2e1f0a9b8c7d6e5f4a3b2c1d)] : Array (String × Int)).map
              fun (xn, x) => (s!"{a}-x{xn}", #[pt a, iv x])) ++
          #[("x-nan", #[pt "gen", .int .nan]), ("x-null", #[pt "gen", .null]), ("one", #[iv 1]), ("empty", #[]),
            ("p-int", #[iv 1, iv 1])])
  | "MULTIEXP" =>
      named suite #[ext opMulti]
        (#[("n0", #[iv 0]), ("n1", #[pt "gen", iv 5, iv 1]), ("n2", #[pt "gen", iv 3, pt "gen2", iv 4, iv 2]),
          ("n3", #[pt "gen", iv 3, pt "gen7", iv (-1), pt "zero", iv 9, iv 3]),
          ("n4", #[pt "gen", iv blsR, pt "gen2", iv 0, pt "gen7", iv 1, pt "gen", iv (2 ^ 256 - 1), iv 4]),
          ("n1-bad", #[pt bad[0]!, iv 5, iv 1]), ("n2-bad", #[pt "gen", iv 1, pt bad[1]!, iv 2, iv 2]),
          ("n1-bad-x0", #[pt bad[1]!, iv 0, iv 1]), ("n2-nan", #[pt "gen", .int .nan, pt "gen2", iv 1, iv 2]),
          ("n-too-big", #[pt "gen", iv 1, iv 2]), ("n-neg", #[iv (-1)]), ("empty", #[]),
          ("n2-int-point", #[iv 1, iv 1, pt "gen", iv 1, iv 2]),
          -- below 32 points, a point at infinity makes blst drop every Booth digit of magnitude
          -- above 1 (the batch inversion of the tables, `multiExp`): 3 = digit 3, 17 = digits 1 1
          ("n2-zero-x3", #[pt "gen", iv 3, pt "zero", iv 5, iv 2]),
          ("n2-zero-x1", #[pt "gen", iv 1, pt "zero", iv 5, iv 2]),
          ("n2-zero-x17", #[pt "gen", iv 17, pt "zero", iv 0, iv 2]),
          ("n2-zero-x-1", #[pt "gen", iv (-1), pt "zero", iv 1, iv 2]),
          ("n2-zero-first", #[pt "zero", iv 2, pt "gen7", iv 0x1111, iv 2]),
          ("n2-nosub", #[pt "noSubgroup", iv 123456789, pt "gen", iv 7, iv 2]),
          ("n3-small", #[pt smallPts[1]!, iv (2 ^ 100 + 3), pt "gen", iv 7, pt "gen2", iv 9, iv 3]),
          ("n1-nosub-big", #[pt "noSubgroup", iv (2 ^ 200 + 12345), iv 1]),
          ("n1-small", #[pt smallPts[1]!, iv (2 ^ 100 + 3), iv 1])] ++
        -- one point at infinity among 31 (tables) and 32 (buckets) points
        ((#[31, 32] : Array Nat).map fun k =>
          (s!"n{k}-zero", ((Array.range k).flatMap fun i =>
            #[pt (if i = 3 then "zero" else (#["gen", "gen2", "gen7"] : Array String)[i % 3]!),
              iv (Int.ofNat (i * 7919 + 3))]) ++ #[iv (Int.ofNat k)])) ++
        -- the gas divisor l of bls_calculate_multiexp_gas (tonops.cpp:1165) starts at 4 and grows
        -- from n = 32 (2^(l+1) <= n): around 32 and 64 points
        ((#[31, 32, 33, 63, 64, 65] : Array Nat).map fun k =>
          (s!"n{k}", ((Array.range k).flatMap fun i =>
            #[pt ((#["gen", "gen2", "gen7"] : Array String)[i % 3]!), iv (Int.ofNat i + 1)]) ++ #[iv (Int.ofNat k)])))
  | "ZERO" => named suite #[ext opZero] #[("empty", #[]), ("on-stack", #[iv 1, iv 2])]
  | "INGROUP" =>
      named suite #[ext opIn] (pts.map (fun a => (a, #[pt a])) ++ bad.map (fun b => (s!"bad-{b}", #[pt b])) ++ common)
  | "ISZERO" =>
      named suite #[ext opIs] (pts.map (fun a => (a, #[pt a])) ++ bad.map (fun b => (s!"bad-{b}", #[pt b])) ++ common)
  | _ => #[]

private def blsMapCases (suite : String) (g2 : Bool) : Array OracleCase :=
  let fps : Array (String × String) := if g2 then CryptoVectors.blsFp2 else CryptoVectors.blsFp
  let size : Nat := if g2 then 96 else 48
  named suite #[ext (if g2 then .blsMapToG2 else .blsMapToG1)]
    (fps.map (fun (n, h) => (n, #[hexSlice h])) ++
      #[("short", #[sl (bytes (size - 1) 1)]), ("long", #[sl (bytes (size + 1) 1)]), ("int", #[iv 1]), ("empty", #[])])

private def blsPairingCases (suite : String) : Array OracleCase :=
  named suite #[ext .blsPairing]
    #[("n0", #[iv 0]), ("n1-gen", #[g1v "gen", g2v "gen", iv 1]), ("n1-zero", #[g1v "zero", g2v "gen", iv 1]),
      ("e(2a,b)e(a,-2b)", #[g1v "gen2", g2v "gen", g1v "gen", g2v "gen2", iv 2]),
      ("e(7a,b)e(a,7b)", #[g1v "gen7", g2v "gen", g1v "gen", g2v "gen7", iv 2]),
      ("e(2a,b)e(-a,2b)", #[g1v "gen2", g2v "gen", g1v "genNeg", g2v "gen2", iv 2]),
      ("bad-g1", #[g1v "offCurve", g2v "gen", iv 1]), ("bad-g2", #[g1v "gen", g2v "offCurve", iv 1]),
      ("nosub-g1", #[g1v "noSubgroup", g2v "gen", iv 1]), ("nosub-g2", #[g1v "gen", g2v "noSubgroup", iv 1]),
      ("n-too-big", #[g1v "gen", g2v "gen", iv 2]), ("empty", #[]), ("n-neg", #[iv (-1)]),
      ("swapped", #[g2v "gen", g1v "gen", iv 1]),
      -- points at infinity (blst_pairing_raw_aggregate, miller_loop_n): a pair of two is skipped
      -- (alone: no Miller loop, false); one alone in its batch counts as 1; a G2 point at infinity
      -- among other pairs makes the batch 0 (false), a G1 point at infinity leaves it as is
      ("n1-g2-zero", #[g1v "gen", g2v "zero", iv 1]), ("n1-zeros", #[g1v "zero", g2v "zero", iv 1]),
      ("zeros-and-one", #[g1v "zero", g2v "zero", g1v "gen2", g2v "gen", g1v "genNeg", g2v "gen2", iv 3]),
      ("g2-zero-among-3", #[g1v "gen2", g2v "gen", g1v "genNeg", g2v "gen2", g1v "gen", g2v "zero", iv 3]),
      ("g1-zero-among-3", #[g1v "gen2", g2v "gen", g1v "genNeg", g2v "gen2", g1v "zero", g2v "gen", iv 3]),
      ("n9-g2-zero-last", blsPairsOne 4 ++ #[g1v "gen", g2v "zero", iv 9]),
      ("n9-g2-zero-first", #[g1v "gen", g2v "zero"] ++ blsPairsOne 4 ++ #[iv 9]),
      ("n10-g2-zero-ninth", blsPairsOne 4 ++ #[g1v "gen", g2v "zero", g1v "gen", g2v "gen", iv 10]),
      ("n16-one", blsPairsOne 8 ++ #[iv 16]), ("n17-g1-zero-last", blsPairsOne 8 ++ #[g1v "zero", g2v "gen", iv 17]),
      ("n2-order11-order13", #[g1v "order11", g2v "order13", g1v "gen", g2v "gen", iv 2]),
      ("n1-order11-gen", #[g1v "order11", g2v "gen", iv 1]), ("n1-gen-order13", #[g1v "gen", g2v "order13", iv 1])]


/-! ### Gas running out at the fixed price

C++ charges the fixed price of these instructions with `consume_gas` before (or while) parsing the
operands (tonops.cpp), so with a limit one short of the price there is only out of gas, even for
operands that would fail afterwards. `PUSHINT lim; SETGASLIMIT; i` with the limit one short, exact
and one above, and operands that fail after the charge. -/

private def chargeLimitCases (suite tag : String) (i : Instr) (st : Array Value) (price : Nat) :
    Array OracleCase := Id.run do
  -- the gas before the price: the three instructions as charged by the decoder (`instrGas` of the
  -- decoded bits; the charged length of PUSHINT depends on lim and is not its full length)
  let progGas (lim : Nat) : Nat := Id.run do
    match assembleCp0 [.pushInt (.num (Int.ofNat lim)), .tonEnvOp .setGasLimit, i] with
    | .error _ => return 0
    | .ok c =>
        let mut code := Slice.ofCell c
        let mut gas : Int := 0
        for _ in [0:3] do
          match decodeCp0WithBits code with
          | .ok (instr, bits, rest) =>
              gas := gas + instrGas instr bits
              code := rest
          | .error _ => pure ()
        return gas.toNat
  let mut lim : Nat := price + 100
  for _ in [0:4] do
    lim := progGas lim + price
  let mut out : Array OracleCase := #[]
  for l in [lim - 1, lim, lim + 1] do
    out := out.push
      { name := s!"oracle/gas-at-price/{tag}/limit{l}", instr := { name := suite },
        program := #[.pushInt (.num (Int.ofNat l)), .tonEnvOp .setGasLimit, i], initStack := st }
  return out

private def ristVal (k : Nat) : Value := iv (ristValid[k]!.2)

/-- `(tag, operands failing after the charge, price)` per suite. -/
private def chargeLimitInputs (suite : String) : Array (String × Array Value × Nat) :=
  match suite with
  | "RIST255_FROMHASH" => #[("x1-neg", #[iv (-1), iv 0], 600), ("ok", #[iv 1, iv 2], 600)]
  | "RIST255_VALIDATE" => #[("neg", #[iv (-1)], 200), ("invalid", #[iv ristInvalid[0]!.2], 200)]
  | "RIST255_ADD" | "RIST255_SUB" => #[("invalid", #[iv ristInvalid[0]!.2, ristVal 1], 600)]
  | "RIST255_MUL" => #[("invalid", #[iv ristInvalid[0]!.2, iv 3], 2000)]
  | "RIST255_MULBASE" => #[("n0", #[iv 0], 750)]
  | "BLS_VERIFY" => #[("short-sig", #[pkv 0, msgv "m1", sl (bytes 95 1)], 61000)]
  | "BLS_AGGREGATE" => #[("bad-sig", #[sigv 0 1, g2v "offCurve", iv 2], 6050)]
  | "BLS_FASTAGGREGATEVERIFY" => #[("unaligned-msg", #[pkv 0, iv 1, unaligned, sigv 0 1], 61000)]
  | "BLS_AGGREGATEVERIFY" => #[("unaligned-msg", #[pkv 0, unaligned, iv 1, sigv 0 1], 61000)]
  | "BLS_G1_ADD" | "BLS_G1_SUB" => #[("bad", #[g1v "gen", g1v "offCurve"], 3900)]
  | "BLS_G2_ADD" | "BLS_G2_SUB" => #[("bad", #[g2v "gen", g2v "offCurve"], 6100)]
  | "BLS_G1_NEG" => #[("short", #[sl (bytes 47 1)], 750)]
  | "BLS_G2_NEG" => #[("short", #[sl (bytes 95 1)], 1550)]
  | "BLS_G1_MUL" => #[("bad", #[g1v "offCurve", iv 1], 5200)]
  | "BLS_G2_MUL" => #[("bad", #[g2v "offCurve", iv 1], 10550)]
  | "BLS_G1_MULTIEXP" => #[("bad", #[g1v "gen", iv 1, g1v "offCurve", iv 2, iv 2], 17045)]
  | "BLS_G2_MULTIEXP" => #[("bad", #[g2v "gen", iv 1, g2v "offCurve", iv 2, iv 2], 44368)]
  | "BLS_MAP_TO_G1" => #[("short", #[sl (bytes 47 1)], 2350)]
  | "BLS_MAP_TO_G2" => #[("short", #[sl (bytes 95 1)], 7950)]
  | "BLS_G1_INGROUP" => #[("short", #[sl (bytes 47 1)], 2950)]
  | "BLS_G2_INGROUP" => #[("short", #[sl (bytes 95 1)], 4250)]
  | "BLS_PAIRING" => #[("bad", #[g1v "offCurve", g2v "gen", iv 1], 31800)]
  | _ => #[]

private def chargeLimitInstr (suite : String) : Option Instr :=
  match suite with
  | "RIST255_FROMHASH" => some (ext .rist255FromHash)
  | "RIST255_VALIDATE" => some (ext .rist255Validate)
  | "RIST255_ADD" => some (ext .rist255Add)
  | "RIST255_SUB" => some (ext .rist255Sub)
  | "RIST255_MUL" => some (ext .rist255Mul)
  | "RIST255_MULBASE" => some (ext .rist255MulBase)
  | "BLS_VERIFY" => some (ext .blsVerify)
  | "BLS_AGGREGATE" => some (ext .blsAggregate)
  | "BLS_FASTAGGREGATEVERIFY" => some (ext .blsFastAggregateVerify)
  | "BLS_AGGREGATEVERIFY" => some (ext .blsAggregateVerify)
  | "BLS_G1_ADD" => some (ext .blsG1Add)
  | "BLS_G1_SUB" => some (ext .blsG1Sub)
  | "BLS_G2_ADD" => some (ext .blsG2Add)
  | "BLS_G2_SUB" => some (ext .blsG2Sub)
  | "BLS_G1_NEG" => some (ext .blsG1Neg)
  | "BLS_G2_NEG" => some (ext .blsG2Neg)
  | "BLS_G1_MUL" => some (ext .blsG1Mul)
  | "BLS_G2_MUL" => some (ext .blsG2Mul)
  | "BLS_G1_MULTIEXP" => some (ext .blsG1MultiExp)
  | "BLS_G2_MULTIEXP" => some (ext .blsG2MultiExp)
  | "BLS_MAP_TO_G1" => some (ext .blsMapToG1)
  | "BLS_MAP_TO_G2" => some (ext .blsMapToG2)
  | "BLS_G1_INGROUP" => some (ext .blsG1InGroup)
  | "BLS_G2_INGROUP" => some (ext .blsG2InGroup)
  | "BLS_PAIRING" => some (ext .blsPairing)
  | _ => none

private def chargeLimitCasesFor (suite : String) : Array OracleCase :=
  match chargeLimitInstr suite with
  | none => #[]
  | some i => (chargeLimitInputs suite).flatMap fun (tag, st, price) => chargeLimitCases suite tag i st price

/-! ### Unit checks against the independent references

The oracle cases compare the model with C++; these unit checks pin the results themselves to the
Python references of `tools/crypto` (global version 13), so that, e.g., a valid signature is known
to verify on both sides and not merely to be rejected by both. -/

/-- The model running `prog` on `stack`. -/
private def runModel (prog : Array Instr) (stack : Array Value) : Except Excno (Array Value) := Id.run do
  let mut st : VmState := { (VmState.initial Cell.empty) with stack := stack }
  for i in prog do
    let (res, st') := (execInstr i).run st
    match res with
    | .ok _ => st := st'
    | .error e => return .error e
  return .ok st.stack

private def expectRun (label : String) (prog : Array Instr) (stack : Array Value)
    (expected : Except Excno (Array Value)) : IO Unit := do
  let got := runModel prog stack
  let ok : Bool :=
    match got, expected with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false
  if !ok then
    throw (IO.userError s!"{label}: got {reprStr got}, expected {reprStr expected}")

/-- `h x1 x2 -1` for an uncompressed key `04 x y`, `0` for "". -/
private def keyResult (k : String) : Array Value :=
  if k.isEmpty then #[iv 0]
  else #[iv 4, iv (hexInt ((k.drop 2).take 64)), iv (hexInt (k.drop 66)), iv (-1)]

private def ristEnc (n : String) : Value :=
  match CryptoVectors.ristretto.find? (fun e => e.1 == n) with
  | some (_, e, _) => iv (hexInt e)
  | none => .null

/-- Unit cases of the suite named `suite`. -/
def unitFor (suite : String) : Array UnitCase :=
  let one (name : String) (run : IO Unit) : Array UnitCase := #[{ name := s!"unit/{name}", run := run }]
  match suite with
  | "CHKSIGNU" | "CHKSIGNS" => one "vectors" do
      let fromSlice := suite == "CHKSIGNS"
      for (name, kind, key, sig, msg, valid) in CryptoVectors.ed25519 do
        if fromSlice || kind == "U" then
          let d : Value := if fromSlice then hexSlice msg else iv (hexInt msg)
          expectRun name #[chkSignInstr fromSlice] #[d, hexSlice sig, iv (hexInt key)]
            (.ok #[iv (if valid then -1 else 0)])
  | "ECRECOVER" => one "vectors" do
      for (name, h, v, r, s, key) in CryptoVectors.ecrecover do
        expectRun name #[ext .ecrecover] #[iv (hexInt h), iv (Int.ofNat v), iv (hexInt r), iv (hexInt s)]
          (.ok (keyResult key))
  | "SECP256K1_XONLY_PUBKEY_TWEAK_ADD" => one "vectors" do
      for (name, k, t, key) in CryptoVectors.xonlyTweak do
        expectRun name #[ext .secp256k1XonlyPubkeyTweakAdd] #[iv (hexInt k), iv (hexInt t)] (.ok (keyResult key))
  | "P256_CHKSIGNU" | "P256_CHKSIGNS" => one "vectors" do
      let fromSlice := suite == "P256_CHKSIGNS"
      for (name, kind, key, sig, data, valid) in CryptoVectors.p256 do
        if fromSlice || kind == "U" then
          let d : Value := if fromSlice then hexSlice data else iv (hexInt data)
          expectRun name #[ext (if fromSlice then .p256ChkSignS else .p256ChkSignU)] #[d, hexSlice sig, hexSlice key]
            (.ok #[iv (if valid then -1 else 0)])
  | "RIST255_VALIDATE" => one "vectors" do
      for (name, e, valid) in CryptoVectors.ristretto do
        expectRun name #[ext .rist255Validate] #[iv (hexInt e)] (if valid then .ok #[] else .error .rangeChk)
  | "RIST255_ADD" => one "group-law" do
      expectRun "B+2B" #[ext .rist255Add] #[ristEnc "mul1", ristEnc "mul2"] (.ok #[ristEnc "mul3"])
      expectRun "7B+8B" #[ext .rist255Add] #[ristEnc "mul7", ristEnc "mul8"] (.ok #[ristEnc "mul15"])
      expectRun "0+B" #[ext .rist255Add] #[ristEnc "mul0", ristEnc "mul1"] (.ok #[ristEnc "mul1"])
  | "RIST255_SUB" => one "group-law" do
      expectRun "3B-B" #[ext .rist255Sub] #[ristEnc "mul3", ristEnc "mul1"] (.ok #[ristEnc "mul2"])
      expectRun "B-B" #[ext .rist255Sub] #[ristEnc "mul1", ristEnc "mul1"] (.ok #[ristEnc "mul0"])
  | "RIST255_MUL" => one "group-law" do
      expectRun "B*7" #[ext .rist255Mul] #[ristEnc "mul1", iv 7] (.ok #[ristEnc "mul7"])
      expectRun "2B*4" #[ext .rist255Mul] #[ristEnc "mul2", iv 4] (.ok #[ristEnc "mul8"])
      expectRun "B*(l+3)" #[ext .rist255Mul] #[ristEnc "mul1", iv (rist255L + 3)] (.ok #[ristEnc "mul3"])
  | "RIST255_MULBASE" => one "group-law" do
      for k in [1, 2, 3, 4, 7, 8, 15] do
        expectRun s!"{k}B" #[ext .rist255MulBase] #[iv k] (.ok #[ristEnc s!"mul{k}"])
  | "BLS_VERIFY" => one "vectors" do
      for (name, pk, m, sig) in CryptoVectors.blsSig do
        expectRun name #[ext .blsVerify] #[g1v pk, msgv m, hexSlice sig] (.ok #[iv (-1)])
      expectRun "wrong-pk" #[ext .blsVerify] #[pkv 1, msgv "m1", sigv 0 1] (.ok #[iv 0])
      expectRun "wrong-msg" #[ext .blsVerify] #[pkv 0, msgv "m2", sigv 0 1] (.ok #[iv 0])
  | "BLS_AGGREGATE" => one "vectors" do
      expectRun "agg012" #[ext .blsAggregate] #[sigv 0 1, sigv 1 1, sigv 2 1, iv 3] (.ok #[g2v "agg012_m1"])
  | "BLS_FASTAGGREGATEVERIFY" => one "vectors" do
      expectRun "valid3" #[ext .blsFastAggregateVerify] #[pkv 0, pkv 1, pkv 2, iv 3, msgv "m1", g2v "agg012_m1"]
        (.ok #[iv (-1)])
  | "BLS_AGGREGATEVERIFY" => one "vectors" do
      expectRun "valid3" #[ext .blsAggregateVerify]
        #[pkv 0, msgv "m0", pkv 1, msgv "m1", pkv 2, msgv "m2", iv 3, g2v "agg_distinct"] (.ok #[iv (-1)])
  | "BLS_G1_ADD" => one "group-law" do
      expectRun "G+G" #[ext .blsG1Add] #[g1v "gen", g1v "gen"] (.ok #[g1v "gen2"])
      expectRun "G+0" #[ext .blsG1Add] #[g1v "gen", g1v "zero"] (.ok #[g1v "gen"])
  | "BLS_G1_NEG" => one "group-law" do
      expectRun "-G" #[ext .blsG1Neg] #[g1v "gen"] (.ok #[g1v "genNeg"])
  | "BLS_G1_MUL" => one "group-law" do
      expectRun "G*7" #[ext .blsG1Mul] #[g1v "gen", iv 7] (.ok #[g1v "gen7"])
      expectRun "G*(r+2)" #[ext .blsG1Mul] #[g1v "gen", iv (blsR + 2)] (.ok #[g1v "gen2"])
      -- the order of the small-order vector (below 2^128 the scalar is the GLV remainder alone)
      expectRun "order11*11" #[ext .blsG1Mul] #[g1v "order11", iv 11] (.ok #[g1v "zero"])
      expectRun "order11*12" #[ext .blsG1Mul] #[g1v "order11", iv 12] (.ok #[g1v "order11"])
  | "BLS_G2_ADD" => one "group-law" do
      expectRun "G+G" #[ext .blsG2Add] #[g2v "gen", g2v "gen"] (.ok #[g2v "gen2"])
  | "BLS_G2_NEG" => one "group-law" do
      expectRun "-G" #[ext .blsG2Neg] #[g2v "gen"] (.ok #[g2v "genNeg"])
  | "BLS_G2_MUL" => one "group-law" do
      expectRun "G*7" #[ext .blsG2Mul] #[g2v "gen", iv 7] (.ok #[g2v "gen7"])
      expectRun "G*(r+2)" #[ext .blsG2Mul] #[g2v "gen", iv (blsR + 2)] (.ok #[g2v "gen2"])
      expectRun "G*(-1)" #[ext .blsG2Mul] #[g2v "gen", iv (-1)] (.ok #[g2v "genNeg"])
      -- the orders of the small-order vectors (below 2^64 the scalar is the first GLS digit alone)
      expectRun "order13*13" #[ext .blsG2Mul] #[g2v "order13", iv 13] (.ok #[g2v "zero"])
      expectRun "order13*14" #[ext .blsG2Mul] #[g2v "order13", iv 14] (.ok #[g2v "order13"])
      expectRun "order23*23" #[ext .blsG2Mul] #[g2v "order23", iv 23] (.ok #[g2v "zero"])
  | "BLS_G1_MULTIEXP" => one "infinity-among-points" do
      -- blst (below 32 points): the tables `2P … 8P` of every point are lost to the point at
      -- infinity, a scalar counts by its Booth digits ±1 only: 3 (digit 3) gives the zero point
      expectRun "G*3+0*5" #[ext .blsG1MultiExp] #[g1v "gen", iv 3, g1v "zero", iv 5, iv 2] (.ok #[g1v "zero"])
      expectRun "G*2+G*5" #[ext .blsG1MultiExp] #[g1v "gen", iv 2, g1v "gen", iv 5, iv 2] (.ok #[g1v "gen7"])
  | "BLS_PAIRING" => one "bilinearity" do
      expectRun "e(2a,b)e(-a,2b)" #[ext .blsPairing] #[g1v "gen2", g2v "gen", g1v "genNeg", g2v "gen2", iv 2]
        (.ok #[iv (-1)])
      expectRun "e(a,b)" #[ext .blsPairing] #[g1v "gen", g2v "gen", iv 1] (.ok #[iv 0])
      -- blst's rules for points at infinity (miller_loop_n, raw_aggregate)
      expectRun "e(a,0)" #[ext .blsPairing] #[g1v "gen", g2v "zero", iv 1] (.ok #[iv (-1)])
      expectRun "e(0,0)" #[ext .blsPairing] #[g1v "zero", g2v "zero", iv 1] (.ok #[iv 0])
      expectRun "e(2a,b)e(-a,2b)e(a,0)" #[ext .blsPairing]
        #[g1v "gen2", g2v "gen", g1v "genNeg", g2v "gen2", g1v "gen", g2v "zero", iv 3] (.ok #[iv 0])
      -- the constants of the Frobenius maps and of σ, ψ against their definitions
      let xi := Bls12381.Fp2.xi
      for n in [1, 2, 3] do
        let pn := Bls12381.p ^ n
        let (c1, c2, c) := Bls12381.Fp12.frobCoeffs[n - 1]!
        if c1 != xi.pow ((pn - 1) / 3) || c2 != xi.pow ((2 * pn - 2) / 3) || c != xi.pow ((pn - 1) / 6) then
          throw (IO.userError s!"Frobenius coefficients of p^{n}")
      if Bls12381.Fp.pow Bls12381.beta 3 != 1 || Bls12381.beta == 1 then
        throw (IO.userError "beta is not a cube root of unity")
      if Bls12381.psiX.mul (xi.pow ((Bls12381.p - 1) / 3)) != .one ||
          Bls12381.psiY.mul (xi.pow ((Bls12381.p - 1) / 2)) != .one then
        throw (IO.userError "psi constants")
  | _ => #[]

/-- Oracle cases of the suite named `suite`, before the gas-at-price cases. -/
private def casesBase (suite : String) : Array OracleCase :=
  match suite with
  | "HASHCU" => cross suite #[("hashcu", .cryptoOp .hashCU)]
      ((cellPool.map (fun c => #[.cell c])) ++ #[#[sl #[]], #[.null], #[]])
  | "HASHSU" => cross suite #[("hashsu", .cryptoOp .hashSU)]
      (((cellPool.extract 0 4).map (fun c => #[.slice (Slice.ofCell c)])) ++
        #[#[.cell Cell.empty], #[bl #[]], #[.null], #[]])
  | "HASHBU" => cross suite #[("hashbu", .cellExt .hashbu)]
      #[#[bl #[]], #[bl (bytes 4 0xabcd)], #[bl (bytes 127 1)], #[bl (natToBits 5 3)],
        #[.builder { bits := bytes 1 1, refs := #[cellPool[1]!, cellPool[5]!] }], #[sl #[]], #[.null], #[]]
  | "SHA256U" => cross suite #[("sha256u", .cryptoOp .sha256U)]
      #[#[sl #[]], #[sl (bytes 1 0x61)], #[sl (bytes 3 0x616263)], #[sl (bytes 127 5)], #[unaligned],
        #[.slice (Slice.ofCell cellPool[2]!)], #[bl (bytes 1 1)], #[.null], #[]] ++
      cross suite #[("sha256u-len", .cryptoOp .sha256U)]
        (#[55, 56, 63, 64, 65, 119, 120, 126].map fun n => #[sl (noise n n)])
  | "HASHEXT" => hashExtCases suite false false
  | "HASHEXTR" => hashExtCases suite false true
  | "HASHEXTA" => hashExtCases suite true false
  | "HASHEXTAR" => hashExtCases suite true true
  | "CHKSIGNU" => chkSignCases suite false
  | "CHKSIGNS" => chkSignCases suite true
  | "ECRECOVER" => ecrecoverCases suite
  | "SECP256K1_XONLY_PUBKEY_TWEAK_ADD" => xonlyCases suite
  | "P256_CHKSIGNU" => p256Cases suite false
  | "P256_CHKSIGNS" => p256Cases suite true
  | "RIST255_FROMHASH" => ristFromHashCases suite
  | "RIST255_VALIDATE" => ristValidateCases suite false
  | "RIST255_QVALIDATE" => ristValidateCases suite true
  | "RIST255_ADD" => ristAddSubCases suite .rist255Add
  | "RIST255_SUB" => ristAddSubCases suite .rist255Sub
  | "RIST255_QADD" => ristAddSubCases suite .rist255Qadd
  | "RIST255_QSUB" => ristAddSubCases suite .rist255Qsub
  | "RIST255_MUL" => ristMulCases suite false
  | "RIST255_QMUL" => ristMulCases suite true
  | "RIST255_MULBASE" => ristMulBaseCases suite false
  | "RIST255_QMULBASE" => ristMulBaseCases suite true
  | "RIST255_PUSHL" => named suite #[ext .rist255PushL] #[("empty", #[]), ("on-stack", #[iv 1])]
  | "BLS_VERIFY" => blsVerifyCases suite
  | "BLS_AGGREGATE" => blsAggregateCases suite
  | "BLS_FASTAGGREGATEVERIFY" => blsFastAggVerifyCases suite
  | "BLS_AGGREGATEVERIFY" => blsAggVerifyCases suite
  | "BLS_MAP_TO_G1" => blsMapCases suite false
  | "BLS_MAP_TO_G2" => blsMapCases suite true
  | "BLS_PAIRING" => blsPairingCases suite
  | "BLS_PUSHR" => named suite #[ext .blsPushR] #[("empty", #[]), ("on-stack", #[iv 1])]
  | _ =>
      if suite.startsWith "BLS_G1_" then blsGroupCases suite false
      else if suite.startsWith "BLS_G2_" then blsGroupCases suite true
      else #[]

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  casesBase suite ++ chargeLimitCasesFor suite

private def randBytes (n : Nat) (rng0 : StdGen) : Array UInt8 × StdGen := Id.run do
  let mut out : Array UInt8 := #[]
  let mut rng := rng0
  for _ in [0:n] do
    let (b, rng') := randNat rng 0 255
    out := out.push (UInt8.ofNat b)
    rng := rng'
  return (out, rng)

/-- Up to 127 random bytes, one time in 16 with 4 bits more (data that is not byte-aligned). -/
private def randHashData (rng0 : StdGen) : BitString × StdGen :=
  let (n, rng1) := randNat rng0 0 127
  let (bs, rng2) := randBytes n rng1
  let (k, rng3) := randNat rng2 0 15
  (bitsOfBytes bs ++ (if k = 0 ∧ n < 127 then natToBits 5 4 else #[]), rng3)

/-- HASHEXT{A}{R} on up to 8 random entries (slices and builders), with a random algorithm (or one
from the stack, 0..5) and, for HASHEXTA, a builder of up to 70 bytes (the digest overflowing it
from 64). -/
private def genHashExtFuzz (suite : String) (append rev : Bool) (rng0 : StdGen) : OracleCase × StdGen := Id.run do
  let (id, rng1) := randNat rng0 0 5
  let (cnt, rng2) := randNat rng1 0 8
  let mut rng := rng2
  let mut entries : Array Value := #[]
  for _ in [0:cnt] do
    let (bits, rng') := randHashData rng
    let (isBuilder, rng'') := randBool rng'
    entries := entries.push (if isBuilder then bl bits else sl bits)
    rng := rng''
  let (blen, rng3) := randNat rng 0 70
  let (sid, rng4) := randNat rng3 0 5
  let pre : Array Value := if append then #[bl (bytes blen 0xa5)] else #[]
  let post : Array Value := if id = 5 then #[iv (Int.ofNat sid)] else #[]
  ({ name := s!"fuzz/id{id}/n{cnt}", instr := { name := suite },
     program := #[.cryptoOp (.hashExt (if id = 5 then 255 else id) append rev)],
     initStack := pre ++ entries ++ #[iv (Int.ofNat cnt)] ++ post }, rng4)

/-- SHA256U on a slice of random data. -/
private def genSha256UFuzz (rng0 : StdGen) : OracleCase × StdGen :=
  let (bits, rng1) := randHashData rng0
  ({ name := s!"fuzz/bits{bits.size}", instr := { name := "SHA256U" },
     program := #[.cryptoOp .sha256U], initStack := #[sl bits] }, rng1)

/-- An ECDSA signature `(r, s, R)` of `e` with the private key `d` and the nonce `k`. -/
private def ecdsaSign (c : Weierstrass.Curve) (e d k : Nat) : Nat × Nat × Nat × Nat :=
  match c.toAffine (c.mul k c.gen) with
  | none => (0, 0, 0, 0)
  | some (rx, ry) =>
      let r := rx % c.n
      (r, Weierstrass.invMod k c.n * ((e + r * d) % c.n) % c.n, rx, ry)

/-- ECRECOVER of a signature by a random key and nonce, as made (recovery id from `R`) or changed:
another recovery id (any up to 3, or 27/28), `s ↦ n − s`, another hash, a random `r`. -/
private def genEcrecoverFuzz (rng0 : StdGen) : OracleCase × StdGen :=
  let c := Secp256k1.curve
  let (d, rng1) := randNat rng0 1 (c.n - 1)
  let (k, rng2) := randNat rng1 1 (c.n - 1)
  let (h, rng3) := randNat rng2 0 (2 ^ 256 - 1)
  let (r, s, rx, ry) := ecdsaSign c (h % c.n) d k
  let v0 := (if ry % 2 = 1 then 1 else 0) + (if rx ≥ c.n then 2 else 0)
  let (mode, rng4) := randNat rng3 0 7
  let (x, rng5) := randNat rng4 0 (2 ^ 256 - 1)
  let (v, r, s, h, tag) :=
    match mode with
    | 0 => (v0 ^^^ 1, r, s, h, "flip-v")
    | 1 => (x % 4, r, s, h, "any-v")
    | 2 => (v0 + 27, r, s, h, "legacy-v")
    | 3 => (v0 ^^^ 1, r, c.n - s, h, "high-s")
    | 4 => (v0, r, s, x, "other-hash")
    | 5 => (v0, x, s, h, "random-r")
    | _ => (v0, r, s, h, "valid")
  ({ name := s!"fuzz/{tag}", instr := { name := "ECRECOVER" }, program := #[.cryptoOp (.ext .ecrecover)],
     initStack := #[iv (Int.ofNat h), iv (Int.ofNat v), iv (Int.ofNat r), iv (Int.ofNat s)] }, rng5)

/-- SECP256K1_XONLY_PUBKEY_TWEAK_ADD on the abscissa of a random key or a random number, with a random
tweak (sometimes above the order). -/
private def genXonlyFuzz (rng0 : StdGen) : OracleCase × StdGen :=
  let c := Secp256k1.curve
  let (d, rng1) := randNat rng0 1 (c.n - 1)
  let (x, rng2) := randNat rng1 0 (2 ^ 256 - 1)
  let (t, rng3) := randNat rng2 0 (2 ^ 256 - 1)
  let (mode, rng4) := randNat rng3 0 3
  let key := if mode = 0 then x else match c.toAffine (c.mul d c.gen) with | some (px, _) => px | none => 0
  let tweak := if mode = 1 then c.n + t % (2 ^ 256 - c.n) else t % c.n
  ({ name := s!"fuzz/mode{mode}", instr := { name := "SECP256K1_XONLY_PUBKEY_TWEAK_ADD" },
     program := #[.cryptoOp (.ext .secp256k1XonlyPubkeyTweakAdd)],
     initStack := #[iv (Int.ofNat key), iv (Int.ofNat tweak)] }, rng4)

/-- P256_CHKSIGNU/S of a signature by a random key and nonce on random data, as made or changed:
`s ↦ n − s`, the other parity of the key, another key, a random abscissa, one bit of the data. -/
private def genP256Fuzz (fromSlice : Bool) (rng0 : StdGen) : OracleCase × StdGen := Id.run do
  let c := P256.curve
  let (d, rng1) := randNat rng0 1 (c.n - 1)
  let (k, rng2) := randNat rng1 1 (c.n - 1)
  let (len, rng3) := randNat rng2 0 127
  let (data, rng4) := randBytes (if fromSlice then len else 32) rng3
  let e := bytesToNatBE (sha256Digest data) % c.n
  let (r, s, _, _) := ecdsaSign c e d k
  let (qx, qy) := match c.toAffine (c.mul d c.gen) with | some q => q | none => (0, 0)
  let (mode, rng5) := randNat rng4 0 7
  let (x, rng6) := randNat rng5 0 (2 ^ 256 - 1)
  let form : Nat := if qy % 2 = 1 then 3 else 2
  let (form, qx, s, data, tag) :=
    match mode with
    | 0 => (form, qx, c.n - s, data, "high-s")
    | 1 => (5 - form, qx, s, data, "other-parity")
    | 2 => (form, x, s, data, "random-key")
    | 3 => (form, qx, s, (if data.isEmpty then #[0] else data.set! 0 (data[0]! ^^^ 1)), "other-data")
    | 4 => (form, qx, x, data, "random-s")
    | _ => (form, qx, s, data, "valid")
  let dataV : Value := if fromSlice then sl (bitsOfBytes data) else iv (Int.ofNat (bytesToNatBE data))
  let key := sl (bitsOfBytes (#[UInt8.ofNat form] ++ natToBytesBEFixed qx 32))
  let sig := sl (bitsOfBytes (natToBytesBEFixed r 32 ++ natToBytesBEFixed s 32))
  let suite := if fromSlice then "P256_CHKSIGNS" else "P256_CHKSIGNU"
  return ({ name := s!"fuzz/{tag}", instr := { name := suite },
            program := #[ext (if fromSlice then .p256ChkSignS else .p256ChkSignU)],
            initStack := #[dataV, sig, key] }, rng6)

/-- A ristretto255 operand (the encoding read big-endian, as C++ exports the integer): an element
from random hash bytes, the same with one bit flipped, a random number, the identity 0, or a number
from `p` on (not canonical). -/
private def randRistOperand (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 7
  let (hb, rng2) := randBytes 64 rng1
  let (x, rng3) := randNat rng2 0 (2 ^ 256 - 1)
  let enc := Ristretto255.fromHash hb
  let v : Nat :=
    match mode with
    | 0 | 1 | 2 => bytesToNatBE enc
    | 3 => bytesToNatBE enc ^^^ (1 <<< (x % 256))
    | 4 => x
    | 5 => 0
    | _ => bytesToNatBE (natToBytesBEFixed (Ed25519.p + x % 64) 32).reverse
  (Int.ofNat v, rng3)

/-- A scalar for RIST255_MUL{BASE}: random 256-bit, small, a multiple of `l` (plus a little),
negative, or 0. -/
private def randRistScalar (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 5
  let (x, rng2) := randNat rng1 0 (2 ^ 256 - 1)
  let n : Int :=
    match mode with
    | 0 => Int.ofNat x
    | 1 => Int.ofNat (x % 16)
    | 2 => rist255L * Int.ofNat (x % 4) + Int.ofNat (x / 4 % 3)
    | 3 => -Int.ofNat x
    | _ => 0
  (n, rng2)

private def ristFuzzCase (suite : String) (op : CryptoExtInstr) (stack : Array Value) : OracleCase :=
  { name := "fuzz", instr := { name := suite }, program := #[ext op], initStack := stack }

/-- Random operands for the ristretto255 instruction `op` of the suite `suite`. -/
private def genRistFuzz (suite : String) (op : CryptoExtInstr) (rng0 : StdGen) : OracleCase × StdGen :=
  let (x, rng1) := randRistOperand rng0
  let (y, rng2) := randRistOperand rng1
  let (n, rng3) := randRistScalar rng2
  let (h1, rng4) := randNat rng3 0 (2 ^ 256 - 1)
  let (same, rng5) := randNat rng4 0 4
  let y := if same = 0 then x else y
  let stack : Array Value :=
    match op with
    | .rist255FromHash => #[iv (Int.ofNat h1), iv x]
    | .rist255Validate | .rist255Qvalidate => #[iv x]
    | .rist255Mul | .rist255Qmul => #[iv x, iv n]
    | .rist255MulBase | .rist255QmulBase => #[iv n]
    | _ => #[iv x, iv y]
  (ristFuzzCase suite op stack, rng5)

/-! #### BLS12-381 fuzz

Points and signatures are made with the model's own BLS12-381 (`TvmLean.Bls12381`) when the cases
are generated, then changed; C++ judges every case. -/

/-- A scalar for BLS_G{1,2}_MUL / _MULTIEXP: random 256-bit, small, around a multiple of `r`,
negative, 0, below 2^128 (the size of the GLV halves), `2^256 − 1` or `−2^256`, below `r`. -/
private def randBlsScalar (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  let (x, rng2) := randNat rng1 0 (2 ^ 256 - 1)
  let n : Int :=
    match mode with
    | 0 | 1 => Int.ofNat x
    | 2 => Int.ofNat (x % 20)
    | 3 => blsR * Int.ofNat (x % 3) + Int.ofNat (x / 3 % 3) - 1
    | 4 => -Int.ofNat x
    | 5 => 0
    | 6 => Int.ofNat (x % 2 ^ 128)
    | 7 => if x % 2 = 0 then 2 ^ 256 - 1 else -(2 ^ 256)
    | _ => Int.ofNat x % blsR
  (n, rng2)

private def flipBitOf (b : Array UInt8) (k : Nat) : Array UInt8 :=
  if b.isEmpty then b
  else
    let i := k / 8 % b.size
    b.set! i (b[i]! ^^^ UInt8.ofNat (1 <<< (k % 8)))

/-- The first abscissa from `x` on whose compressed encoding (sign flag `sgn`) is a point of E1
(almost never in G1); the point at infinity after 64 tries. -/
private def onCurveG1 (x : Nat) (sgn : Bool) : Array UInt8 := Id.run do
  for i in [0:64] do
    let b := Bls12381.natToBE ((x + i) % Bls12381.p) 48
    let b := b.set! 0 (b[0]! ||| 0x80 ||| (if sgn then 0x20 else 0))
    if (Bls12381.decodeG1 b).isSome then return b
  return Bls12381.infEncoding 48

/-- As `onCurveG1` on E2, the imaginary part counting up from `x`. -/
private def onCurveG2 (x : Nat) (sgn : Bool) : Array UInt8 := Id.run do
  for i in [0:64] do
    let b := Bls12381.natToBE ((x + i) % Bls12381.p) 48 ++ Bls12381.natToBE (x / 2 ^ 384 % Bls12381.p) 48
    let b := b.set! 0 (b[0]! ||| 0x80 ||| (if sgn then 0x20 else 0))
    if (Bls12381.decodeG2 b).isSome then return b
  return Bls12381.infEncoding 96

/-- `k · G` compressed (`k` nonzero). -/
private def blsGenMul (g2 : Bool) (k : Nat) : Array UInt8 :=
  (if g2 then Bls12381.g2MulInt g2GenB (Int.ofNat k) else Bls12381.g1MulInt g1GenB (Int.ofNat k)).getD #[]

/-- A G1 (G2 for `g2`) operand: mostly a multiple of the generator; a point of the curve off the
subgroup; the point at infinity; a point of small order; one bit flipped; random bytes; an abscissa
(or, on E2, one part of it) from `p` on; the infinity flag with another bit or with the sign flag;
no compression flag; the abscissa 0; the other ordinate. -/
private def randBlsPoint (g2 : Bool) (rng0 : StdGen) : Array UInt8 × StdGen :=
  let (mode, rng1) := randNat rng0 0 19
  let (k, rng2) := randNat rng1 1 (2 ^ 255)
  let (x, rng3) := randNat rng2 0 (2 ^ 800)
  let size := if g2 then 96 else 48
  let valid (_ : Unit) : Array UInt8 := blsGenMul g2 k
  let b : Array UInt8 :=
    match mode with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => valid ()
    | 7 | 8 => if g2 then onCurveG2 x (x % 2 = 1) else onCurveG1 x (x % 2 = 1)
    | 9 => Bls12381.infEncoding size
    | 10 =>
        hexBytes (lookupHex (if g2 then blsExtraG2 else blsExtraG1)
          (if g2 then (if x % 2 = 0 then "order13" else "order23") else "order11"))
    | 11 => flipBitOf (valid ()) x
    | 12 => Bls12381.natToBE x size
    | 13 =>
        let big := Bls12381.natToBE (Bls12381.p + x % 4) 48
        let b :=
          if !g2 then big
          else if x % 8 < 4 then big ++ Bls12381.natToBE 1 48 else Bls12381.natToBE 1 48 ++ big
        b.set! 0 (b[0]! ||| 0x80 ||| (if x % 16 < 8 then 0x20 else 0))
    | 14 => (Bls12381.infEncoding size).set! (1 + x % (size - 1)) (UInt8.ofNat (1 + x % 255))
    | 15 => (Bls12381.infEncoding size).set! 0 0xe0
    | 16 => let v := valid (); v.set! 0 (v[0]! &&& 0x7f)
    | 17 => (Bls12381.infEncoding size).set! 0 (if x % 2 = 0 then 0x80 else 0xa0)
    | _ => let v := valid (); v.set! 0 (v[0]! ^^^ 0x20)
  (b, rng3)

/-- A point that decodes: a multiple of the generator, the point at infinity (one time in ten), a
point off the subgroup (one time in ten). -/
private def randBlsPointOk (g2 : Bool) (rng0 : StdGen) : Array UInt8 × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  let (k, rng2) := randNat rng1 1 (2 ^ 255)
  let (x, rng3) := randNat rng2 0 (2 ^ 800)
  let b :=
    match mode with
    | 0 => Bls12381.infEncoding (if g2 then 96 else 48)
    | 1 => if g2 then onCurveG2 x (x % 2 = 1) else onCurveG1 x (x % 2 = 1)
    | _ => blsGenMul g2 k
  (b, rng3)

private def blsFuzzCase (suite tag : String) (op : CryptoExtInstr) (stack : Array Value) : OracleCase :=
  { name := s!"fuzz/{tag}", instr := { name := suite }, program := #[ext op], initStack := stack }

/-- G1/G2 ADD, SUB, NEG, INGROUP, ISZERO, MUL on random operands (for ADD/SUB the same point twice,
or a point and its negation, one time in six each). -/
private def genBlsGroupFuzz (suite : String) (g2 : Bool) (op : CryptoExtInstr) (rng0 : StdGen) :
    OracleCase × StdGen :=
  let (a, rng1) := randBlsPoint g2 rng0
  let (b0, rng2) := randBlsPoint g2 rng1
  let (rel, rng3) := randNat rng2 0 5
  let (x, rng4) := randBlsScalar rng3
  let b :=
    if rel = 0 then a
    else if rel = 1 then (if g2 then Bls12381.g2Neg a else Bls12381.g1Neg a).getD b0
    else b0
  let stack : Array Value :=
    match op with
    | .blsG1Add | .blsG1Sub | .blsG2Add | .blsG2Sub => #[blsBytesV a, blsBytesV b]
    | .blsG1Mul | .blsG2Mul => #[blsBytesV a, iv x]
    | _ => #[blsBytesV a]
  (blsFuzzCase suite s!"rel{rel}" op stack, rng4)

/-- G1/G2 MULTIEXP: up to 8 pairs, or 28 to 36 (around the 32 points where blst passes from
tables to buckets) one time in eight; the points decodable two times in three (multiples of the
generator, infinity, off the subgroup), else any. -/
private def genBlsMultiExpFuzz (suite : String) (g2 : Bool) (rng0 : StdGen) : OracleCase × StdGen := Id.run do
  let (big, rng1) := randNat rng0 0 7
  let (n0, rng2) := randNat rng1 0 8
  let (n1, rng3) := randNat rng2 28 36
  let (clean, rng4) := randNat rng3 0 2
  let n := if big = 0 then n1 else n0
  let mut rng := rng4
  let mut st : Array Value := #[]
  for _ in [0:n] do
    let (pt, r1) := if clean < 2 then randBlsPointOk g2 rng else randBlsPoint g2 rng
    let (x, r2) := randBlsScalar r1
    st := st ++ #[blsBytesV pt, iv x]
    rng := r2
  return (blsFuzzCase suite s!"n{n}/clean{clean}" (if g2 then .blsG2MultiExp else .blsG1MultiExp)
    (st ++ #[iv (Int.ofNat n)]), rng)

/-- MAP_TO_G1/G2: random bytes, the top bits cleared, around `p`, all ones, zeros. -/
private def genBlsMapFuzz (suite : String) (g2 : Bool) (rng0 : StdGen) : OracleCase × StdGen :=
  let size := if g2 then 96 else 48
  let (mode, rng1) := randNat rng0 0 7
  let (bs, rng2) := randBytes size rng1
  let (d, rng3) := randNat rng2 0 4
  let pBytes := Bls12381.natToBE (Bls12381.p + d - 2) 48
  let b : Array UInt8 :=
    match mode with
    | 0 => bs.set! 0 (bs[0]! &&& 0x1f)
    | 1 => if g2 then (if d % 2 = 0 then pBytes ++ bs.extract 48 96 else bs.extract 0 48 ++ pBytes) else pBytes
    | 2 => Array.replicate size 0xff
    | 3 => Array.replicate size 0
    | _ => bs
  (blsFuzzCase suite s!"mode{mode}" (if g2 then .blsMapToG2 else .blsMapToG1) #[blsBytesV b], rng3)

/-- `point + Q` for `Q` the point of E2 off the subgroup decoded from `q` (unchanged if `q` does not
decode). -/
private def g2PlusOff (sig : Array UInt8) (q : Array UInt8) : Array UInt8 :=
  match Bls12381.decodeG2 sig, Bls12381.decodeG2 q with
  | some a, some b =>
      Bls12381.compressG2 (Bls12381.Jac.add Bls12381.fp2F (Bls12381.Jac.ofAff Bls12381.fp2F a)
        (Bls12381.Jac.ofAff Bls12381.fp2F b))
  | _, _ => sig

/-- BLS_VERIFY of a signature by a random key on a random message, as made or changed: another
message, another key, a random or flipped signature, a random key, infinity for the key or the
signature, the signature plus a point off G2, a key off G1. -/
private def genBlsVerifyFuzz (rng0 : StdGen) : OracleCase × StdGen :=
  let (sk, rng1) := randNat rng0 1 (Bls12381.r - 1)
  let (len, rng2) := randNat rng1 0 127
  let (msg, rng3) := randBytes len rng2
  let (mode, rng4) := randNat rng3 0 11
  let (k, rng5) := randNat rng4 0 (2 ^ 800)
  let pk := blsGenMul false sk
  let sig := Bls12381.compressG2 (blsSign sk msg)
  let (other, rng6) := if mode = 3 then randBlsPoint false rng5 else (#[], rng5)
  let (otherSig, rng7) := if mode = 2 then randBlsPoint true rng6 else (#[], rng6)
  let (pk, msg, sig, tag) :=
    match mode with
    | 0 => (pk, (if msg.isEmpty then #[0] else flipBitOf msg k), sig, "other-msg")
    | 1 => (blsGenMul false (sk + 1), msg, sig, "other-pk")
    | 2 => (pk, msg, otherSig, "random-sig")
    | 3 => (other, msg, sig, "random-pk")
    | 4 => (pk, msg, Bls12381.infEncoding 96, "sig-inf")
    | 5 => (Bls12381.infEncoding 48, msg, sig, "pk-inf")
    | 6 => (pk, msg, g2PlusOff sig (onCurveG2 k (k % 2 = 1)), "sig-off-subgroup")
    | 7 => (onCurveG1 k (k % 2 = 1), msg, sig, "pk-off-subgroup")
    | 8 => (pk, msg, flipBitOf sig k, "flip-sig")
    | _ => (pk, msg, sig, "valid")
  (blsFuzzCase "BLS_VERIFY" tag .blsVerify #[blsBytesV pk, blsBytesV msg, blsBytesV sig], rng7)

/-- BLS_AGGREGATE of one to four signatures: multiples of the generator of G2, points off G2,
infinity, any. -/
private def genBlsAggregateFuzz (rng0 : StdGen) : OracleCase × StdGen := Id.run do
  let (n, rng1) := randNat rng0 1 4
  let mut rng := rng1
  let mut st : Array Value := #[]
  for _ in [0:n] do
    let (m, r1) := randNat rng 0 5
    let (pt, r2) := if m < 4 then randBlsPointOk true r1 else randBlsPoint true r1
    st := st.push (blsBytesV pt)
    rng := r2
  return (blsFuzzCase "BLS_AGGREGATE" s!"n{n}" .blsAggregate (st ++ #[iv (Int.ofNat n)]), rng)

/-- BLS_FASTAGGREGATEVERIFY: up to four keys signing one message, the signatures added, as made or
changed: another message, a random key or signature, a key at infinity, a key off G1 first or later,
keys cancelling, a key twice, the signature at infinity. -/
private def genBlsFastAggFuzz (rng0 : StdGen) : OracleCase × StdGen := Id.run do
  let (n, rng1) := randNat rng0 0 4
  let (len, rng2) := randNat rng1 0 127
  let (msg, rng3) := randBytes len rng2
  let mut rng := rng3
  let mut sks : Array Nat := #[]
  for _ in [0:n] do
    let (sk, r1) := randNat rng 1 (Bls12381.r - 1)
    sks := sks.push sk
    rng := r1
  let total := sks.foldl (fun a b => (a + b) % Bls12381.r) 0
  let mut pks := sks.map (blsGenMul false)
  let mut sig := if total = 0 then Bls12381.infEncoding 96 else Bls12381.compressG2 (blsSign total msg)
  let mut msg := msg
  let (mode, r2) := randNat rng 0 11
  let (k, r3) := randNat r2 0 (2 ^ 800)
  rng := r3
  let i := if n = 0 then 0 else k % n
  match mode with
  | 0 => msg := if msg.isEmpty then #[1] else flipBitOf msg k
  | 1 =>
      if n > 0 then
        let (p, r) := randBlsPoint false rng
        pks := pks.set! i p
        rng := r
  | 2 =>
      let (s, r) := randBlsPoint true rng
      sig := s
      rng := r
  | 3 => if n > 0 then pks := pks.set! i (Bls12381.infEncoding 48)
  | 4 => if n > 0 then pks := pks.set! 0 (onCurveG1 k (k % 2 = 1))
  | 5 => if n > 1 then pks := pks.set! (1 + k % (n - 1)) (onCurveG1 k (k % 2 = 1))
  | 6 => if n > 1 then pks := pks.set! 1 ((Bls12381.g1Neg pks[0]!).getD pks[1]!)
  | 7 => if n > 1 then pks := pks.set! 1 pks[0]!
  | 8 => sig := Bls12381.infEncoding 96
  | _ => pure ()
  return (blsFuzzCase "BLS_FASTAGGREGATEVERIFY" s!"n{n}/mode{mode}" .blsFastAggregateVerify
    ((pks.map blsBytesV) ++ #[iv (Int.ofNat n), blsBytesV msg, blsBytesV sig]), rng)

/-- BLS_AGGREGATEVERIFY: up to ten keys with their messages (distinct, or one message for all one
time in three), the signatures added, as made or changed: one message changed, a random key or
signature, the signature at infinity, a key at infinity, two messages swapped, the signature plus a
point off G2. -/
private def genBlsAggVerifyFuzz (rng0 : StdGen) : OracleCase × StdGen := Id.run do
  let (n, rng1) := randNat rng0 0 10
  let (dup, rng2) := randNat rng1 0 2
  let (len0, rng3) := randNat rng2 0 60
  let (shared, rng4) := randBytes len0 rng3
  let mut rng := rng4
  let mut sks : Array Nat := #[]
  let mut msgs : Array (Array UInt8) := #[]
  for _ in [0:n] do
    let (sk, r1) := randNat rng 1 (Bls12381.r - 1)
    let (len, r2) := randNat r1 0 60
    let (m, r3) := randBytes len r2
    sks := sks.push sk
    msgs := msgs.push (if dup = 0 then shared else m)
    rng := r3
  let mut pks := sks.map (blsGenMul false)
  let sum := (Array.range n).foldl (fun acc j => Bls12381.Jac.add Bls12381.fp2F acc (blsSign sks[j]! msgs[j]!))
    (Bls12381.Jac.inf Bls12381.fp2F)
  let mut sig := Bls12381.compressG2 sum
  let (mode, r2) := randNat rng 0 10
  let (k, r3) := randNat r2 0 (2 ^ 800)
  rng := r3
  let i := if n = 0 then 0 else k % n
  match mode with
  | 0 => if n > 0 then msgs := msgs.set! i (if msgs[i]!.isEmpty then #[7] else flipBitOf msgs[i]! k)
  | 1 =>
      if n > 0 then
        let (p, r) := randBlsPoint false rng
        pks := pks.set! i p
        rng := r
  | 2 =>
      let (s, r) := randBlsPoint true rng
      sig := s
      rng := r
  | 3 => sig := Bls12381.infEncoding 96
  | 4 => if n > 0 then pks := pks.set! i (Bls12381.infEncoding 48)
  | 5 => if n > 1 then msgs := (msgs.set! 0 msgs[1]!).set! 1 msgs[0]!
  | 6 => sig := g2PlusOff sig (onCurveG2 k (k % 2 = 1))
  | _ => pure ()
  let st := (Array.range n).flatMap fun j => #[blsBytesV pks[j]!, blsBytesV msgs[j]!]
  return (blsFuzzCase "BLS_AGGREGATEVERIFY" s!"n{n}/mode{mode}" .blsAggregateVerify
    (st ++ #[iv (Int.ofNat n), blsBytesV sig]), rng)

/-- BLS_PAIRING: up to ten pairs `(aᵢ G1, bᵢ G2)` and a last `(−Σ aᵢbᵢ G1, G2)` (the product is 1),
as made or changed: a pair with a G1, G2 or both points at infinity inserted anywhere (the batches of
eight), a random point, a point of E1 and its negation against one point of E2. -/
private def genBlsPairingFuzz (rng0 : StdGen) : OracleCase × StdGen := Id.run do
  let (n, rng1) := randNat rng0 1 10
  let mut rng := rng1
  let mut pairs : Array (Array UInt8 × Array UInt8) := #[]
  let mut acc : Nat := 0
  for _ in [0:n - 1] do
    let (a, r1) := randNat rng 1 (Bls12381.r - 1)
    let (b, r2) := randNat r1 1 (Bls12381.r - 1)
    acc := (acc + a * b) % Bls12381.r
    pairs := pairs.push (blsGenMul false a, blsGenMul true b)
    rng := r2
  let last := (Bls12381.r - acc) % Bls12381.r
  pairs := pairs.push
    (if last = 0 then Bls12381.infEncoding 48 else blsGenMul false last, g2GenB)
  let (mode, r2) := randNat rng 0 9
  let (k, r3) := randNat r2 0 (2 ^ 800)
  rng := r3
  let pos := k % (pairs.size + 1)
  let i := k % pairs.size
  match mode with
  | 0 => pairs := pairs.insertIdxIfInBounds pos (Bls12381.infEncoding 48, g2GenB)
  | 1 => pairs := pairs.insertIdxIfInBounds pos (g1GenB, Bls12381.infEncoding 96)
  | 2 => pairs := pairs.insertIdxIfInBounds pos (Bls12381.infEncoding 48, Bls12381.infEncoding 96)
  | 3 =>
      let (p, r) := randBlsPoint false rng
      pairs := pairs.set! i (p, pairs[i]!.2)
      rng := r
  | 4 =>
      let (q, r) := randBlsPoint true rng
      pairs := pairs.set! i (pairs[i]!.1, q)
      rng := r
  | 5 =>
      let p := onCurveG1 k (k % 2 = 1)
      let q := if k % 4 < 2 then onCurveG2 (k / 7) (k % 3 = 0) else g2GenB
      pairs := (pairs.push (p, q)).push ((Bls12381.g1Neg p).getD p, q)
  | _ => pure ()
  let st := pairs.flatMap fun (p, q) => #[blsBytesV p, blsBytesV q]
  return (blsFuzzCase "BLS_PAIRING" s!"n{pairs.size}/mode{mode}" .blsPairing
    (st ++ #[iv (Int.ofNat pairs.size)]), rng)

/-- BLS_G1_ZERO, BLS_G2_ZERO, BLS_PUSHR on a stack of up to two random integers. -/
private def genBlsConstFuzz (suite : String) (op : CryptoExtInstr) (rng0 : StdGen) : OracleCase × StdGen :=
  let (n, rng1) := randNat rng0 0 2
  let (x, rng2) := randNat rng1 0 (2 ^ 256)
  (blsFuzzCase suite s!"n{n}" op ((Array.range n).map fun j => iv (Int.ofNat (x / (j + 1)))), rng2)

/-- Fuzz specs of the suite named `suite`: random data for the hash instructions, random
signatures for secp256k1 and P-256, random operands for ristretto255, random and changed points,
signatures and pairings for BLS12-381, computed in Lean. -/
def fuzzFor (suite : String) : Array FuzzSpec :=
  let rist (op : CryptoExtInstr) (seed : UInt64) : Array FuzzSpec :=
    #[{ seed := seed, count := 300, gen := genRistFuzz suite op }]
  match suite with
  | "RIST255_FROMHASH" => rist .rist255FromHash 2026102010
  | "RIST255_VALIDATE" => rist .rist255Validate 2026102011
  | "RIST255_QVALIDATE" => rist .rist255Qvalidate 2026102012
  | "RIST255_ADD" => rist .rist255Add 2026102013
  | "RIST255_SUB" => rist .rist255Sub 2026102014
  | "RIST255_QADD" => rist .rist255Qadd 2026102015
  | "RIST255_QSUB" => rist .rist255Qsub 2026102016
  | "RIST255_MUL" => rist .rist255Mul 2026102017
  | "RIST255_QMUL" => rist .rist255Qmul 2026102018
  | "RIST255_MULBASE" => rist .rist255MulBase 2026102019
  | "RIST255_QMULBASE" => rist .rist255QmulBase 2026102020
  | "ECRECOVER" => #[{ seed := 2026102006, count := 300, gen := genEcrecoverFuzz }]
  | "SECP256K1_XONLY_PUBKEY_TWEAK_ADD" => #[{ seed := 2026102007, count := 300, gen := genXonlyFuzz }]
  | "P256_CHKSIGNU" => #[{ seed := 2026102008, count := 300, gen := genP256Fuzz false }]
  | "P256_CHKSIGNS" => #[{ seed := 2026102009, count := 300, gen := genP256Fuzz true }]
  | "HASHEXT" => #[{ seed := 2026102001, count := 400, gen := genHashExtFuzz suite false false }]
  | "HASHEXTR" => #[{ seed := 2026102002, count := 400, gen := genHashExtFuzz suite false true }]
  | "HASHEXTA" => #[{ seed := 2026102003, count := 400, gen := genHashExtFuzz suite true false }]
  | "HASHEXTAR" => #[{ seed := 2026102004, count := 400, gen := genHashExtFuzz suite true true }]
  | "SHA256U" => #[{ seed := 2026102005, count := 300, gen := genSha256UFuzz }]
  | "BLS_VERIFY" => #[{ seed := 2026102101, count := 200, gen := genBlsVerifyFuzz }]
  | "BLS_AGGREGATE" => #[{ seed := 2026102102, count := 200, gen := genBlsAggregateFuzz }]
  | "BLS_FASTAGGREGATEVERIFY" => #[{ seed := 2026102103, count := 200, gen := genBlsFastAggFuzz }]
  | "BLS_AGGREGATEVERIFY" => #[{ seed := 2026102104, count := 150, gen := genBlsAggVerifyFuzz }]
  | "BLS_PAIRING" => #[{ seed := 2026102105, count := 200, gen := genBlsPairingFuzz }]
  | "BLS_MAP_TO_G1" => #[{ seed := 2026102106, count := 200, gen := genBlsMapFuzz suite false }]
  | "BLS_MAP_TO_G2" => #[{ seed := 2026102107, count := 200, gen := genBlsMapFuzz suite true }]
  | "BLS_G1_MULTIEXP" => #[{ seed := 2026102108, count := 200, gen := genBlsMultiExpFuzz suite false }]
  | "BLS_G2_MULTIEXP" => #[{ seed := 2026102109, count := 200, gen := genBlsMultiExpFuzz suite true }]
  | "BLS_G1_ADD" => #[{ seed := 2026102110, count := 300, gen := genBlsGroupFuzz suite false .blsG1Add }]
  | "BLS_G1_SUB" => #[{ seed := 2026102111, count := 300, gen := genBlsGroupFuzz suite false .blsG1Sub }]
  | "BLS_G1_NEG" => #[{ seed := 2026102112, count := 300, gen := genBlsGroupFuzz suite false .blsG1Neg }]
  | "BLS_G1_MUL" => #[{ seed := 2026102113, count := 300, gen := genBlsGroupFuzz suite false .blsG1Mul }]
  | "BLS_G1_INGROUP" => #[{ seed := 2026102114, count := 300, gen := genBlsGroupFuzz suite false .blsG1InGroup }]
  | "BLS_G1_ISZERO" => #[{ seed := 2026102115, count := 300, gen := genBlsGroupFuzz suite false .blsG1IsZero }]
  | "BLS_G2_ADD" => #[{ seed := 2026102116, count := 300, gen := genBlsGroupFuzz suite true .blsG2Add }]
  | "BLS_G2_SUB" => #[{ seed := 2026102117, count := 300, gen := genBlsGroupFuzz suite true .blsG2Sub }]
  | "BLS_G2_NEG" => #[{ seed := 2026102118, count := 300, gen := genBlsGroupFuzz suite true .blsG2Neg }]
  | "BLS_G2_MUL" => #[{ seed := 2026102119, count := 300, gen := genBlsGroupFuzz suite true .blsG2Mul }]
  | "BLS_G2_INGROUP" => #[{ seed := 2026102120, count := 300, gen := genBlsGroupFuzz suite true .blsG2InGroup }]
  | "BLS_G2_ISZERO" => #[{ seed := 2026102121, count := 300, gen := genBlsGroupFuzz suite true .blsG2IsZero }]
  | "BLS_G1_ZERO" => #[{ seed := 2026102122, count := 30, gen := genBlsConstFuzz suite .blsG1Zero }]
  | "BLS_G2_ZERO" => #[{ seed := 2026102123, count := 30, gen := genBlsConstFuzz suite .blsG2Zero }]
  | "BLS_PUSHR" => #[{ seed := 2026102124, count := 30, gen := genBlsConstFuzz suite .blsPushR }]
  | _ => #[]

end Tests.Gen.Crypto

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
gas are compared with C++.
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

private def hashExtVariants (append rev : Bool) : Array (String × Instr) :=
  #[0, 1, 2, 3, 4].map (fun id => (s!"id{id}", Instr.cryptoOp (.hashExt id append rev)))

private def hashExtCases (suite : String) (append rev : Bool) : Array OracleCase :=
  cross suite (hashExtVariants append rev) (hashExtStacks append false) ++
    cross suite #[("id-from-stack", .cryptoOp (.hashExt 255 append rev))] (hashExtStacks append true) ++
    hashExtGasCases suite append rev


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
  named suite #[ext .ecrecover] (vec ++ errs) ++
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
  named suite #[i] (vec ++ errs) ++ gasLimitCases suite i #[D, S, K] [3584, 3585, 3586, 3587]

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

private def g1v (n : String) : Value := hexSlice (lookupHex CryptoVectors.blsG1 n)
private def g2v (n : String) : Value := hexSlice (lookupHex CryptoVectors.blsG2 n)
private def msgv (n : String) : Value := hexSlice (lookupHex CryptoVectors.blsMsg n)
private def sigv (i j : Nat) : Value :=
  match CryptoVectors.blsSig.find? (fun e => e.1 == s!"s{i}_{j}") with
  | some (_, _, _, h) => hexSlice h
  | none => sl #[]
private def pkv (i : Nat) : Value := g1v s!"pk{i}"
private def blsR : Int := 52435875175126190479447740508185965837690552500527637822603658699938581184513

private def g1Bad : Array String := #["noSubgroup", "offCurve", "noCompressFlag", "xTooBig", "infNonzero"]
private def g2Bad : Array String := #["noSubgroup", "offCurve", "noCompressFlag"]

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
      ("not-slice", #[iv 5, iv 1])] ++
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
     g2Bad.map (fun b => (s!"sig-{b}", #[pkv 0, iv 1, msgv "m1", g2v b])))

private def blsAggVerifyCases (suite : String) : Array OracleCase :=
  let agg := g2v "agg_distinct"
  named suite #[ext .blsAggregateVerify]
    (#[("valid3", #[pkv 0, msgv "m0", pkv 1, msgv "m1", pkv 2, msgv "m2", iv 3, agg]),
      ("one", #[pkv 0, msgv "m1", iv 1, sigv 0 1]),
      ("swapped", #[pkv 1, msgv "m0", pkv 0, msgv "m1", pkv 2, msgv "m2", iv 3, agg]),
      ("n0", #[iv 0, agg]), ("n-too-big", #[pkv 0, msgv "m1", iv 2, agg]), ("empty", #[]), ("one-entry", #[agg]),
      ("unaligned-msg", #[pkv 0, unaligned, iv 1, sigv 0 1]), ("pk-zero", #[g1v "zero", msgv "m1", iv 1, sigv 0 1])] ++
     g1Bad.map (fun b => (s!"pk-{b}", #[g1v b, msgv "m1", iv 1, sigv 0 1])) ++
     g2Bad.map (fun b => (s!"sig-{b}", #[pkv 0, msgv "m1", iv 1, g2v b])))

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
          #[("x-nan", #[pt "gen", .int .nan]), ("x-null", #[pt "gen", .null]), ("one", #[iv 1]), ("empty", #[]),
            ("p-int", #[iv 1, iv 1])])
  | "MULTIEXP" =>
      named suite #[ext opMulti]
        #[("n0", #[iv 0]), ("n1", #[pt "gen", iv 5, iv 1]), ("n2", #[pt "gen", iv 3, pt "gen2", iv 4, iv 2]),
          ("n3", #[pt "gen", iv 3, pt "gen7", iv (-1), pt "zero", iv 9, iv 3]),
          ("n4", #[pt "gen", iv blsR, pt "gen2", iv 0, pt "gen7", iv 1, pt "gen", iv (2 ^ 256 - 1), iv 4]),
          ("n1-bad", #[pt bad[0]!, iv 5, iv 1]), ("n2-bad", #[pt "gen", iv 1, pt bad[1]!, iv 2, iv 2]),
          ("n1-bad-x0", #[pt bad[1]!, iv 0, iv 1]), ("n2-nan", #[pt "gen", .int .nan, pt "gen2", iv 1, iv 2]),
          ("n-too-big", #[pt "gen", iv 1, iv 2]), ("n-neg", #[iv (-1)]), ("empty", #[]),
          ("n2-int-point", #[iv 1, iv 1, pt "gen", iv 1, iv 2])]
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
      ("swapped", #[g2v "gen", g1v "gen", iv 1])]


/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
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
        #[.slice (Slice.ofCell cellPool[2]!)], #[bl (bytes 1 1)], #[.null], #[]]
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

end Tests.Gen.Crypto

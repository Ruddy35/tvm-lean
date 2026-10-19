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
  | _ => #[]

end Tests.Gen.Crypto

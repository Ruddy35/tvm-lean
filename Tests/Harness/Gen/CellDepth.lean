import Tests.Harness.Registry
import Tests.Harness.Gen.VmCore

/-!
Oracle cases for the depth limit of new cells. C++ `DataCell::create` (`cells/DataCell.cpp:78`,
`CellChecker::check_and_compute_level_info`) rejects a cell whose depth at some level exceeds
`CellTraits::max_depth` = 1024; `CellBuilder::finalize{,_copy,_novm}` then throws `CellWriteError`,
which `VmState::run_inner` turns into cell_ov. `finalize` and `finalize_copy` charge the creation
first (`register_cell_create`); `finalize_novm` (BTOS, HASHBU) charges nothing.

Every instruction creating a cell from the stack is run with a reference of depth 1023 and 1024, and
with references deep at level 0 only (a pruned branch storing that depth, a Merkle proof):
ENDC, ENDXC (also building a pruned branch storing a depth above 1024 and a Merkle proof or update
of a deep cell), STBREF{,R}{,Q}, ENDCST, BTOS, HASHBU, and the output actions (a deep `c5`, or a
deep message, code or reserved-currency dictionary). HASHSU and ENDC also make an ordinary cell from
the slice of a Merkle proof (`XCTOS`): the proof is shallow, but its child is deep at level 0.

Dictionary set operations (`dict_set`, `dict_lookup_set`, `dict.cpp`) create their nodes bottom-up:
the new leaf, the lower part of a split edge, then the forks up to the root. The value makes the
leaf, the split fork or the root the first node beyond the limit; the nodes created before it are
charged. Keys are 4 bits; the dictionary's values are a reference to an empty cell. A builder value
is built in the program (`NEWC; STREF; BLKSWAP 3,1`): a builder with a reference of depth 1024 has
no BOC.
-/

namespace Tests.Gen.CellDepth

open TvmLean

private def iv (n : Int) : Value := .int (.num n)
private def bitsOf (s : String) : BitString := s.toList.toArray.map (· == '1')
private def bytesBits (bs : Array UInt8) : BitString := bs.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

/-- A chain of `d` ordinary cells ending in an empty one: depth `d`. -/
def chain (d : Nat) : Cell := (List.range d).foldl (fun c _ => Cell.mkOrdinary #[] #[c]) Cell.empty

/-- Data of a pruned branch of level 1 storing depth `d` (its depth at level 0). -/
private def prunedBits (d : Nat) : BitString := natToBits 1 8 ++ natToBits 1 8 ++ natToBits 0x5a 256 ++ natToBits d 16

private def pruned (d : Nat) : Cell := { bits := prunedBits d, refs := #[], special := true, levelMask := 1 }

private def merkleProofBits (c : Cell) : BitString := natToBits 3 8 ++ bytesBits (Cell.hashBytes c) ++ natToBits c.depth 16

private def merkleUpdateBits (a b : Cell) : BitString :=
  natToBits 4 8 ++ bytesBits (Cell.hashBytes a) ++ bytesBits (Cell.hashBytes b) ++ natToBits a.depth 16 ++
    natToBits b.depth 16

private def slOf (c : Cell) : Value := .slice (Slice.ofCell c)

/-- A Merkle proof of `x` (of level 1): it stores `x`'s hash and depth at level 0 and is one deeper
than `x` at level 1. With `x` above a pruned branch storing depth `d`, the proof is 2 deep, `x` at
level 0 `d + 1`: an ordinary cell made from the proof's slice (`XCTOS`) is `d + 2` deep. -/
private def proofOverPruned (d : Nat) : Cell :=
  let x := Cell.mkOrdinary #[] #[pruned d]
  match x.computeLevelInfo? with
  | .ok info =>
      { bits := natToBits 3 8 ++ bytesBits (info.getHash 0) ++ natToBits (info.getDepth 0) 16, refs := #[x],
        special := true, levelMask := LevelMask.shiftRight x.levelMask }
  | .error _ => Cell.empty

/-- References for the instructions storing one: depth 1023 or 1024, at level 0 only (a pruned
branch of level 1, deep at level 0; a Merkle proof, its depth at level 0 one more than its
child's). -/
private def refPool : Array (String × Cell) :=
  #[("chain1023", chain 1023), ("chain1024", chain 1024), ("pruned1023", pruned 1023), ("pruned1024", pruned 1024),
    ("merkle1023", Tests.Gen.VmCore.merkleProof (chain 1022)), ("merkle1024", Tests.Gen.VmCore.merkleProof (chain 1023))]

private def mk (suite name : String) (prog : Array Instr) (stack : Array Value) : OracleCase :=
  { name := s!"oracle/depth/{name}", instr := { name := suite }, program := prog, initStack := stack }

/-- `NEWC; STREF` on each reference of `refPool`, then `ops`. -/
private def refCases (suite : String) (ops : Array Instr) : Array OracleCase :=
  refPool.map fun (n, c) => mk suite n (#[.newc, .stref] ++ ops) #[.cell c]

/-- The slice of `proofOverPruned d` (`XCTOS; DROP`), then `ops`, for `d` 1022 and 1023. -/
private def proofSliceCases (suite : String) (ops : Array Instr) : Array OracleCase :=
  #[1022, 1023].map fun d => mk suite s!"proof-slice-pruned{d}" (#[.xctos, .pop 0] ++ ops) #[.cell (proofOverPruned d)]

private def envOp (o : TonEnvInstr) : Instr := .tonEnvOp o

private def smallMsg : Cell := Cell.mkOrdinary (natToBits 5 8) #[]

/-- Output actions: the new action cell refers to `c5` (set by `POP c5`: the oracle takes no
initial `c5`) and to the message, code or dictionary. -/
private def actionCases (suite : String) : Array OracleCase :=
  let deepC5 (prog : Array Instr) (stack : Array Value) : Array OracleCase :=
    #[1023, 1024].map fun d => mk suite s!"c5-chain{d}" (#[.popCtr 5] ++ prog) (stack ++ #[.cell (chain d)])
  let deepArg (prog : Array Instr) (stack : Nat → Array Value) : Array OracleCase :=
    #[1023, 1024].map fun d => mk suite s!"arg-chain{d}" prog (stack d)
  match suite with
  | "SENDRAWMSG" =>
      deepC5 #[envOp .sendRawMsg] #[.cell smallMsg, iv 0] ++ deepArg #[envOp .sendRawMsg] fun d => #[.cell (chain d), iv 0]
  | "RAWRESERVE" => deepC5 #[envOp .rawReserve] #[iv 1000, iv 0]
  | "RAWRESERVEX" =>
      deepC5 #[envOp .rawReserveX] #[iv 1000, .null, iv 0] ++
        deepArg #[envOp .rawReserveX] fun d => #[iv 1000, .cell (chain d), iv 0]
  | "SETCODE" => deepC5 #[envOp .setCode] #[.cell smallMsg] ++ deepArg #[envOp .setCode] fun d => #[.cell (chain d)]
  | "SETLIBCODE" =>
      deepC5 #[envOp .setLibCode] #[.cell smallMsg, iv 1] ++ deepArg #[envOp .setLibCode] fun d => #[.cell (chain d), iv 1]
  | "CHANGELIB" => deepC5 #[envOp .changeLib] #[iv 5, iv 1]
  | _ => #[]

/-- ENDXC: an ordinary cell, a pruned branch storing a depth up to 1025 (built from its data), a
Merkle proof and update of a cell of depth 1023 and 1024. -/
private def endxcCases (suite : String) : Array OracleCase :=
  refPool.map (fun (n, c) => mk suite s!"ordinary-{n}" #[.newc, .stref, .pushInt (.num 0), .cellOp .endxc] #[.cell c]) ++
  (#[1023, 1024, 1025, 65535].map fun d =>
    mk suite s!"pruned-depth{d}" #[.pushInt (.num (-1)), .cellOp .endxc]
      #[.builder { bits := prunedBits d, refs := #[] }]) ++
  (#[1023, 1024].map fun d =>
    mk suite s!"merkle-proof-chain{d}" #[.newc, .stSlice false false, .stref, .pushInt (.num (-1)), .cellOp .endxc]
      #[.cell (chain d), slOf (Cell.mkOrdinary (merkleProofBits (chain d)) #[])]) ++
  (#[1023, 1024].map fun d =>
    mk suite s!"merkle-update-chain{d}"
      #[.newc, .stSlice false false, .stref, .stref, .pushInt (.num (-1)), .cellOp .endxc]
      #[.cell Cell.empty, .cell (chain d), slOf (Cell.mkOrdinary (merkleUpdateBits (chain d) Cell.empty) #[])])

/-- ENDXC on exotic data that `DataCell::create` (`CellChecker`, cells/DataCell.cpp:43-255) rejects
— fewer than 8 bits, an ordinary or unknown type byte; a pruned branch with references, cut short,
with level 0 or above 3, or with the wrong number of hashes and depths; a library cell with
references or of the wrong length; a Merkle proof or update with the wrong number of references,
of the wrong length, or storing another hash or depth than its child's — and the valid forms
(pruned branches of each level mask, a library cell, a proof, an update). All rejections are
cell_ov after the creation is charged. -/
private def endxcExoticCases (suite : String) : Array OracleCase :=
  let x : Cell := Cell.mkOrdinary (natToBits 5 8) #[]
  let y : Cell := Cell.mkOrdinary (natToBits 6 8) #[x]
  let h (c : Cell) : BitString := bytesBits (Cell.hashBytes c)
  let pruned (mask : Nat) (hashes : Nat) : BitString :=
    natToBits 1 8 ++ natToBits mask 8 ++ (List.replicate hashes (natToBits 0x77 256)).foldl (· ++ ·) #[] ++
      (List.replicate hashes (natToBits 9 16)).foldl (· ++ ·) #[]
  let proof (hash : BitString) (d : Nat) : BitString := natToBits 3 8 ++ hash ++ natToBits d 16
  let update (h1 h2 : BitString) (d1 d2 : Nat) : BitString := natToBits 4 8 ++ h1 ++ h2 ++ natToBits d1 16 ++ natToBits d2 16
  let items : Array (String × BitString × Array Cell) :=
    #[("no-bits", #[], #[]), ("seven-bits", natToBits 1 7, #[]), ("type0", natToBits 0 16, #[]),
      ("type5", natToBits 5 8 ++ natToBits 0 256, #[]), ("type255", natToBits 255 8, #[]),
      ("pruned-ok-mask1", pruned 1 1, #[]), ("pruned-ok-mask2", pruned 2 1, #[]), ("pruned-ok-mask3", pruned 3 2, #[]),
      ("pruned-ok-mask5", pruned 5 2, #[]), ("pruned-ok-mask7", pruned 7 3, #[]),
      ("pruned-refs", pruned 1 1, #[x]), ("pruned-type-only", natToBits 1 8, #[]), ("pruned-mask0", pruned 0 0, #[]),
      ("pruned-mask0-hash", pruned 0 1, #[]), ("pruned-mask8", pruned 8 1, #[]), ("pruned-mask3-one-hash", pruned 3 1, #[]),
      ("pruned-extra-byte", pruned 1 1 ++ natToBits 0 8, #[]), ("pruned-extra-bit", pruned 1 1 ++ #[true], #[]),
      ("library-ok", natToBits 2 8 ++ h x, #[]), ("library-refs", natToBits 2 8 ++ h x, #[x]),
      ("library-short", natToBits 2 8 ++ (h x).extract 0 255, #[]),
      ("proof-ok", proof (h x) 0, #[x]), ("proof-ok-deeper", proof (h y) 1, #[y]), ("proof-no-ref", proof (h x) 0, #[]),
      ("proof-two-refs", proof (h x) 0, #[x, x]), ("proof-wrong-hash", proof (h y) 0, #[x]),
      ("proof-wrong-depth", proof (h y) 2, #[y]), ("proof-extra-bit", proof (h x) 0 ++ #[false], #[x]),
      ("update-ok", update (h x) (h y) 0 1, #[x, y]), ("update-one-ref", update (h x) (h y) 0 1, #[x]),
      ("update-wrong-hash2", update (h x) (h x) 0 1, #[x, y]), ("update-wrong-depth1", update (h x) (h y) 1 1, #[x, y]),
      ("update-short", (update (h x) (h y) 0 1).extract 0 (8 + 2 * 256 + 24), #[x, y])]
  items.map fun (n, bits, refs) =>
    mk suite s!"exotic-{n}" #[.pushInt (.num (-1)), .cellOp .endxc] #[.builder { bits := bits, refs := refs }]


/-! ### Dictionary set operations -/

private inductive ValKind
  | slice
  | ref
  | builder

/-- The instruction of a dictionary set suite and the kind of its key (`intKey`, `unsigned`) and value. -/
private def dictSuite? (s : String) : Option (Instr × Bool × Bool × ValKind) := do
  if !s.startsWith "DICT" then none
  let r := s.drop 4
  let (intKey, unsigned, r) :=
    if r.startsWith "I" then (true, false, r.drop 1) else if r.startsWith "U" then (true, true, r.drop 1) else (false, false, r)
  let (mode, mutMode, r) ←
    if r.startsWith "SET" then some (DictSetMode.set, DictMutMode.set, r.drop 3)
    else if r.startsWith "ADD" then some (.add, .add, r.drop 3)
    else if r.startsWith "REPLACE" then some (.replace, .replace, r.drop 7)
    else none
  let (get, r) := if r.startsWith "GET" then (true, r.drop 3) else (false, r)
  match get, r with
  | false, "" => some (.dictSet intKey unsigned false mode, intKey, unsigned, .slice)
  | false, "REF" => some (.dictSet intKey unsigned true mode, intKey, unsigned, .ref)
  | false, "B" =>
      some (if mode == .replace then .dictReplaceB intKey unsigned else .dictSetB intKey unsigned mode, intKey, unsigned, .builder)
  | true, "" => some (.dictExt (.mutGet intKey unsigned false mutMode), intKey, unsigned, .slice)
  | true, "REF" => some (.dictExt (.mutGet intKey unsigned true mutMode), intKey, unsigned, .ref)
  | true, "B" => some (.dictExt (.mutGetB intKey unsigned mode), intKey, unsigned, .builder)
  | true, "OPTREF" => if mode == .set then some (.dictExt (.setGetOptRef intKey unsigned), intKey, unsigned, .ref) else none
  | _, _ => none

/-- A dictionary with 4-bit keys `keys`, each value a reference to an empty cell. -/
private def dictOf (keys : Array String) : Value :=
  let root := keys.foldl (fun root k =>
    match dictSetSliceWithCells root (bitsOf k) (Slice.ofCell (Cell.mkOrdinary #[] #[Cell.empty])) .set with
    | .ok (some r, _, _, _) => some r
    | _ => root) none
  match root with
  | some r => .cell r
  | none => .null

private def keyVal (intKey unsigned : Bool) (k : String) : Value :=
  let b := bitsOf k
  if !intKey then .slice (Slice.ofCell (Cell.mkOrdinary b #[]))
  else if unsigned then iv (Int.ofNat (bitsToNat b))
  else iv (natToIntSignedTwos (bitsToNat b) 4)

/-- (name, keys of the dictionary, key set, depth of the value's reference): the leaf of an empty
or one-entry dictionary (depth 1025), the fork splitting an edge (the leaf 1024 deep), the root above
the replaced leaf or above the split fork, and the same paths one level short of the limit. -/
private def dictScenarios : Array (String × Array String × String × Nat) :=
  #[("empty-leaf", #[], "0011", 1024), ("replace-leaf", #["0011"], "0011", 1024),
    ("split-fork", #["0011"], "0101", 1023), ("replace-root", #["0000", "1000"], "0000", 1023),
    ("split-root", #["0000", "1000"], "0001", 1022), ("split-ok", #["0000", "1000"], "0001", 1021),
    ("replace-ok", #["0000", "1000"], "0000", 1022)]

private def dictCases (suite : String) : Array OracleCase :=
  match dictSuite? suite with
  | none => #[]
  | some (op, intKey, unsigned, kind) =>
      dictScenarios.map fun (name, keys, k, d) =>
        let below : Array Value := #[keyVal intKey unsigned k, dictOf keys, iv 4]
        match kind with
        | .ref => mk suite s!"dict-{name}" #[op] (#[.cell (chain d)] ++ below)
        -- the slice's cell holds the reference, so it is at most 1023 deep
        | .slice => mk suite s!"dict-{name}" #[op] (#[slOf (Cell.mkOrdinary #[] #[chain (Nat.min d 1023)])] ++ below)
        | .builder => mk suite s!"dict-{name}" #[.newc, .stref, .blkSwap 3 1, op] (below ++ #[.cell (chain d)])

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "ENDC" => refCases suite #[.endc] ++ proofSliceCases suite #[.newc, .stSlice false false, .endc]
  | "HASHSU" => proofSliceCases suite #[.cryptoOp .hashSU]
  | "ENDXC" => endxcCases suite ++ endxcExoticCases suite
  -- the resulting builder is dropped: its reference may be 1024 deep, and the oracle prints a
  -- builder by finalizing it
  | "STBREF" => refCases suite #[.newc, .stbRef false false, .pop 0]
  | "STBREFQ" => refCases suite #[.newc, .stbRef false true, .pop 0, .pop 0]
  | "STBREFR" => refCases suite #[.newc, .xchg0 1, .stbRef true false, .pop 0]
  | "STBREFRQ" => refCases suite #[.newc, .xchg0 1, .stbRef true true, .pop 0, .pop 0]
  | "ENDCST" => refCases suite #[.newc, .xchg0 1, .endcst, .pop 0]
  | "BTOS" => refCases suite #[.cellExt .btos]
  | "HASHBU" => refCases suite #[.cellExt .hashbu]
  | _ => actionCases suite ++ dictCases suite

end Tests.Gen.CellDepth

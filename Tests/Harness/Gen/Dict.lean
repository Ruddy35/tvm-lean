import Tests.Harness.Registry
import Tests.Harness.Gen.CellDepth
import Tests.Harness.Gen.Control

/-!
Oracle cases for dictionary paths the full coverage run of 2026-10-19 did not reach
(`crypto/vm/dict.cpp`, `dictops.cpp`):

- prefix-code dictionaries with several entries: `pfx_dict_set` and `pfx_dict_lookup_delete`
  through fork nodes (insertion splitting an edge or going down a fork, deletion merging the
  remaining child into its parent edge), lookups of keys, of non-keys, of proper prefixes of keys
  and of keys extended past a leaf. The dictionary is built in the program by chained
  `PFXDICTSET`s from `null`, then the instruction under test runs on it;
- `DICT{I,U}DEL`, `DICT{I,U}DELGET{,REF}` with an integer key outside the key's range:
  `DictionaryFixed::integer_key` (`dict.cpp:418`, not quiet) throws range_chk, so the branch of
  `exec_dict_delete` / `exec_dict_deleteget` that would return the dictionary unchanged with 0 is
  never reached; the cases pin the range_chk;
- a new node that does not fit in a cell: the value next to the leaf's label (`dict.cpp:595-653`,
  `698-758`, `809-874`), the edge of a fork merged with its surviving child when a key is deleted
  (`dict.cpp:1182`, `993`), the root of a subdictionary with a longer label (`dict.cpp:1641`): cell_ov,
  after the nodes loaded on the way are charged. Keys are 8 bits; a value of 1017 bits fits under a
  leaf at depth 1 (label of 7 equal bits, 6 bits) and not at the root (label of 8, 7 bits).
-/

namespace Tests.Gen.Dict

open TvmLean

private def iv (n : Int) : Value := .int (.num n)
private def bitsOf (s : String) : BitString := s.toList.toArray.map (· == '1')
private def sl (b : BitString) : Value := .slice (Slice.ofCell (Cell.mkOrdinary b #[]))
private def key (s : String) : Value := sl (bitsOf s)
/-- Values are the code `PUSHINT k` (0x7k), for `PFXDICTGETJMP` / `PFXDICTGETEXEC`. -/
private def val (k : Nat) : Value := sl (natToBits (0x70 + k) 8)

/-- Prefix-free key sets (`n` = 8). -/
private def keySets : Array (String × Array String) :=
  #[ ("code4", #["0", "10", "110", "111"]),
     ("labels", #["0011", "0101", "1"]),
     ("deep", #["10101010", "10101011", "1010100", "0"]),
     ("ones", #["1111", "1110", "110", "0"]) ]

/-- The stack for building the dictionary of `keys` under `below` (values 1, 2, ...), and the
program prefix that builds it: `PUSHNULL`, then `PUSHINT 8; PFXDICTSET; DROP` per key. -/
private def build (keys : Array String) (below : Array Value) : Array Value × Array Instr :=
  let entries := (keys.mapIdx fun i k => #[val (i + 1), key k]).reverse.flatten
  (below ++ entries,
   #[Instr.pushNull] ++ (keys.map fun _ => #[Instr.pushInt (.num 8), .dictExt (.pfxSet .set), .pop 0]).flatten)

/-- Keys looked up or deleted: each key, a non-key, a proper prefix of a key, a key extended
past its leaf, the empty key. -/
private def probes (keys : Array String) : Array String :=
  keys ++ #["01", (keys[0]!).dropRight 1, keys[0]! ++ "1", ""]

private def pfxCases (suite : String) (op : Instr) (extra : String → Array Value) : Array OracleCase :=
  keySets.flatMap fun (sl, keys) =>
    (probes keys).toList.toArray.mapIdx fun j p =>
      let (stack, prog) := build keys (extra p)
      { name := s!"oracle/cov/{sl}/probe{j}", instr := { name := suite }, program := prog ++ #[.pushInt (.num 8), op],
        initStack := stack }

/-- Values whose reference is `d` deep make the new leaf `d + 1` deep: C++ `pfx_dict_set` (dict.cpp)
creates the leaf, the lower part of a split edge, then the forks up to the root, and
`DataCell::create` fails (cell_ov) at the first one deeper than 1024, after charging the cells
created before it. (name, keys, key set, depth of the value's reference): the fork splitting an
edge, the root above a split fork or above a replaced leaf, and paths within the limit. -/
private def pfxDepthCases (suite : String) (op : Instr) : Array OracleCase :=
  let scenarios : Array (String × Array String × String × Nat) :=
    #[("empty-leaf", #[], "0011", 1023), ("split-fork", #["0011"], "0101", 1023),
      ("split-root", #["00", "10"], "01", 1022), ("split-ok", #["00", "10"], "01", 1021),
      ("replace-root", #["00", "10"], "00", 1023), ("replace-ok", #["00", "10"], "00", 1022)]
  scenarios.map fun (name, keys, k, d) =>
    let value : Value := .slice (Slice.ofCell (Cell.mkOrdinary #[] #[Tests.Gen.CellDepth.chain d]))
    let (stack, prog) := build keys #[value, key k]
    { name := s!"oracle/depth/{name}", instr := { name := suite }, program := prog ++ #[.pushInt (.num 8), op],
      initStack := stack }

/-- `DICT{I,U}DEL{GET{,REF}}` with keys out of range (n = 4: signed -8..7, unsigned 0..15):
range_chk from `integer_key`. -/
private def intKeyCases (suite : String) (op : Instr) (unsigned : Bool) : Array OracleCase :=
  let dict : Value :=
    match dictSetSliceWithCells none (natToBits 3 4) (Slice.ofCell (Cell.mkOrdinary (natToBits 5 8) #[])) .set with
    | .ok (some r, _, _, _) => .cell r
    | _ => .null
  let keys : Array Int := if unsigned then #[16, -1, 2 ^ 256 - 1, 3] else #[8, -9, 2 ^ 200, 3]
  keys.flatMap fun k =>
    #[dict, .null].mapIdx fun i d =>
      { name := s!"oracle/cov/int-key/{k}/dict{i}", instr := { name := suite }, program := #[op],
        initStack := #[iv k, d, iv 4] }

private def zeros (n : Nat) : Value := .slice (Slice.ofCell (Cell.mkOrdinary (Array.replicate n false) #[]))

/-- A case running `prog` on the dictionary with `entries` (value, 8-bit unsigned key), built by
`DICTUSET`s from `null`; `top` is below the entries. -/
private def onDict (suite name : String) (entries : Array (Value × Int)) (prog : Array Instr)
    (top : Array Value := #[]) : OracleCase :=
  { name := s!"oracle/overflow/{name}", instr := { name := suite },
    codeCell? := some (Tests.Gen.Control.codeOf
      (#[Instr.pushNull] ++ (entries.map fun _ => #[Instr.pushInt (.num 8), .dictSet true true false .set]).flatten ++ prog)),
    initStack := top ++ (entries.reverse.map fun (v, k) => #[v, iv k]).flatten }

/-- The same with a prefix-code dictionary (`PFXDICTSET`, keys as bit strings). -/
private def onPfxDict (suite name : String) (entries : Array (Value × String)) (prog : Array Instr)
    (top : Array Value := #[]) : OracleCase :=
  { name := s!"oracle/overflow/{name}", instr := { name := suite },
    codeCell? := some (Tests.Gen.Control.codeOf
      (#[Instr.pushNull] ++ (entries.map fun _ => #[Instr.pushInt (.num 8), .dictExt (.pfxSet .set), .pop 0]).flatten ++ prog)),
    initStack := top ++ (entries.reverse.map fun (v, k) => #[v, key k]).flatten }

/-- `x` pushed below the dictionary on the top of the stack, then `n` = 8 and `op`. -/
private def withKey (x : Instr) (op : Instr) : Array Instr := #[x, .xchg0 1, .pushInt (.num 8), op]

private def pushKey (k : String) : Instr := .pushSliceConst (Slice.ofCell (Cell.mkOrdinary (bitsOf k) #[]))

/-- Each scenario with a value that fits and one bit more. -/
private def sizes (base : Nat) (f : Nat → OracleCase) : Array OracleCase := #[f base, f (base + 1)]

/-- The cases of a new node that does not fit, for the suite named `suite` (attached to every suite by
`Tests.suiteOracleCases`). -/
def overflowCasesFor (suite : String) : Array OracleCase :=
  let set : Instr := .dictSet true true false .set
  let setget : Instr := .dictExt (.mutGet true true false .set)
  let del : Instr := .dictExt (.del true true)
  let delget : Instr := .dictExt (.mutGet true true false .del)
  -- 0x80 and 0x00 differ in the first bit (fork at the root); 0x80, 0x08, 0x00: fork at depth 1
  -- with label 000, leaves at depth 5
  match suite with
  | "DICTUSET" =>
      sizes 1016 (fun n => onDict suite s!"empty-{n}" #[] #[] |> fun c =>
        { c with codeCell? := some (Tests.Gen.Control.codeOf #[set]), initStack := #[zeros n, iv 0, .null, iv 8] }) ++
      sizes 1016 (fun n => onDict suite s!"replace-root-{n}" #[(zeros 8, 0), (zeros n, 0)] #[]) ++
      sizes 1017 (fun n => onDict suite s!"split-{n}" #[(zeros 8, 128), (zeros n, 0)] #[]) ++
      sizes 1017 (fun n => onDict suite s!"replace-depth1-{n}" #[(zeros 8, 128), (zeros 8, 0), (zeros n, 0)] #[])
  | "DICTUSETGET" =>
      sizes 1016 (fun n => onDict suite s!"replace-root-{n}" #[(zeros 8, 0)] (withKey (.pushInt (.num 0)) setget) #[zeros n]) ++
      sizes 1017 (fun n => onDict suite s!"split-{n}" #[(zeros 8, 128)] (withKey (.pushInt (.num 0)) setget) #[zeros n])
  | "DICTUSETB" =>
      sizes 1016 fun n =>
        { name := s!"oracle/overflow/empty-{n}", instr := { name := suite }, program := #[.dictSetB true true .set],
          initStack := #[.builder { bits := Array.replicate n false, refs := #[] }, iv 0, .null, iv 8] }
  | "DICTUDEL" =>
      sizes 1016 (fun n => onDict suite s!"merge-root-{n}" #[(zeros 8, 128), (zeros n, 0)] (withKey (.pushInt (.num 128)) del)) ++
      sizes 1017 (fun n => onDict suite s!"merge-depth1-{n}" #[(zeros 8, 128), (zeros 8, 8), (zeros n, 0)] (withKey (.pushInt (.num 8)) del))
  | "DICTUDELGET" =>
      sizes 1017 (fun n => onDict suite s!"merge-depth1-{n}" #[(zeros 8, 128), (zeros 8, 8), (zeros n, 0)] (withKey (.pushInt (.num 8)) delget))
  | "DICTUREMMIN" =>
      -- the minimum (0x00) is removed, its sibling 0x08 merged into the fork's edge: label 0001000
      -- of 7 bits, 12 bits long
      sizes 1011 (fun n => onDict suite s!"merge-depth1-{n}" #[(zeros 8, 128), (zeros 8, 0), (zeros n, 8)] #[.pushInt (.num 8), .dictGetMinMax 22])
  | "DICTUSETGETOPTREF" =>
      -- a null value deletes the key
      sizes 1017 (fun n => onDict suite s!"delete-merge-depth1-{n}" #[(zeros 8, 128), (zeros 8, 8), (zeros n, 0)]
        (#[.pushNull, .xchg0 1] ++ withKey (.pushInt (.num 8)) (.dictExt (.setGetOptRef true true))))
  | "SUBDICTUGET" =>
      let sub : Instr := .dictExt (.subdictGet true true false)
      sizes 1016 (fun n => onDict suite s!"root-{n}" #[(zeros 8, 128), (zeros n, 0)]
        #[.pushInt (.num 0), .xchg0 1, .pushInt (.num 1), .xchg0 1, .pushInt (.num 8), sub]) ++
      sizes 1016 (fun n => onDict suite s!"depth1-{n}" #[(zeros 8, 128), (zeros 8, 64), (zeros n, 0)]
        #[.pushInt (.num 0), .xchg0 1, .pushInt (.num 2), .xchg0 1, .pushInt (.num 8), sub])
  | "PFXDICTSET" =>
      let pset : Instr := .dictExt (.pfxSet .set)
      sizes 1018 (fun n => onPfxDict suite s!"empty-{n}" #[] (withKey (pushKey "0") pset) #[zeros n]) ++
      sizes 1020 (fun n => onPfxDict suite s!"split-{n}" #[(zeros 8, "1")] (withKey (pushKey "0") pset) #[zeros n]) ++
      sizes 1018 (fun n => onPfxDict suite s!"replace-depth1-{n}" #[(zeros 8, "1"), (zeros 8, "00")] (withKey (pushKey "00") pset) #[zeros n])
  | "PFXDICTDEL" =>
      let pdel : Instr := .dictExt .pfxDel
      sizes 1016 (fun n => onPfxDict suite s!"merge-root-{n}" #[(zeros 8, "1"), (zeros n, "00")] (withKey (pushKey "1") pdel)) ++
      sizes 1016 (fun n => onPfxDict suite s!"merge-depth1-{n}" #[(zeros 8, "1"), (zeros 8, "01"), (zeros n, "000")] (withKey (pushKey "01") pdel))
  | _ => #[]

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "PFXDICTDEL" => pfxCases suite (.dictExt .pfxDel) (fun p => #[key p])
  | "PFXDICTGET" => pfxCases suite (.dictExt (.pfxGet .get)) (fun p => #[key p])
  | "PFXDICTGETQ" => pfxCases suite (.dictExt (.pfxGet .getQ)) (fun p => #[key p])
  | "PFXDICTGETJMP" => pfxCases suite (.dictExt (.pfxGet .getJmp)) (fun p => #[key p])
  | "PFXDICTGETEXEC" => pfxCases suite (.dictExt (.pfxGet .getExec)) (fun p => #[key p])
  | "PFXDICTSET" => pfxCases suite (.dictExt (.pfxSet .set)) (fun p => #[val 9, key p]) ++
      pfxDepthCases suite (.dictExt (.pfxSet .set))
  | "PFXDICTADD" => pfxCases suite (.dictExt (.pfxSet .add)) (fun p => #[val 9, key p]) ++
      pfxDepthCases suite (.dictExt (.pfxSet .add))
  | "PFXDICTREPLACE" => pfxCases suite (.dictExt (.pfxSet .replace)) (fun p => #[val 9, key p]) ++
      pfxDepthCases suite (.dictExt (.pfxSet .replace))
  | "DICTIDEL" => intKeyCases suite (.dictExt (.del true false)) false
  | "DICTUDEL" => intKeyCases suite (.dictExt (.del true true)) true
  | "DICTIDELGET" => intKeyCases suite (.dictExt (.mutGet true false false .del)) false
  | "DICTUDELGET" => intKeyCases suite (.dictExt (.mutGet true true false .del)) true
  | "DICTIDELGETREF" => intKeyCases suite (.dictExt (.mutGet true false true .del)) false
  | "DICTUDELGETREF" => intKeyCases suite (.dictExt (.mutGet true true true .del)) true
  | _ => #[]

end Tests.Gen.Dict

import Tests.Harness.Registry
import Tests.Harness.Gen.CellDepth

/-!
Oracle cases for dictionary paths the full coverage run of 2026-10-19 did not reach
(`crypto/vm/dict.cpp`, `dictops.cpp`):

- prefix-code dictionaries with several entries: `pfx_dict_set` and `pfx_dict_lookup_delete`
  through fork nodes (insertion splitting an edge or going down a fork, deletion merging the
  remaining child into its parent edge), lookups of keys, of non-keys, of proper prefixes of keys
  and of keys extended past a leaf. The dictionary is built in the program by chained
  `PFXDICTSET`s from `null`, then the instruction under test runs on it;
- `DICT{I,U}DEL`, `DICT{I,U}DELGET{,REF}` with an integer key outside the key's range: the
  dictionary is returned unchanged with 0 (`exec_dict_delete`, `exec_dict_deleteget`).
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

/-- `DICT{I,U}DEL{GET{,REF}}` with keys out of range (n = 4: signed -8..7, unsigned 0..15). -/
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

import Tests.Harness.Registry
import Tests.Harness.Gen.Control

/-!
Oracle cases that run the opcode a suite is named after. A check of every suite's oracle code
against the opcode prefix of its specification row found 27 suites that never ran it: written while
the assembler rejected the form, they ran a neighbour instead (`PUSHINT n; PLDIX` for `PLDI n`,
`PUSHINT z; MULRSHIFTC` for `MULRSHIFTC# z`, the var forms for `LSHIFT`/`RSHIFT` and the reverse for
`RSHIFTMODC`, the short `LDU` for `LDU_ALT`, `STREF` for `STREF_ALT`, `CALLXARGS p,-1` for
`CALLXARGS p,r`, other dictionary opcodes for `DICTISETGET` & co.). Both C++ forms share their
`exec_*` function, so the C++ function coverage did not show it.

Each case runs a raw code cell: an optional assembled prefix, then the opcode's bits exactly as the
C++ dispatch table reads them (`crypto/vm/{cellops,arithops,contops,dictops}.cpp`).
-/

namespace Tests.Gen.OwnOpcode

open TvmLean

private def iv (n : Int) : Value := .int (.num n)
private def bitsOf (s : String) : BitString := s.toList.toArray.map (· == '1')

/-- Code: `pre` encoded (`Tests.Gen.Control.codeOf`), then `raw`. -/
private def codeWith (pre : Array Instr) (raw : BitString) : Cell :=
  let c := Tests.Gen.Control.codeOf pre
  Cell.mkOrdinary (c.bits ++ raw) c.refs

private def mk (suite name : String) (code : Cell) (stack : Array Value) : OracleCase :=
  { name := s!"oracle/own-opcode/{name}", instr := { name := suite }, codeCell? := some code, initStack := stack }

/-! ### Fixed-width loads (`exec_load_int_fixed{,2}`, `exec_load_slice_fixed`) -/

/-- A slice of `n` bits (alternating from `start`) and `refs` empty references. -/
private def bitsSlice (n : Nat) (start : Bool) (refs : Nat := 0) : Value :=
  .slice (Slice.ofCell (Cell.mkOrdinary ((Array.range n).map (fun i => (i % 2 == 0) == start))
    (Array.replicate refs Cell.empty)))

/-- `raw b` loads `b` bits: slices of exactly `b` bits, longer with references, one bit short; and
the stack errors. -/
private def loadCases (suite : String) (raw : Nat → BitString) : Array OracleCase :=
  let widths : Array Nat := #[1, 8, 57, 255, 256]
  (widths.flatMap fun b =>
    #[mk suite s!"b{b}/exact-1" (codeWith #[] (raw b)) #[bitsSlice b true],
      mk suite s!"b{b}/exact-0" (codeWith #[] (raw b)) #[bitsSlice b false],
      mk suite s!"b{b}/longer-refs" (codeWith #[] (raw b)) #[iv 5, bitsSlice (b + 9) true 2],
      mk suite s!"b{b}/short" (codeWith #[] (raw b)) #[bitsSlice (b - 1) true 1]]) ++
  #[mk suite "underflow" (codeWith #[] (raw 8)) #[],
    mk suite "type-null" (codeWith #[] (raw 8)) #[.null],
    mk suite "type-int" (codeWith #[] (raw 8)) #[iv 3],
    mk suite "type-cell" (codeWith #[] (raw 8)) #[.cell Cell.empty]]

/-- `0xd708 >> 3` (13 bits), the flags (unsigned 1, prefetch 2, quiet 4), the width less one. -/
private def ldFixed2 (flags : Nat) (b : Nat) : BitString := natToBits ((0xd708 >>> 3 <<< 3) ||| flags) 16 ++ natToBits (b - 1) 8

/-! ### Multiply-shift with an immediate shift (`exec_mulshrmod`, `0xa9b0..0xa9bf` + tt) -/

private def mulShiftPairs : Array (Int × Int) :=
  #[(7, 3), (-7, 3), (7, -3), (-7, -3), (0, 5), (1, 1), (2 ^ 200, 2 ^ 100), (-(2 ^ 255), 3), (2 ^ 255 - 1, 2 ^ 255 - 1),
    (-(2 ^ 256), -(2 ^ 256))]

private def mulShiftCases (suite : String) (op : Nat) : Array OracleCase :=
  (#[1, 8, 255, 256].flatMap fun z =>
    mulShiftPairs.mapIdx fun i (x, y) =>
      mk suite s!"z{z}/pair{i}" (codeWith #[] (natToBits op 16 ++ natToBits (z - 1) 8)) #[iv x, iv y]) ++
  #[mk suite "underflow" (codeWith #[] (natToBits op 16 ++ natToBits 7 8)) #[iv 3],
    mk suite "type-null" (codeWith #[] (natToBits op 16 ++ natToBits 7 8)) #[iv 3, .null],
    mk suite "type-null-below" (codeWith #[] (natToBits op 16 ++ natToBits 7 8)) #[.null, iv 3]]

/-! ### Shifts: `RSHIFTMODC` (shift on the stack), `LSHIFT`/`RSHIFT` (immediate) -/

private def shiftValues : Array Int := #[7, -7, 0, 1, -1, 2 ^ 255 - 1, -(2 ^ 256), 2 ^ 200]

private def rshiftModCCases (suite : String) : Array OracleCase :=
  (#[0, 1, 7, 255, 256, 257, -1, 1023, 1024].flatMap fun z =>
    shiftValues.mapIdx fun i x => mk suite s!"z{z}/x{i}" (codeWith #[] (natToBits 0xa92e 16)) #[iv x, iv z]) ++
  #[mk suite "underflow" (codeWith #[] (natToBits 0xa92e 16)) #[iv 3],
    mk suite "type-null" (codeWith #[] (natToBits 0xa92e 16)) #[iv 3, .null]]

private def shiftConstCases (suite : String) (op : Nat) : Array OracleCase :=
  (#[0, 7, 254, 255].flatMap fun cc =>
    shiftValues.mapIdx fun i x => mk suite s!"cc{cc}/x{i}" (codeWith #[] (natToBits op 8 ++ natToBits cc 8)) #[iv x]) ++
  #[mk suite "underflow" (codeWith #[] (natToBits op 8 ++ natToBits 3 8)) #[],
    mk suite "type-null" (codeWith #[] (natToBits op 8 ++ natToBits 3 8)) #[.null]]

/-! ### `STREF_ALT` (0xcf10), `STSLICE_ALT` (0xcf12) -/

private def fullRefs : Value := .builder { bits := #[], refs := Array.replicate 4 Cell.empty }
private def fullBits : Value := .builder { bits := Array.replicate 1023 true, refs := #[] }

private def storeAltCases (suite : String) (op : Nat) (item : Value) (big : Value) : Array OracleCase :=
  let code := codeWith #[] (natToBits op 16)
  #[mk suite "ok-empty" code #[item, .builder Builder.empty],
    mk suite "ok-bits" code #[item, .builder { bits := Array.replicate 100 false, refs := #[Cell.empty] }],
    mk suite "full-refs" code #[item, fullRefs],
    mk suite "full-bits" code #[item, fullBits],
    mk suite "big-item" code #[big, .builder { bits := Array.replicate 10 true, refs := #[] }],
    mk suite "swapped" code #[.builder Builder.empty, item],
    mk suite "type-null" code #[.null, .builder Builder.empty],
    mk suite "underflow" code #[.builder Builder.empty]]

/-! ### `CALLXARGS p,r` (0xda + p + r) -/

private def callxArgsCases (suite : String) : Array OracleCase :=
  let body (b : Array Instr) : Instr := .pushCont (Slice.ofCell (Tests.Gen.Control.codeOf b))
  let call (p r : Nat) : BitString := natToBits 0xda 8 ++ natToBits p 4 ++ natToBits r 4
  #[mk suite "add-2-1" (codeWith #[body #[.add]] (call 2 1)) #[iv 1, iv 2, iv 3],
    mk suite "add-2-0" (codeWith #[body #[.add]] (call 2 0)) #[iv 1, iv 2, iv 3],
    mk suite "push3-0-3" (codeWith #[body #[.pushInt (.num 1), .pushInt (.num 2), .pushInt (.num 3)]] (call 0 3)) #[iv 9],
    mk suite "push3-0-2" (codeWith #[body #[.pushInt (.num 1), .pushInt (.num 2), .pushInt (.num 3)]] (call 0 2)) #[iv 9],
    mk suite "returns-too-few" (codeWith #[body #[.pop 0]] (call 1 2)) #[iv 1, iv 2],
    mk suite "params-too-many" (codeWith #[body #[]] (call 3 0)) #[iv 1],
    mk suite "p15-r0" (codeWith #[body #[.blkdrop 15]] (call 15 0))
      ((Array.range 16).map fun i => iv (Int.ofNat i)),
    mk suite "not-cont" (codeWith #[] (call 0 0)) #[iv 1, iv 2]]

/-! ### Dictionary opcodes (`dictops.cpp`) -/

/-- A dictionary with 4-bit keys `keys`, each value a reference to a cell holding the key (a valid
value for the `REF` variants too). -/
private def dictOf (keys : Array String) : Value :=
  let root := keys.foldl (fun root k =>
    match dictSetRefWithCells root (bitsOf k) (Cell.mkOrdinary (natToBits (bitsToNat (bitsOf k)) 8) #[]) .set with
    | .ok (some r, _, _, _) => some r
    | _ => root) none
  match root with
  | some r => .cell r
  | none => .null

private def dicts : Array (String × Value) :=
  #[("empty", dictOf #[]), ("one", dictOf #["0101"]), ("spread", dictOf #["0000", "0011", "0110", "1001", "1111"])]

private def sliceKey (k : String) : Value := .slice (Slice.ofCell (Cell.mkOrdinary (bitsOf k) #[]))

/-- `DICTGETPREV` (slice key), `DICTIGETPREVEQ` (signed key): (k D n -- x' k' -1 | 0). -/
private def getNearCases (suite : String) (op : Nat) (intKey : Bool) : Array OracleCase :=
  let code := codeWith #[] (natToBits op 16)
  let keys : Array Value :=
    if intKey then #[iv 0, iv 3, iv (-1), iv (-8), iv 7, iv 8, iv (-9), iv 6]
    else #[sliceKey "0000", sliceKey "0011", sliceKey "0100", sliceKey "1111", sliceKey "1000", sliceKey "001"]
  (dicts.flatMap fun (dn, d) => keys.mapIdx fun i k => mk suite s!"{dn}/key{i}" code #[k, d, iv 4]) ++
  #[mk suite "n0" code #[keys[0]!, (dicts[2]!).2, iv 0], mk suite "n-big" code #[keys[0]!, (dicts[2]!).2, iv 1024],
    mk suite "underflow" code #[keys[0]!, (dicts[2]!).2], mk suite "type-dict" code #[keys[0]!, iv 1, iv 4]]

/-- `DICTISETGET`, `DICTUSETGET` (slice value), `DICTISETGETREF` (cell value): (x i D n -- D' y -1 | D' 0). -/
private def setGetCases (suite : String) (op : Nat) (unsigned byRef : Bool) : Array OracleCase :=
  let code := codeWith #[] (natToBits op 16)
  let value : Value :=
    if byRef then .cell (Cell.mkOrdinary (natToBits 0xab 8) #[]) else .slice (Slice.ofCell (Cell.mkOrdinary (natToBits 0xcd 8) #[]))
  let keys : Array Int := if unsigned then #[0, 5, 9, 15, 16, -1] else #[0, 5, -7, 7, -8, 8, -9]
  (dicts.flatMap fun (dn, d) => keys.map fun k => mk suite s!"{dn}/key{k}" code #[value, iv k, d, iv 4]) ++
  #[mk suite "value-type" code #[(if byRef then .slice (Slice.ofCell Cell.empty) else .cell Cell.empty), iv 5, (dicts[2]!).2, iv 4],
    mk suite "underflow" code #[iv 5, (dicts[2]!).2, iv 4], mk suite "n-big" code #[value, iv 5, (dicts[2]!).2, iv 1024]]

/-! ### Opcodes most of whose suite runs a neighbour (`--opcode-check` finds them in few cases) -/

/-- A dictionary with 4-bit keys whose values are code: `PUSHINT k` for key `k` (signed). -/
private def codeDict (keys : Array Int) : Value :=
  let root := keys.foldl (fun root k =>
    let bits := natToBits ((k + 16).toNat % 16) 4
    match dictSetSliceWithCells root bits (Slice.ofCell (Cell.mkOrdinary (natToBits (0x70 + ((k + 16).toNat % 16)) 8) #[])) .set with
    | .ok (some r, _, _, _) => some r
    | _ => root) none
  match root with
  | some r => .cell r
  | none => .null

/-- `DICTIGETEXEC` / `DICTUGETEXEC` (i D n -- ): the value runs as a continuation (`PUSHINT`). -/
private def getExecCases (suite : String) (op : Nat) (unsigned : Bool) : Array OracleCase :=
  let code := codeWith #[] (natToBits op 16)
  let d := codeDict (if unsigned then #[0, 3, 9, 15] else #[0, 3, -7, -1])
  let keys : Array Int := if unsigned then #[0, 3, 9, 15, 4, 16, -1] else #[0, 3, -7, -1, 4, 8, -9]
  (keys.map fun k => mk suite s!"key{k}" code #[iv 42, iv k, d, iv 4]) ++
  #[mk suite "empty" code #[iv 3, .null, iv 4], mk suite "underflow" code #[d, iv 4],
    mk suite "type-key" code #[.null, d, iv 4], mk suite "n-big" code #[iv 3, d, iv 1024]]

/-- `DICTIMIN` (D n -- x i -1 | 0): the least signed key. -/
private def dictIMinCases (suite : String) : Array OracleCase :=
  let code := codeWith #[] (natToBits 0xf484 16)
  (dicts.map fun (dn, d) => mk suite dn code #[d, iv 4]) ++
  #[mk suite "negatives" code #[(match dictSetRefWithCells none (natToBits 9 4) Cell.empty .set with
        | .ok (some r, _, _, _) => .cell r | _ => .null), iv 4],
    mk suite "n0" code #[(dicts[2]!).2, iv 0], mk suite "underflow" code #[(dicts[2]!).2], mk suite "type" code #[iv 1, iv 4]]

/-- `DICTSETREF` (c k D n -- D'): slice key, the value a reference. -/
private def dictSetRefCases (suite : String) : Array OracleCase :=
  let code := codeWith #[] (natToBits 0xf413 16)
  let c : Value := .cell (Cell.mkOrdinary (natToBits 0xee 8) #[])
  (dicts.flatMap fun (dn, d) =>
    #["0101", "0000", "1110", "011"].map fun k => mk suite s!"{dn}/key{k}" code #[c, sliceKey k, d, iv 4]) ++
  #[mk suite "value-slice" code #[.slice (Slice.ofCell Cell.empty), sliceKey "0101", (dicts[2]!).2, iv 4],
    mk suite "underflow" code #[sliceKey "0101", (dicts[2]!).2, iv 4]]

/-- `PLDDICT` (s -- D), `LDDICTQ` (s -- D s' -1 | s 0): a `Maybe ^Cell`. -/
private def loadDictCases (suite : String) (op : Nat) : Array OracleCase :=
  let code := codeWith #[] (natToBits op 16)
  let sl (bits : BitString) (refs : Array Cell) : Value := .slice (Slice.ofCell (Cell.mkOrdinary bits refs))
  #[mk suite "nothing" code #[sl #[false] #[]], mk suite "nothing-tail" code #[sl #[false, true] #[Cell.empty]],
    mk suite "just" code #[sl #[true] #[Cell.empty]], mk suite "just-tail" code #[sl #[true, false, true] #[Cell.empty, Cell.empty]],
    mk suite "just-no-ref" code #[sl #[true] #[]], mk suite "empty" code #[sl #[] #[]], mk suite "refs-only" code #[sl #[] #[Cell.empty]],
    mk suite "type" code #[iv 1], mk suite "underflow" code #[]]

/-- `THROW n` in its long form (`0xf2c4_` + 11 bits), n from 0 to 2047: uncaught, and inside
`TRY` with an empty handler (the handler gets the stack `[n, n]`). -/
private def throwLongCases (suite : String) : Array OracleCase :=
  let raw (n : Nat) : BitString := natToBits (0xf2c0 >>> 3) 13 ++ natToBits n 11
  #[0, 1, 2, 63, 64, 100, 1000, 2047].flatMap fun n =>
    #[mk suite s!"n{n}" (codeWith #[] (raw n)) #[iv 5],
      mk suite s!"n{n}/try"
        (codeWith #[.pushCont (Slice.ofCell (Cell.mkOrdinary (raw n) #[])),
          .pushCont (Slice.ofCell (Tests.Gen.Control.codeOf #[])), .try_] #[]) #[iv 5]]

/-- `XCHG3 s(i),s(j),s(k)` in its long form (`0x540ijk`). -/
private def xchg3AltCases (suite : String) : Array OracleCase :=
  let stack := (Array.range 16).map fun i => iv (Int.ofNat (100 + i))
  #[(1, 2, 3), (0, 0, 0), (15, 14, 13), (3, 3, 3), (0, 15, 7), (2, 1, 0)].flatMap fun (i, j, k) =>
    #[mk suite s!"i{i}j{j}k{k}" (codeWith #[] (natToBits 0x540 12 ++ natToBits i 4 ++ natToBits j 4 ++ natToBits k 4)) stack,
      mk suite s!"i{i}j{j}k{k}/short" (codeWith #[] (natToBits 0x540 12 ++ natToBits i 4 ++ natToBits j 4 ++ natToBits k 4))
        (stack.extract 0 (Nat.max i (Nat.max j k)))]

/-- `CALLXARGS p,-1` (`0xdb0p`): every result returned. -/
private def callxArgsAllCases (suite : String) : Array OracleCase :=
  let body (b : Array Instr) : Instr := .pushCont (Slice.ofCell (Tests.Gen.Control.codeOf b))
  let call (p : Nat) : BitString := natToBits 0xdb0 12 ++ natToBits p 4
  #[mk suite "p2-add" (codeWith #[body #[.add]] (call 2)) #[iv 1, iv 2, iv 3],
    mk suite "p0-push3" (codeWith #[body #[.pushInt (.num 1), .pushInt (.num 2), .pushInt (.num 3)]] (call 0)) #[iv 9],
    mk suite "p1-drop" (codeWith #[body #[.pop 0]] (call 1)) #[iv 7, iv 8],
    mk suite "p3-short" (codeWith #[body #[]] (call 3)) #[iv 1, iv 2],
    mk suite "p15" (codeWith #[body #[.blkdrop 14]] (call 15)) ((Array.range 16).map fun i => iv (Int.ofNat i)),
    mk suite "not-cont" (codeWith #[] (call 1)) #[iv 1, iv 2]]

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "LDI" => loadCases suite fun b => natToBits 0xd2 8 ++ natToBits (b - 1) 8
  | "LDSLICE" => loadCases suite fun b => natToBits 0xd6 8 ++ natToBits (b - 1) 8
  | "LDI_ALT" => loadCases suite (ldFixed2 0)
  | "LDU_ALT" => loadCases suite (ldFixed2 1)
  | "PLDI" => loadCases suite (ldFixed2 2)
  | "PLDU" => loadCases suite (ldFixed2 3)
  | "LDIQ" => loadCases suite (ldFixed2 4)
  | "LDUQ" => loadCases suite (ldFixed2 5)
  | "PLDIQ" => loadCases suite (ldFixed2 6)
  | "PLDUQ" => loadCases suite (ldFixed2 7)
  | "MULRSHIFTR#" => mulShiftCases suite 0xa9b5
  | "MULRSHIFTC#" => mulShiftCases suite 0xa9b6
  | "MULMODPOW2R#" => mulShiftCases suite 0xa9b9
  | "MULMODPOW2C#" => mulShiftCases suite 0xa9ba
  | "MULRSHIFTR#MOD" => mulShiftCases suite 0xa9bd
  | "MULRSHIFTC#MOD" => mulShiftCases suite 0xa9be
  | "RSHIFTMODC" => rshiftModCCases suite
  | "LSHIFT" => shiftConstCases suite 0xaa
  | "RSHIFT" => shiftConstCases suite 0xab
  | "STREF_ALT" => storeAltCases suite 0xcf10 (.cell Cell.empty) (.cell (Cell.mkOrdinary #[] #[Cell.empty]))
  | "STSLICE_ALT" =>
      storeAltCases suite 0xcf12 (.slice (Slice.ofCell (Cell.mkOrdinary (natToBits 5 3) #[Cell.empty])))
        (.slice (Slice.ofCell (Cell.mkOrdinary (Array.replicate 1020 false) #[])))
  | "CALLXARGS_1" => callxArgsCases suite
  | "DICTGETPREV" => getNearCases suite 0xf476 false
  | "DICTIGETPREVEQ" => getNearCases suite 0xf47b true
  | "DICTISETGET" => setGetCases suite 0xf41c false false
  | "DICTISETGETREF" => setGetCases suite 0xf41d false true
  | "DICTUSETGET" => setGetCases suite 0xf41e true false
  | "DICTIGETEXEC" => getExecCases suite 0xf4a2 false
  | "DICTUGETEXEC" => getExecCases suite 0xf4a3 true
  | "DICTIMIN" => dictIMinCases suite
  | "DICTSETREF" => dictSetRefCases suite
  | "PLDDICT" => loadDictCases suite 0xf405
  | "LDDICTQ" => loadDictCases suite 0xf406
  | "THROW" => throwLongCases suite
  | "XCHG3_ALT" => xchg3AltCases suite
  | "CALLXARGS" => callxArgsAllCases suite
  | _ => #[]

end Tests.Gen.OwnOpcode

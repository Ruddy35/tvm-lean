import Tests.Harness.Registry
import Tests.Harness.Gen.Control

/-!
Oracle cases for the branches of C++ on the global version (`docs/audit/cpp-global-version.csv`)
that the suites' own cases do not reach. Every case runs on every version: on one side of the
threshold it takes one branch, on the other side the other.

- The stack operations with a count from the stack (`PICK`, `ROLL`, `ROLLREV`, `BLKSWX`, `REVX`,
  `DROPX`, `XCHGX`, `CHKDEPTH`, `ONLYTOPX`, `ONLYX`) pop it with `pop_smallint_range` up to
  `2^30 - 1` from version 4, up to 255 before (stackops.cpp:404-530): a count of 256 on a deep
  stack works (and charges the entries over 255) or is range_chk; on a short stack it is stk_und or
  range_chk. `BLKSWX` charges the entries over 255 only from version 4 (stackops.cpp:443).
- `HASHEXT` with the hash id from the stack checks for two entries before popping it from version
  9 only (tonops.cpp:688): a single `null` is stk_und or type_chk.
- Before version 13 the shifts, `AND`, `OR` and the `MULRSHIFT` and `LSHIFTDIV` families compute
  with a NaN operand as C++ BigInts (arithops.cpp:542-562, 655-673, 814-889): NaN shifted by whole
  52-bit words becomes 0, shifted right by more than 12 bits -1 (rounding down) or 0, `AND` with 0
  is 0, `OR` with -1 is -1; the quiet forms are range_chk on a bad shift. From version 13 the result
  is NaN. The cases put NaN on each side of these bounds.
- Before version 10 a message address may be `addr_var$11` and have an anycast
  (`depth:(#<= 30) rewrite_pfx:(bits depth)`, `depth >= 1`), which `LDMSGADDR`, `PARSEMSGADDR` and
  the `REWRITE*ADDR` instructions accept (tonops.cpp:1608-1814); `REWRITEVARADDR` builds a new cell
  for an address whose anycast prefix is shorter than it (tonops.cpp:1837-1853). The cases give
  standard and variable addresses with anycasts of valid and invalid depths.
-/

namespace Tests.Gen.Versions

open TvmLean

private def pi (n : Int) : Instr := .pushInt (.num n)

private def mk (suite name : String) (prog : Array Instr) (stack : Array Value := #[]) : OracleCase :=
  { name := s!"oracle/versions/{name}", instr := { name := suite },
    codeCell? := some (Tests.Gen.Control.codeOf prog), initStack := stack }

/-- 301 copies of 7 on the stack. -/
private def deepStack : Array Instr :=
  #[pi 7] ++ (List.replicate 20 (Instr.blkPush 15 0)).toArray

/-- The cases of a stack operation `op` with `counts` pushed before it: on a stack of 301 entries
and on the stack `[1, 2]`. -/
private def countCases (suite : String) (op : Instr) (counts : List (String × Array Int)) : Array OracleCase :=
  (counts.toArray.flatMap fun (nm, ns) =>
    #[mk suite s!"count-{nm}/deep" (deepStack ++ ns.map pi ++ #[op]),
      mk suite s!"count-{nm}/short" (#[pi 1, pi 2] ++ ns.map pi ++ #[op])])

private def oneCount : List (String × Array Int) := [("255", #[255]), ("256", #[256])]

private def twoCounts : List (String × Array Int) :=
  [("255-1", #[255, 1]), ("256-1", #[256, 1]), ("1-256", #[1, 256]), ("200-100", #[200, 100])]

private def nan : Instr := .pushInt .nan

/-- `op` run after `args` (pushed in order, NaN as `PUSHNAN`); `nm` names the case. -/
private def opCases (suite : String) (op : Instr) (cs : List (String × Array (Option Int))) : Array OracleCase :=
  cs.toArray.map fun (nm, args) =>
    mk suite s!"nan-bigint/{nm}" (args.map (fun a => match a with | some n => pi n | none => nan) ++ #[op])

private def shiftCases (suite : String) (op : Instr) (shifts : List Int) : Array OracleCase :=
  opCases suite op (shifts.map fun sh => (s!"nan-shift{sh}", #[none, some sh]))

private def logicCases (suite : String) (op : Instr) : Array OracleCase :=
  opCases suite op
    [("nan-0", #[none, some 0]), ("0-nan", #[some 0, none]), ("nan-m1", #[none, some (-1)]),
     ("m1-nan", #[some (-1), none]), ("nan-5", #[none, some 5])]

/-- `x y z` for `MULRSHIFT` (`z` the shift) with `x` NaN. -/
private def mulShrCases (suite : String) (op : Instr) : Array OracleCase :=
  opCases suite op
    [("x-nan-shift5", #[none, some 3, some 5]), ("x-nan-shift20", #[none, some 3, some 20]),
     ("y-nan-shift0", #[some 3, none, some 0]), ("bad-shift", #[some 3, some 3, some 300])]

/-- `x z y` for `LSHIFTDIV` (`z` the divisor, `y` the shift) with `x` NaN. -/
private def shlDivCases (suite : String) (op : Instr) (add : Bool) : Array OracleCase :=
  let w : Array (Option Int) := if add then #[some 10] else #[]
  opCases suite op
    [("x-nan-shift51", #[none] ++ w ++ #[some 3, some 51]), ("x-nan-shift52", #[none] ++ w ++ #[some 3, some 52]),
     ("x-nan-shift52-div0", #[none] ++ w ++ #[some 0, some 52]),
     ("x-nan-shift52-div-nan", #[none] ++ w ++ #[none, some 52]),
     ("bad-shift", #[some 1] ++ w ++ #[some 3, some 300])]

/-- `addr_std$10` or `addr_var$11` with the anycast `pfx` (its depth, `none` for `nothing$0`),
workchain `wc` (8 or 32 bits) and address bits `addr` (256 bits for `addr_std`). -/
private def msgAddr (var : Bool) (pfx : Option (Nat × Nat)) (wc : Int) (addr : BitString) : Value :=
  let anycast : BitString :=
    match pfx with
    | none => #[false]
    | some (depth, bits) => #[true] ++ natToBits depth 5 ++ natToBits bits depth
  let wcBits : BitString :=
    match intToBitsTwos wc (if var then 32 else 8) with
    | .ok b => b
    | .error _ => #[]
  let body : BitString :=
    if var then natToBits 0b11 2 ++ anycast ++ natToBits addr.size 9 ++ wcBits ++ addr
    else natToBits 0b10 2 ++ anycast ++ wcBits ++ addr
  .slice (Slice.ofCell (Cell.mkOrdinary body #[]))

private def addrBits (n seed : Nat) : BitString := natToBits ((seed * 0x9e3779b97f4a7c15) % (2 ^ n)) n

/-- Addresses of every kind the versions before 10 tell apart. -/
private def anycastAddrs : List (String × Value) :=
  [("std-anycast5", msgAddr false (some (5, 0b10110)) 0 (addrBits 256 1)),
   ("std-anycast30", msgAddr false (some (30, 12345)) (-1) (addrBits 256 2)),
   ("std-anycast31", msgAddr false (some (31, 7)) 0 (addrBits 256 3)),
   ("std-anycast0", msgAddr false (some (0, 0)) 0 (addrBits 256 4)),
   ("var-len64", msgAddr true none 7 (addrBits 64 5)),
   ("var-len256", msgAddr true none (-2) (addrBits 256 6)),
   ("var-anycast3-len100", msgAddr true (some (3, 0b101)) 3 (addrBits 100 7)),
   ("var-anycast8-len8", msgAddr true (some (8, 0xa5)) 0 (addrBits 8 8)),
   ("var-anycast10-len5", msgAddr true (some (10, 0x3ff)) 0 (addrBits 5 9)),
   ("var-anycast4-len256", msgAddr true (some (4, 0b1111)) 1 (addrBits 256 10))]

private def addrCases (suite : String) (op : Instr) : Array OracleCase :=
  anycastAddrs.toArray.map fun (nm, v) => mk suite s!"anycast/{nm}" #[op] #[v]

/-- The cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "PICK" => countCases suite .pick oneCount
  | "ROLL" => countCases suite .roll oneCount
  | "ROLLREV" => countCases suite .rollRev oneCount
  | "BLKSWX" => countCases suite .blkSwapX twoCounts
  | "REVX" => countCases suite .reverseX twoCounts
  | "DROPX" => countCases suite .dropX oneCount
  | "XCHGX" => countCases suite .xchgX oneCount
  | "CHKDEPTH" => countCases suite .chkDepth oneCount
  | "ONLYTOPX" => countCases suite .onlyTopX oneCount
  | "ONLYX" => countCases suite .onlyX oneCount
  | "HASHEXT" | "HASHEXTR" | "HASHEXTA" | "HASHEXTAR" =>
      let append := suite == "HASHEXTA" || suite == "HASHEXTAR"
      let rev := suite == "HASHEXTR" || suite == "HASHEXTAR"
      #[mk suite "id-from-stack/null-only" #[.cryptoOp (.hashExt 255 append rev)] #[.null]]
  | "LSHIFT_VAR" => shiftCases suite .lshift [0, 51, 52, 311, 312]
  | "RSHIFT_VAR" => shiftCases suite .rshift [0, 12, 13]
  | "QLSHIFT_VAR" => shiftCases suite (.arithExt (.lshiftVar true)) [52, 312, 1024]
  | "QRSHIFT_VAR" => shiftCases suite (.arithExt (.rshiftVar true)) [12, 13, -1]
  | "AND" => logicCases suite .and_
  | "OR" => logicCases suite .or
  | "QAND" => logicCases suite (.contExt .qand)
  | "QOR" => logicCases suite (.contExt .qor)
  | "QMULRSHIFT" => mulShrCases suite (.arithExt (.shrMod true false 1 (-1) true none))
  | "QMULRSHIFTR" => mulShrCases suite (.arithExt (.shrMod true false 1 0 true none))
  | "QMULRSHIFTC" => mulShrCases suite (.arithExt (.shrMod true false 1 1 true none))
  | "QMULRSHIFTMOD" => mulShrCases suite (.arithExt (.shrMod true false 3 (-1) true none))
  | "MULRSHIFT#" => opCases suite (.mulShrModConst 1 (-1) 20) [("x-nan-shift20", #[none, some 3])]
  | "QLSHIFTDIV" => shlDivCases suite (.arithExt (.shlDivMod 1 (-1) false true none)) false
  | "QLSHIFTDIVMOD" => shlDivCases suite (.arithExt (.shlDivMod 3 (-1) false true none)) false
  | "QLSHIFTADDDIVMOD" => shlDivCases suite (.arithExt (.shlDivMod 3 (-1) true true none)) true
  | "LDMSGADDR" => addrCases suite (.tonEnvOp (.ldMsgAddr false))
  | "LDMSGADDRQ" => addrCases suite (.tonEnvOp (.ldMsgAddr true))
  | "PARSEMSGADDR" => addrCases suite (.tonEnvOp (.parseMsgAddr false))
  | "PARSEMSGADDRQ" => addrCases suite (.tonEnvOp (.parseMsgAddr true))
  | "REWRITESTDADDR" => addrCases suite (.tonEnvOp (.rewriteStdAddr false))
  | "REWRITESTDADDRQ" => addrCases suite (.tonEnvOp (.rewriteStdAddr true))
  | "REWRITEVARADDR" => addrCases suite (.tonEnvOp (.rewriteVarAddr false))
  | "REWRITEVARADDRQ" => addrCases suite (.tonEnvOp (.rewriteVarAddr true))
  | _ => #[]

end Tests.Gen.Versions

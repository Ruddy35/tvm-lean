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
- `consume_gas` throws at once from version 4 only (vm.h:203-209); before, the `gas.check()` that
  ends a step finds it, and the jump to the exception handler is made after that check
  (vm.cpp:483-497). An exception into a handler with a closure stack of 45 entries charges stack
  gas on the jump; with the gas running out there, the handler's first instruction runs before
  version 4 (`exc-closure-handler/limit*`, around the charges of the exception and of the stack).
- `GLOBALID` reads the global id from the unpacked configuration from version 6; before, from entry
  19 of a configuration dictionary in parameter 19 of `c7` (tonops.cpp:277-304).
- `SENDMSG` (tonops.cpp:2121-2357) takes the prices from the configuration dictionary of parameter 9
  (entries 24 and 25) and allows 2^13 cells before version 6; counts the message's extra-currency
  dictionary, and the extra currencies of the balance (mode 128) or incoming value (mode 64), before
  version 10; computes the IHR fee unless the message disables it before version 11; reads
  `extra_flags` as the user's `ihr_fee` before version 12; counts the user's fees if larger before
  version 14. The cases vary each of these in messages and `c7`.
- `RUNVM` clamps the child's gas limits by what the parent has left after paying its free gas
  (isolated gas, mode 128) from version 10, before by what it had before (vm.cpp:752-757); a child
  that did not commit returns null as its data or actions from version 11, before a cell entry
  without a cell, which `ISNULL` does not take for null (vm.cpp:811-826).
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

private def pi' (n : Int) : Value := .int (.num n)

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

/-- `THROW 5` into a handler `{ PUSHINT 7 }` holding 45 stack entries, with the gas limit `lim`:
1021 gas up to the exception's charge, 15 for the stack of the jump (47 entries), 18 for `PUSHINT`. -/
private def excClosureCase (lim : Int) : OracleCase :=
  let handler : Instr := .pushCont (Slice.ofCell (Tests.Gen.Control.codeOf #[pi 7]))
  let prog : Array Instr :=
    (List.replicate 45 (pi 1)).toArray ++
      #[handler, .setContArgs 15 (-1), .setContArgs 15 (-1), .setContArgs 15 (-1), .popCtr 2, .throw 5]
  { mk "THROW" s!"exc-closure-handler/limit{lim}" prog with gasLimits := { gasLimit := lim, gasMax := lim } }

/-- Grams (VarUInteger 16): 4-bit byte length, then the value. -/
private def gramsBits (g : Nat) : BitString :=
  let len := if g = 0 then 0 else (Nat.log2 g + 8) / 8
  natToBits len 4 ++ natToBits g (8 * len)

private def stdAddr (wc h : Nat) : BitString := natToBits 0b10 2 ++ #[false] ++ natToBits wc 8 ++ natToBits h 256

/-- A dictionary with 32-bit keys of references to the given cells (`dictSetRefWithCells`). -/
private def dict32 (entries : List (Nat × Cell)) : Option Cell :=
  entries.foldl (fun root (k, v) =>
    match dictSetRefWithCells root (natToBits k 32) v .set with
    | .ok (r, _, _, _) => r
    | .error _ => root) none

/-- An extra-currency dictionary: currency 7, amount 100 (VarUInteger 32). -/
private def extraCurrencies : Cell :=
  match dictSetSliceWithCells none (natToBits 7 32) (Slice.ofCell (Cell.mkOrdinary (natToBits 1 5 ++ natToBits 100 8) #[])) .set with
  | .ok (some r, _, _, _) => r
  | _ => Cell.empty

/-- int_msg_info$0 ihr_disabled bounce=1 bounced=0 src:addr_none dest:addr_std(0) value
extra-currencies `ihr_fee`/`extra_flags` fwd_fee created_lt created_at, no init, an inline body. -/
private def sendMsgCell (ihrDisabled : Bool) (value ihr fwd : Nat) (extra : Bool) : Cell :=
  let hdr := #[false, ihrDisabled, true, false] ++ natToBits 0 2 ++ stdAddr 0 0x1234 ++ gramsBits value ++ #[extra] ++
    gramsBits ihr ++ gramsBits fwd ++ natToBits 0 64 ++ natToBits 0 32
  Cell.mkOrdinary (hdr ++ #[false, false] ++ natToBits 0x5a 8) (if extra then #[extraCurrencies] else #[])

/-- msg_forward_prices#ea: IHR factor 1.5, first_frac 1/3. -/
private def fwdPricesBits (lump bit cell : Nat) : BitString :=
  natToBits 0xea 8 ++ natToBits lump 64 ++ natToBits bit 64 ++ natToBits cell 64 ++ natToBits 98304 32 ++
    natToBits 21845 16 ++ natToBits 21845 16

private def mcPrices : BitString := fwdPricesBits 10000000 655360000 65536000000
private def bcPrices : BitString := fwdPricesBits 400000 26214400 2621440000

/-- The configuration dictionary: prices under 24 and 25 (or `entries`), the global id under 19. -/
private def configDict (entries : List (Nat × Cell) :=
    [(19, Cell.mkOrdinary (natToBits (2 ^ 32 - 239) 32) #[]), (24, Cell.mkOrdinary mcPrices #[]),
     (25, Cell.mkOrdinary bcPrices #[])]) : Value :=
  match dict32 entries with
  | some c => .cell c
  | none => .null

/-- `c7` of `SENDMSG` and `GLOBALID`: `params` slots 7, 8, 9, 11, 14 as given, 19 the configuration
dictionary for `GLOBALID` before version 6. -/
private def oldC7 (cfg9 : Value := configDict) (cfg19 : Value := configDict) (balance : Value := .tuple #[pi' 5000000000, .null])
    (incoming : Value := .tuple #[pi' 777, .null]) (myWc : Nat := 0) : Array Value :=
  let unpacked : Value := .tuple #[.null, .slice (Slice.ofCell (Cell.mkOrdinary (natToBits 5 32) #[])), .null, .null,
    .slice (Slice.ofCell (Cell.mkOrdinary mcPrices #[])), .slice (Slice.ofCell (Cell.mkOrdinary bcPrices #[])), .null]
  #[.tuple ((Array.range 20).map fun i =>
    match i with
    | 0 => pi' 0x076ef1ea
    | 7 => balance
    | 8 => .slice (Slice.ofCell (Cell.mkOrdinary (stdAddr myWc 0x99) #[]))
    | 9 => cfg9
    | 11 => incoming
    | 14 => unpacked
    | 19 => cfg19
    | _ => .null)]

private def sendCase (name : String) (msg : Cell) (mode : Int) (c7 : Array Value := oldC7) : OracleCase :=
  { mk "SENDMSG" s!"old-rules/{name}" #[.tonEnvOp .sendMsg] #[.cell msg, pi' mode] with initC7 := c7 }

private def sendMsgCases : Array OracleCase :=
  #[sendCase "ihr-enabled" (sendMsgCell false 100 0 0 false) 1024,
    sendCase "ihr-enabled-send" (sendMsgCell false 100 0 0 false) 0,
    sendCase "ihr-enabled-user-ihr" (sendMsgCell false 100 1000000000 0 false) 1024,
    sendCase "ihr-disabled-user-ihr" (sendMsgCell true 100 1000000000 0 false) 1024,
    sendCase "user-fwd" (sendMsgCell true 100 0 1000000000 false) 1024,
    sendCase "msg-extra" (sendMsgCell true 100 0 0 true) 1024,
    sendCase "mode128-balance-extra" (sendMsgCell true 100 0 0 false) (128 + 1024)
      (oldC7 (balance := .tuple #[pi' 5000000000, .cell extraCurrencies])),
    sendCase "mode64-incoming-extra" (sendMsgCell true 100 0 0 false) (64 + 1024)
      (oldC7 (incoming := .tuple #[pi' 777, .cell extraCurrencies])),
    sendCase "mode64-incoming-short" (sendMsgCell true 100 0 0 false) (64 + 1024) (oldC7 (incoming := .tuple #[pi' 777])),
    sendCase "masterchain" (sendMsgCell true 100 0 0 false) 1024 (oldC7 (myWc := 255)),
    sendCase "cfg9-null" (sendMsgCell true 100 0 0 false) 1024 (oldC7 (cfg9 := .null)),
    sendCase "cfg9-no-25" (sendMsgCell true 100 0 0 false) 1024
      (oldC7 (cfg9 := configDict [(24, Cell.mkOrdinary mcPrices #[])])),
    sendCase "cfg9-25-short" (sendMsgCell true 100 0 0 false) 1024
      (oldC7 (cfg9 := configDict [(25, Cell.mkOrdinary (natToBits 0xea 8) #[])]))]

private def globalIdCases : Array OracleCase :=
  let mkG (name : String) (c7 : Array Value) : OracleCase :=
    { mk "GLOBALID" s!"old-rules/{name}" #[.tonEnvOp .globalId] with initC7 := c7 }
  #[mkG "cfg19" oldC7,
    mkG "cfg19-short" (oldC7 (cfg19 := configDict [(19, Cell.mkOrdinary (natToBits 5 16) #[])])),
    mkG "cfg19-missing" (oldC7 (cfg19 := configDict [(24, Cell.mkOrdinary mcPrices #[])])),
    mkG "cfg19-not-cell" (oldC7 (cfg19 := pi' 19))]

/-- `RUNVM` cases of the version rules: a child that throws with `c4` (mode 4) or `c4` and `c5`
(mode 36) returned, and isolated gas after a free `CHKSIGNU` (4000 gas of free gas) with a child
that loops until it runs out of its gas (10000 gas for the parent). -/
private def runvmCases : Array OracleCase :=
  let code (body : Array Instr) : Cell := Tests.Gen.Control.codeOf body
  let child (body : Array Instr) (mode : Nat) (gas? : Option Int := none) : Array Instr :=
    #[pi 0, .pushRef (code body), .ctos] ++ (if mode &&& 4 = 4 then #[.newc, .endc] else #[]) ++
      (match gas? with | some g => #[pi g] | none => #[]) ++ #[.contExt (.runvm mode)]
  let loop : Array Instr := #[.pushCont (Slice.ofCell (code #[])), .contExt (.again false)]
  let sig : Value := .slice (Slice.ofCell (Cell.mkOrdinary (Array.replicate 512 false) #[]))
  #[mk "RUNVM" "uncommitted/data" (child #[.throw 5] 4),
    mk "RUNVM" "uncommitted/data-isnull" (child #[.throw 5] 4 ++ #[.isNull]),
    mk "RUNVM" "uncommitted/data-actions-isnull" (child #[.throw 5] 36 ++ #[.isNull, .xchg0 1, .isNull]),
    { mk "RUNVM" "isolated-gas-limit/after-free-gas"
        (#[.cryptoOp .chkSignU, .pop 0] ++ child loop 136 (some 1000000000)) #[pi' 0, sig, pi' 12345] with
      gasLimits := { gasLimit := 10000, gasMax := 10000 } }]

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
  | "THROW" => #[1020, 1021, 1028, 1035, 1036, 1053, 1054].map excClosureCase
  | "SENDMSG" => sendMsgCases
  | "GLOBALID" => globalIdCases
  | "RUNVM" => runvmCases
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

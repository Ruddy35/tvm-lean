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
  | _ => #[]

end Tests.Gen.Versions

import Tests.Harness.Registry
import Tests.Harness.OracleHarness
import Tests.Harness.FuzzHarness
import TvmLean.Validation.Diff.Schema

/-!
Oracle cases as text, for `tools/klee` (the path-complete check of C++ instruction handlers with
KLEE, `tools/klee/README` section of `tools/README.md`).

- A case line is `<id> \t <global version> \t <gas limit> \t <code BOC hex> \t <stack tokens>`:
  the code cell as a standard BOC in hex, the stack bottom first in the tokens of the oracle
  (`oracle/fif/ton_oracle_runvm.fif`: integers, `N`, `CB:`/`SB:`/`BB:` + BOC hex, `B`, `T`,
  `TUP:<n>`, `K`) and `NaN` for a NaN integer (the oracle gets it through the code prelude of
  `runOracleCase`). The gas limit is the limit and the maximum, without credit, as `runvmx` gets
  it.
- `caseOfLine` turns a line into an `OracleCase`; `runCaseFile` runs a file of them through
  `runOracleCase` (Lean model and C++ `runvmx`) at the global version of the process
  (`TVMLEAN_GLOBAL_VERSION`); the version column is informational.
- `dumpSuiteCases` prints the oracle and fuzz cases of suites as they reach `runvmx`
  (`<suite>/<case> \t <gas> \t <code BOC hex> \t <tokens>`), for rerunning them on an instrumented
  C++ build.
-/

namespace Tests.CaseFile

open TvmLean

private def bocOfHex (h : String) : Except String Cell := do
  let bytes ← hexDecode h
  match stdBocDeserialize bytes with
  | .ok c => pure c
  | .error e => throw s!"bad BOC: {reprStr e}"

/-- The stack (bottom first) of oracle tokens. -/
def parseStackTokens (toks : List String) : Except String (Array Value) := do
  let mut st : Array Value := #[]
  for t in toks do
    if t == "N" then st := st.push .null
    else if t == "NaN" then st := st.push (.int .nan)
    else if t == "I" then st := st.push (.int (.num 0))
    else if t == "C" then st := st.push (.cell Cell.empty)
    else if t == "S" then st := st.push (.slice (Slice.ofCell Cell.empty))
    else if t == "B" then st := st.push (.builder Builder.empty)
    else if t == "T" then st := st.push (.tuple #[])
    else if t == "K" then st := st.push (.cont (.quit 0))
    else if t.startsWith "CB:" then st := st.push (.cell (← bocOfHex (t.drop 3)))
    else if t.startsWith "SB:" then st := st.push (.slice (Slice.ofCell (← bocOfHex (t.drop 3))))
    else if t.startsWith "BB:" then
      let c ← bocOfHex (t.drop 3)
      st := st.push (.builder { bits := c.bits, refs := c.refs })
    else if t.startsWith "TUP:" then
      let n ← match (t.drop 4).toNat? with
        | some n => pure n
        | none => throw s!"bad token {t}"
      if n > st.size then throw s!"{t}: only {st.size} values"
      st := (st.extract 0 (st.size - n)).push (.tuple (st.extract (st.size - n) st.size))
    else
      match t.toInt? with
      | some n => st := st.push (.int (.num n))
      | none => throw s!"bad token {t}"
  pure st

/-- The oracle case of a case line (see the module doc), for the suite `instr`. -/
def caseOfLine (instr : String) (line : String) : Except String OracleCase := do
  match line.splitOn "\t" with
  | [id, _ver, gas, code, toks] =>
      let g ← match gas.toInt? with
        | some g => pure g
        | none => throw s!"{id}: bad gas {gas}"
      let codeCell ← bocOfHex code
      let stack ← parseStackTokens ((toks.splitOn " ").filter (· ≠ ""))
      pure { name := id, instr := { name := instr }, codeCell? := some codeCell, initStack := stack,
             gasLimits := { gasLimit := g, gasMax := g, gasCredit := 0 } }
  | _ => throw s!"bad case line: {line.take 80}"

/-- Runs every case of the file `path` on the Lean model and on C++ (`runOracleCase`) at the
process's global version, with `jobs` workers; prints `<id> \t OK` or `<id> \t FAIL \t <why>` in the
order of the file, then a summary line. Returns the number of failures.

Worker `w` runs the lines `w`, `w + jobs`, ... and keeps its result lines until all have finished:
the workers share no `IO.Ref`. The `get` and `take` of an `IO.Ref` used by several threads spin
until the value is back (`lean_st_ref_get`, `lean_st_ref_take` in the Lean runtime's `io.cpp`), so
with an `IO.Ref` touched per case (the next line, the failures, the output) a worker preempted
inside `modify` had the others spin through their time slices whenever the workers, their `fift`
processes and the output threads outnumbered the cores. An exception of one case is that case's
failure; the other cases of its worker still run. -/
def runCaseFile (path : String) (jobs : Nat) : IO Nat := do
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").filter (·.trim ≠ "") |>.toArray
  let jobs := Nat.max 1 jobs
  -- the result line of a case line, and whether the case failed
  let runLine (line : String) : IO (String × Bool) := do
    let msg ←
      match caseOfLine "KLEE" line with
      | .error e => pure (some e)
      | .ok c =>
          try
            let r ← runOracleCase c
            pure (if r.ok then none else some (r.error?.getD "failed"))
          catch e =>
            pure (some s!"error: {e}")
    let id := (line.splitOn "\t").headD "?"
    match msg with
    | none => pure (s!"{id}\tOK", false)
    | some m => pure (s!"{id}\tFAIL\t{m}", true)
  let worker (w : Nat) : IO (Array (String × Bool)) := do
    let mut out := #[]
    -- the lines `w + k * jobs` below `lines.size` (`w < jobs`)
    for k in [0:(lines.size + jobs - 1 - w) / jobs] do
      out := out.push (← runLine lines[w + k * jobs]!)
    pure out
  let mut tasks := #[]
  for w in [0:jobs] do
    tasks := tasks.push (← IO.asTask (worker w))
  let mut results : Array (Array (String × Bool)) := #[]
  let mut fails := 0
  for t in tasks do
    match ← IO.wait t with
    | .ok rs => results := results.push rs
    | .error e =>
        results := results.push #[]
        fails := fails + 1
        IO.println s!"[worker/error] {e}"
  -- line `i` is the `i / jobs`-th of worker `i % jobs`
  for i in [0:lines.size] do
    if let some (l, failed) := results[i % jobs]?.bind (·[i / jobs]?) then
      IO.println l
      if failed then fails := fails + 1
  IO.println s!"cases={lines.size} failures={fails}"
  pure fails

/-- Prints the case lines (without the version column) of the oracle and fuzz cases of the suites
named in `names` (see the module doc). -/
def dumpSuiteCases (suites : Array InstrSuite) (oracleCases : InstrSuite → Array OracleCase)
    (names : List String) : IO Unit := do
  for suite in suites do
    if names.contains suite.id.name then
      let cases := oracleCases suite ++ suite.fuzz.flatMap (fun spec => fuzzSpecCases spec suite.oracle)
      for c in cases do
        match oracleCaseInvocation c with
        | .error e => IO.eprintln s!"{suite.id.name}/{c.name}: not dumped: {e}"
        | .ok (code, toks, gas) =>
            match cellBocHex code with
            | .error e => IO.eprintln s!"{suite.id.name}/{c.name}: not dumped: {e}"
            | .ok hex =>
                let lib := if c.initLibraries.isEmpty then "" else "\tLIB"
                IO.println s!"{suite.id.name}/{c.name}\t{gas}\t{hex}\t{" ".intercalate toks}{lib}"

end Tests.CaseFile

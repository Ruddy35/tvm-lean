import Tests.Harness.Registry
import Tests.Harness.OracleHarness
import Tests.Harness.FuzzHarness
import Tests.Harness.Gen.CellDepth
import Tests.Harness.Gen.Loops
import Tests.Harness.Gen.Dict
import Tests.Harness.Gen.OwnOpcode
import Tests.Harness.Gen.Versions
import TvmLean.Spec.Index

namespace Tests

structure RunnerOpts where
  filter? : Option String := none
  unitOnly : Bool := false
  oracleOnly : Bool := false
  fuzzOnly : Bool := false
  opcodeCheck : Bool := false
  opcodeShare : Bool := false
  jobs? : Option Nat := none
  progress : Bool := true
  deriving Repr

structure RunnerSummary where
  suites : Nat := 0
  unitCases : Nat := 0
  oracleCases : Nat := 0
  fuzzCases : Nat := 0
  failures : Nat := 0
  deriving Repr

structure SuiteRunResult where
  suiteId : TvmLean.InstrId
  unitCases : Nat := 0
  oracleCases : Nat := 0
  fuzzCases : Nat := 0
  failures : Nat := 0
  failureLines : Array String := #[]
  deriving Repr

def suiteSelected (opts : RunnerOpts) (suite : InstrSuite) : Bool :=
  match opts.filter? with
  | none => true
  | some needle => suite.id.name = needle

def runUnitCase (suite : InstrSuite) (c : UnitCase) : IO (Option String) := do
  try
    c.run
    pure none
  catch e =>
    pure (some s!"{suite.id.name}/{c.name}: {e.toString}")

private def parsePositiveNat? (s : String) : Option Nat :=
  match s.trim.toNat? with
  | some 0 => none
  | some n => some n
  | none => none

private def readPositiveNatEnv (name : String) : IO (Option Nat) := do
  match (← IO.getEnv name) with
  | some v => pure (parsePositiveNat? v)
  | none => pure none

private def detectJobsFromCmd (cmd : String) (args : Array String := #[]) : IO (Option Nat) := do
  try
    let out ← IO.Process.output { cmd := cmd, args := args }
    if out.exitCode = 0 then
      pure (parsePositiveNat? out.stdout)
    else
      pure none
  catch _ =>
    pure none

private def detectDefaultJobs : IO Nat := do
  match (← readPositiveNatEnv "TVMLEAN_TEST_JOBS") with
  | some n => pure n
  | none =>
    match (← readPositiveNatEnv "LEAN_NUM_THREADS") with
    | some n => pure n
    | none =>
      match (← detectJobsFromCmd "nproc") with
      | some n => pure n
      | none =>
        match (← detectJobsFromCmd "sysctl" #["-n", "hw.ncpu"]) with
        | some n => pure n
        | none => pure 8

private def oracleFailureReason (out : OracleRunResult) : String :=
  match out.error? with
  | some err => err
  | none =>
      match out.comparison? with
      | some cmp =>
          match cmp.mismatch? with
          | some mismatch => mismatch.message
          | none => "oracle comparison failed"
      | none => "oracle comparison failed"

/-- The prefixes a spec row may mean: `prefixBits` is either the checked prefix itself or a sample
encoding of `skipLenBits` bits whose top `checkLenBits` bits are the prefix. -/
def specRowPrefixes (row : TvmLean.InstrSpecRow) : Array TvmLean.BitString :=
  let sample := (TvmLean.natToBits row.prefixBits row.skipLenBits).extract 0 row.checkLenBits
  if row.prefixBits < 2 ^ row.checkLenBits then #[TvmLean.natToBits row.prefixBits row.checkLenBits, sample] else #[sample]

/-- Whether the instruction `i` is the suite's own opcode (its encoding starts with the prefix of the
suite's spec row); true for a suite without a spec row. -/
def isSuiteOpcode (suite : InstrSuite) (i : TvmLean.Instr) : Bool :=
  match TvmLean.allInstrRows.find? (fun r => r.id.name == suite.id.name) with
  | none => true
  | some row =>
      match TvmLean.encodeCp0 i with
      | .ok e => (specRowPrefixes row).any fun p => e.size ≥ p.size && e.extract 0 p.size == p
      | .error _ => false

/-- Whether the code cell `cc` is one instruction of the suite's own opcode, as raw bits (the
alternative encodings of `Tests.Gen.OwnOpcode`): no references, decoded in full, starting with the
prefix of the suite's spec row. -/
def codeIsSuiteOpcode (suite : InstrSuite) (cc : TvmLean.Cell) : Bool :=
  match TvmLean.allInstrRows.find? (fun r => r.id.name == suite.id.name) with
  | none => false
  | some row =>
      cc.refs.isEmpty &&
        (match TvmLean.decodeCp0WithBits (TvmLean.Slice.ofCell cc) with
         | .ok (_, used, _) => used == cc.bits.size
         | .error _ => false) &&
        (specRowPrefixes row).any fun p => cc.bits.size ≥ p.size && cc.bits.extract 0 p.size == p

/-- Short stacks for every suite: C++ checks the stack depth (`check_underflow`) before popping
the operands, so a stack too short for an instruction is stk_und whatever its values, while a
model that pops first fails on the first value of a wrong type. The suite's first oracle case
that runs its own opcode alone (as a program or a raw code cell) is run on 0..5 copies of `null`
and of `1` (its `c7`, libraries and gas kept). -/
def shortStackCases (suite : InstrSuite) : Array OracleCase :=
  let ownAlone (c : OracleCase) : Bool :=
    match c.codeCell? with
    | some cc => codeIsSuiteOpcode suite cc
    | none => match c.program.toList with | [i] => isSuiteOpcode suite i | _ => false
  match (suite.oracle ++ Tests.Gen.OwnOpcode.casesFor suite.id.name).find? ownAlone with
  | none => #[]
  | some base =>
      (#[("null", TvmLean.Value.null), ("int", TvmLean.Value.int (.num 1))] : Array (String × TvmLean.Value)).flatMap fun (vl, v) =>
        (Array.range 6).map fun k =>
          { base with name := s!"sweep/short-stack/{vl}{k}", initStack := Array.replicate k v }

/-- Every oracle case run for `suite`: its own, the short stacks, and the generators run for every
suite (`Tests.Gen.CellDepth`, `Tests.Gen.OwnOpcode`, `Tests.Gen.Loops`, the overflow, label and library cases of `Tests.Gen.Dict`,
`Tests.Gen.Versions`). -/
def suiteOracleCases (suite : InstrSuite) : Array OracleCase :=
  suite.oracle ++ shortStackCases suite ++ Tests.Gen.CellDepth.casesFor suite.id.name ++
    Tests.Gen.OwnOpcode.casesFor suite.id.name ++ Tests.Gen.Loops.casesFor suite.id.name ++
    Tests.Gen.Dict.overflowCasesFor suite.id.name ++ Tests.Gen.Dict.labelCasesFor suite.id.name ++
    Tests.Gen.Dict.libCasesFor suite.id.name ++
    Tests.Gen.Versions.casesFor suite.id.name

private def runSuite (opts : RunnerOpts) (suite : InstrSuite) : IO SuiteRunResult := do
  let mut out : SuiteRunResult := { suiteId := suite.id }

  if !opts.oracleOnly && !opts.fuzzOnly then
    for c in suite.unit do
      out := { out with unitCases := out.unitCases + 1 }
      let err? ← runUnitCase suite c
      match err? with
      | some msg =>
          out := { out with
            failures := out.failures + 1
            failureLines := out.failureLines.push s!"[FAIL][unit] {msg}" }
      | none => pure ()

  if !opts.unitOnly && !opts.fuzzOnly then
    for c in suiteOracleCases suite do
      out := { out with oracleCases := out.oracleCases + 1 }
      let runOut ← runOracleCase c
      if !runOut.ok then
        let reason := oracleFailureReason runOut
        out := { out with
          failures := out.failures + 1
          failureLines := out.failureLines.push s!"[FAIL][oracle] {suite.id.name}/{runOut.caseName}: {reason}" }

  if !opts.unitOnly && !opts.oracleOnly then
    for spec in suite.fuzz do
      let fuzzOut ← runFuzzSpec spec suite.oracle
      out := { out with fuzzCases := out.fuzzCases + fuzzOut.total }
      if fuzzOut.failures.size > 0 then
        out := { out with failures := out.failures + fuzzOut.failures.size }
        for fail in fuzzOut.failures do
          let reason := oracleFailureReason fail.result
          let artifact :=
            match fail.artifact? with
            | some p => s!" artifact={p}"
            | none => ""
          out := { out with
            failureLines := out.failureLines.push
              s!"[FAIL][fuzz] {suite.id.name}/{fail.result.caseName} seed={fuzzOut.seed.toNat} iter={fail.iteration}: {reason}{artifact}" }

  pure out

private def effectiveJobs (opts : RunnerOpts) (suiteCount : Nat) : IO Nat := do
  let jobs0 ←
    match opts.jobs? with
    | some n => pure n
    | none => detectDefaultJobs
  let jobs := Nat.max 1 jobs0
  pure (Nat.max 1 (Nat.min jobs suiteCount))

def runSuites (opts : RunnerOpts) : IO RunnerSummary := do
  let suites ← registeredSuites
  let selected := suites.filter (suiteSelected opts)
  if selected.isEmpty then
    return {}

  let jobs ← effectiveJobs opts selected.size
  if opts.progress then
    IO.println s!"[runner] suites={selected.size} jobs={jobs}"

  let nextIdxRef ← IO.mkRef 0
  let resultsRef ← IO.mkRef (#[] : Array SuiteRunResult)

  let worker : IO Unit := do
    let mut keepRunning := true
    while keepRunning do
      let idx ← nextIdxRef.modifyGet (fun n => (n, n + 1))
      if h : idx < selected.size then
        let suite := selected[idx]'h
        if opts.progress then
          IO.println s!"[suite/start] {suite.id.name} ({idx + 1}/{selected.size})"
        let t0 ← IO.monoMsNow
        let suiteResult ← runSuite opts suite
        let t1 ← IO.monoMsNow
        if opts.progress then
          IO.println s!"[suite/done] {suite.id.name} unit={suiteResult.unitCases} oracle={suiteResult.oracleCases} fuzz={suiteResult.fuzzCases} failures={suiteResult.failures} ms={t1 - t0}"
        for line in suiteResult.failureLines do
          IO.println line
        resultsRef.modify (·.push suiteResult)
      else
        keepRunning := false

  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for _ in [0:jobs] do
    let t ← IO.asTask worker
    tasks := tasks.push t

  let mut workerFailures : Nat := 0
  for t in tasks do
    match (← IO.wait t) with
    | .ok _ => pure ()
    | .error e =>
        workerFailures := workerFailures + 1
        IO.println s!"[worker/error] {e.toString}"

  let results ← resultsRef.get
  let mut summary : RunnerSummary := { suites := selected.size, failures := workerFailures }
  for r in results do
    summary := { summary with
      unitCases := summary.unitCases + r.unitCases
      oracleCases := summary.oracleCases + r.oracleCases
      fuzzCases := summary.fuzzCases + r.fuzzCases
      failures := summary.failures + r.failures }

  pure summary

def printSummary (s : RunnerSummary) : IO Unit := do
  IO.println s!"suites={s.suites} unit={s.unitCases} oracle={s.oracleCases} fuzz={s.fuzzCases} failures={s.failures}"

/-- Returns 0 on success, 1 when at least one case failed. -/
def runAndReport (opts : RunnerOpts) : IO UInt32 := do
  let summary ← runSuites opts
  printSummary summary
  if summary.failures = 0 then
    pure 0
  else
    pure 1

end Tests

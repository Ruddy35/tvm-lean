import Tests.All
import Tests.Harness.Cli
import Tests.Harness.Runner
import Tests.Harness.OpcodeCheck
import Tests.Harness.CaseFile

namespace TvmLeanTestsApp

def main (args : List String) : IO UInt32 := do
  let opts ← Tests.parseCliArgs args
  if opts.opcodeCheck then
    return (if (← Tests.opcodeCheck) == 0 then 0 else 1)
  if opts.opcodeShare then
    Tests.opcodeShare opts.filter?
    return 0
  if let some names := opts.dumpCases? then
    Tests.CaseFile.dumpSuiteCases (← Tests.registeredSuites) Tests.suiteOracleCases (names.splitOn ",")
    return 0
  if let some path := opts.casesFile? then
    let fails ← Tests.CaseFile.runCaseFile path (opts.jobs?.getD 8)
    return (if fails == 0 then 0 else 1)
  Tests.runAndReport opts

end TvmLeanTestsApp

def main (args : List String) : IO UInt32 :=
  TvmLeanTestsApp.main args

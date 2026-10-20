import Tests.All
import Tests.Harness.Cli
import Tests.Harness.Runner
import Tests.Harness.OpcodeCheck

namespace TvmLeanTestsApp

def main (args : List String) : IO UInt32 := do
  let opts ← Tests.parseCliArgs args
  if opts.opcodeCheck then
    return (if (← Tests.opcodeCheck) == 0 then 0 else 1)
  Tests.runAndReport opts

end TvmLeanTestsApp

def main (args : List String) : IO UInt32 :=
  TvmLeanTestsApp.main args

import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.LTIME

def suite : InstrSuite where
  id := { name := "LTIME" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "LTIME"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.LTIME

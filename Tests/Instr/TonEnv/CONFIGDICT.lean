import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.CONFIGDICT

def suite : InstrSuite where
  id := { name := "CONFIGDICT" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "CONFIGDICT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.CONFIGDICT

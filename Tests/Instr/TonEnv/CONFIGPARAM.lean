import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.CONFIGPARAM

def suite : InstrSuite where
  id := { name := "CONFIGPARAM" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "CONFIGPARAM"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.CONFIGPARAM

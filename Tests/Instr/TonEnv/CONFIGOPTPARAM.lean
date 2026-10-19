import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.CONFIGOPTPARAM

def suite : InstrSuite where
  id := { name := "CONFIGOPTPARAM" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "CONFIGOPTPARAM"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.CONFIGOPTPARAM

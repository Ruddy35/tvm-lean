import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INMSGPARAM

def suite : InstrSuite where
  id := { name := "INMSGPARAM" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "INMSGPARAM"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INMSGPARAM

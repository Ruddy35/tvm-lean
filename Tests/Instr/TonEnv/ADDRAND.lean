import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.ADDRAND

def suite : InstrSuite where
  id := { name := "ADDRAND" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "ADDRAND"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.ADDRAND

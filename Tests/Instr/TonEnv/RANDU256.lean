import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.RANDU256

def suite : InstrSuite where
  id := { name := "RANDU256" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "RANDU256"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.RANDU256

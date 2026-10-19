import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.COMMIT

def suite : InstrSuite where
  id := { name := "COMMIT" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "COMMIT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.COMMIT

import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.RANDSEED

def suite : InstrSuite where
  id := { name := "RANDSEED" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "RANDSEED"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.RANDSEED

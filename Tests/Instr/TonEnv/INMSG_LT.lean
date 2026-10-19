import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INMSG_LT

def suite : InstrSuite where
  id := { name := "INMSG_LT" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "INMSG_LT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INMSG_LT

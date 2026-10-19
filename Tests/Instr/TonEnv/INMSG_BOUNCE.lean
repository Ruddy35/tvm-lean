import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INMSG_BOUNCE

def suite : InstrSuite where
  id := { name := "INMSG_BOUNCE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "INMSG_BOUNCE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INMSG_BOUNCE

import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INMSG_SRC

def suite : InstrSuite where
  id := { name := "INMSG_SRC" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "INMSG_SRC"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INMSG_SRC

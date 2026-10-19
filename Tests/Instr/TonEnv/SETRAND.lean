import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.SETRAND

def suite : InstrSuite where
  id := { name := "SETRAND" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "SETRAND"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.SETRAND

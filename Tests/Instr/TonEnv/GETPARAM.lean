import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETPARAM

def suite : InstrSuite where
  id := { name := "GETPARAM" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETPARAM"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETPARAM

import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETORIGINALFWDFEE

def suite : InstrSuite where
  id := { name := "GETORIGINALFWDFEE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETORIGINALFWDFEE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETORIGINALFWDFEE

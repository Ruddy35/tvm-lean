import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INCOMINGVALUE

def suite : InstrSuite where
  id := { name := "INCOMINGVALUE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "INCOMINGVALUE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INCOMINGVALUE

import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PARSEMSGADDRQ

def suite : InstrSuite where
  id := { name := "PARSEMSGADDRQ" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "PARSEMSGADDRQ"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PARSEMSGADDRQ

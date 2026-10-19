import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.REWRITESTDADDRQ

def suite : InstrSuite where
  id := { name := "REWRITESTDADDRQ" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "REWRITESTDADDRQ"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.REWRITESTDADDRQ

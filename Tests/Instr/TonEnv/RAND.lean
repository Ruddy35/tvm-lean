import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.RAND

def suite : InstrSuite where
  id := { name := "RAND" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "RAND"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.RAND

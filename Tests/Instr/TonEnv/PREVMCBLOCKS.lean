import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PREVMCBLOCKS

def suite : InstrSuite where
  id := { name := "PREVMCBLOCKS" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "PREVMCBLOCKS"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PREVMCBLOCKS

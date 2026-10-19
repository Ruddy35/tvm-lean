import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PREVMCBLOCKS_100

def suite : InstrSuite where
  id := { name := "PREVMCBLOCKS_100" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "PREVMCBLOCKS_100"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PREVMCBLOCKS_100

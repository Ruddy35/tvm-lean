import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.BLOCKLT

def suite : InstrSuite where
  id := { name := "BLOCKLT" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "BLOCKLT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.BLOCKLT

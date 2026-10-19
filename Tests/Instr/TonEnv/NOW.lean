import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.NOW

def suite : InstrSuite where
  id := { name := "NOW" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "NOW"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.NOW

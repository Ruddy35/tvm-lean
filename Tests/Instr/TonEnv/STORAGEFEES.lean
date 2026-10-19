import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.STORAGEFEES

def suite : InstrSuite where
  id := { name := "STORAGEFEES" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "STORAGEFEES"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.STORAGEFEES

import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.SETGLOB

def suite : InstrSuite where
  id := { name := "SETGLOB" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "SETGLOB"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.SETGLOB

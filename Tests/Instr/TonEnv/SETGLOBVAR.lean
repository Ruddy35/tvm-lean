import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.SETGLOBVAR

def suite : InstrSuite where
  id := { name := "SETGLOBVAR" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "SETGLOBVAR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.SETGLOBVAR

import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETGLOBVAR

def suite : InstrSuite where
  id := { name := "GETGLOBVAR" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETGLOBVAR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETGLOBVAR

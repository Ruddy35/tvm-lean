import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETPARAMLONG2

def suite : InstrSuite where
  id := { name := "GETPARAMLONG2" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETPARAMLONG2"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETPARAMLONG2

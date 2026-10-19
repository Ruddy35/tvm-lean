import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETPARAMLONG

def suite : InstrSuite where
  id := { name := "GETPARAMLONG" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETPARAMLONG"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETPARAMLONG

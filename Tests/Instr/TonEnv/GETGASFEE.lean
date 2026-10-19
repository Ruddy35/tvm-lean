import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETGASFEE

def suite : InstrSuite where
  id := { name := "GETGASFEE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETGASFEE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETGASFEE

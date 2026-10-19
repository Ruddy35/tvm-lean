import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETGASFEESIMPLE

def suite : InstrSuite where
  id := { name := "GETGASFEESIMPLE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETGASFEESIMPLE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETGASFEESIMPLE

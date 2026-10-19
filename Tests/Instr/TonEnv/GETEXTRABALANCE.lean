import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETEXTRABALANCE

def suite : InstrSuite where
  id := { name := "GETEXTRABALANCE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETEXTRABALANCE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETEXTRABALANCE

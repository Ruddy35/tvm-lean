import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.BALANCE

def suite : InstrSuite where
  id := { name := "BALANCE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "BALANCE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.BALANCE

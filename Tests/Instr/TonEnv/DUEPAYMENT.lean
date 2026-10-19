import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.DUEPAYMENT

def suite : InstrSuite where
  id := { name := "DUEPAYMENT" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "DUEPAYMENT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.DUEPAYMENT

import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETFORWARDFEE

def suite : InstrSuite where
  id := { name := "GETFORWARDFEE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETFORWARDFEE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETFORWARDFEE

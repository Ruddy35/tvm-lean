import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.ACCEPT

def suite : InstrSuite where
  id := { name := "ACCEPT" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "ACCEPT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.ACCEPT

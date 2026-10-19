import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.REWRITEVARADDR

def suite : InstrSuite where
  id := { name := "REWRITEVARADDR" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "REWRITEVARADDR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.REWRITEVARADDR

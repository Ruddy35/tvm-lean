import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.REWRITESTDADDR

def suite : InstrSuite where
  id := { name := "REWRITESTDADDR" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "REWRITESTDADDR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.REWRITESTDADDR

import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.RIST255_ADD

def suite : InstrSuite where
  id := { name := "RIST255_ADD" }
  unit := Tests.Gen.Crypto.unitFor "RIST255_ADD"
  oracle := Tests.Gen.Crypto.casesFor "RIST255_ADD"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.RIST255_ADD

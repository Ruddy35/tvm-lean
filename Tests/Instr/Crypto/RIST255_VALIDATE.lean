import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.RIST255_VALIDATE

def suite : InstrSuite where
  id := { name := "RIST255_VALIDATE" }
  unit := Tests.Gen.Crypto.unitFor "RIST255_VALIDATE"
  oracle := Tests.Gen.Crypto.casesFor "RIST255_VALIDATE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.RIST255_VALIDATE

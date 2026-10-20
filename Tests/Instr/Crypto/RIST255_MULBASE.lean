import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.RIST255_MULBASE

def suite : InstrSuite where
  id := { name := "RIST255_MULBASE" }
  unit := Tests.Gen.Crypto.unitFor "RIST255_MULBASE"
  oracle := Tests.Gen.Crypto.casesFor "RIST255_MULBASE"
  fuzz := Tests.Gen.Crypto.fuzzFor "RIST255_MULBASE"

initialize registerSuite suite

end Tests.Instr.Crypto.RIST255_MULBASE

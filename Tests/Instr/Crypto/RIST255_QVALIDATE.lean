import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.RIST255_QVALIDATE

def suite : InstrSuite where
  id := { name := "RIST255_QVALIDATE" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "RIST255_QVALIDATE"
  fuzz := Tests.Gen.Crypto.fuzzFor "RIST255_QVALIDATE"

initialize registerSuite suite

end Tests.Instr.Crypto.RIST255_QVALIDATE

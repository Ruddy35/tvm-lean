import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_VERIFY

def suite : InstrSuite where
  id := { name := "BLS_VERIFY" }
  unit := Tests.Gen.Crypto.unitFor "BLS_VERIFY"
  oracle := Tests.Gen.Crypto.casesFor "BLS_VERIFY"
  fuzz := Tests.Gen.Crypto.fuzzFor "BLS_VERIFY"

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_VERIFY

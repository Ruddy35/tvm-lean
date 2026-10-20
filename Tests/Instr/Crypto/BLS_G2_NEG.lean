import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_G2_NEG

def suite : InstrSuite where
  id := { name := "BLS_G2_NEG" }
  unit := Tests.Gen.Crypto.unitFor "BLS_G2_NEG"
  oracle := Tests.Gen.Crypto.casesFor "BLS_G2_NEG"
  fuzz := Tests.Gen.Crypto.fuzzFor "BLS_G2_NEG"

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_G2_NEG

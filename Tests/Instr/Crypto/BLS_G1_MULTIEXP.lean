import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_G1_MULTIEXP

def suite : InstrSuite where
  id := { name := "BLS_G1_MULTIEXP" }
  unit := Tests.Gen.Crypto.unitFor "BLS_G1_MULTIEXP"
  oracle := Tests.Gen.Crypto.casesFor "BLS_G1_MULTIEXP"
  fuzz := Tests.Gen.Crypto.fuzzFor "BLS_G1_MULTIEXP"

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_G1_MULTIEXP

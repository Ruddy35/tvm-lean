import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_G2_ISZERO

def suite : InstrSuite where
  id := { name := "BLS_G2_ISZERO" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "BLS_G2_ISZERO"
  fuzz := Tests.Gen.Crypto.fuzzFor "BLS_G2_ISZERO"

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_G2_ISZERO

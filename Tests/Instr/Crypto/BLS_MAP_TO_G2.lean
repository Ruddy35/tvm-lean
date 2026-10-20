import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_MAP_TO_G2

def suite : InstrSuite where
  id := { name := "BLS_MAP_TO_G2" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "BLS_MAP_TO_G2"
  fuzz := Tests.Gen.Crypto.fuzzFor "BLS_MAP_TO_G2"

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_MAP_TO_G2

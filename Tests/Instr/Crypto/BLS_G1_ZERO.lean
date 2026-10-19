import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_G1_ZERO

def suite : InstrSuite where
  id := { name := "BLS_G1_ZERO" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "BLS_G1_ZERO"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_G1_ZERO

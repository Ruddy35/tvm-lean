import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.P256_CHKSIGNS

def suite : InstrSuite where
  id := { name := "P256_CHKSIGNS" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "P256_CHKSIGNS"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.P256_CHKSIGNS

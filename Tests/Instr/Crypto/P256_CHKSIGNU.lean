import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.P256_CHKSIGNU

def suite : InstrSuite where
  id := { name := "P256_CHKSIGNU" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "P256_CHKSIGNU"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.P256_CHKSIGNU

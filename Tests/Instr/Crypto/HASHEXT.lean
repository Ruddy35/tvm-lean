import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.HASHEXT

def suite : InstrSuite where
  id := { name := "HASHEXT" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "HASHEXT"
  fuzz := Tests.Gen.Crypto.fuzzFor "HASHEXT"

initialize registerSuite suite

end Tests.Instr.Crypto.HASHEXT

import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.SHA256U

def suite : InstrSuite where
  id := { name := "SHA256U" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "SHA256U"
  fuzz := Tests.Gen.Crypto.fuzzFor "SHA256U"

initialize registerSuite suite

end Tests.Instr.Crypto.SHA256U

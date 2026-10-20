import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_PUSHR

def suite : InstrSuite where
  id := { name := "BLS_PUSHR" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "BLS_PUSHR"
  fuzz := Tests.Gen.Crypto.fuzzFor "BLS_PUSHR"

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_PUSHR

import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_PAIRING

def suite : InstrSuite where
  id := { name := "BLS_PAIRING" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "BLS_PAIRING"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_PAIRING

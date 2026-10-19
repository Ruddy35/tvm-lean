import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.RIST255_QADD

def suite : InstrSuite where
  id := { name := "RIST255_QADD" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "RIST255_QADD"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.RIST255_QADD

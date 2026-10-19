import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.RIST255_FROMHASH

def suite : InstrSuite where
  id := { name := "RIST255_FROMHASH" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "RIST255_FROMHASH"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.RIST255_FROMHASH

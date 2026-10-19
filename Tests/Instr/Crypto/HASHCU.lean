import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.HASHCU

def suite : InstrSuite where
  id := { name := "HASHCU" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "HASHCU"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.HASHCU

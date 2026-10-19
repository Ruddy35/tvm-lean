import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.HASHSU

def suite : InstrSuite where
  id := { name := "HASHSU" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "HASHSU"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.HASHSU

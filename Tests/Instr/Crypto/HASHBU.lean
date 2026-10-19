import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.HASHBU

def suite : InstrSuite where
  id := { name := "HASHBU" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "HASHBU"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.HASHBU

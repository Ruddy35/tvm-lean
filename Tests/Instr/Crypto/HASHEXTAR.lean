import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.HASHEXTAR

def suite : InstrSuite where
  id := { name := "HASHEXTAR" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "HASHEXTAR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.HASHEXTAR

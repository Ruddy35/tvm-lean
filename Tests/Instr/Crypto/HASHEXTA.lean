import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.HASHEXTA

def suite : InstrSuite where
  id := { name := "HASHEXTA" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "HASHEXTA"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.HASHEXTA

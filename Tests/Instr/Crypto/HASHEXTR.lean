import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.HASHEXTR

def suite : InstrSuite where
  id := { name := "HASHEXTR" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "HASHEXTR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.HASHEXTR

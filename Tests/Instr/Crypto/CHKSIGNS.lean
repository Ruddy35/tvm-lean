import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.CHKSIGNS

def suite : InstrSuite where
  id := { name := "CHKSIGNS" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "CHKSIGNS"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.CHKSIGNS

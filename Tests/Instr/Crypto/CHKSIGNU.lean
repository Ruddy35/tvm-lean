import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.CHKSIGNU

def suite : InstrSuite where
  id := { name := "CHKSIGNU" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "CHKSIGNU"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.CHKSIGNU

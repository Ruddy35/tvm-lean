import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.RIST255_MUL

def suite : InstrSuite where
  id := { name := "RIST255_MUL" }
  unit := Tests.Gen.Crypto.unitFor "RIST255_MUL"
  oracle := Tests.Gen.Crypto.casesFor "RIST255_MUL"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.RIST255_MUL

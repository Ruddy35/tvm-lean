import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_AGGREGATEVERIFY

def suite : InstrSuite where
  id := { name := "BLS_AGGREGATEVERIFY" }
  unit := Tests.Gen.Crypto.unitFor "BLS_AGGREGATEVERIFY"
  oracle := Tests.Gen.Crypto.casesFor "BLS_AGGREGATEVERIFY"
  fuzz := Tests.Gen.Crypto.fuzzFor "BLS_AGGREGATEVERIFY"

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_AGGREGATEVERIFY

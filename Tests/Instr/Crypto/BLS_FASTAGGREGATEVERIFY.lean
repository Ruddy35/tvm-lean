import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_FASTAGGREGATEVERIFY

def suite : InstrSuite where
  id := { name := "BLS_FASTAGGREGATEVERIFY" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "BLS_FASTAGGREGATEVERIFY"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_FASTAGGREGATEVERIFY

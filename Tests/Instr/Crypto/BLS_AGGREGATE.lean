import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_AGGREGATE

def suite : InstrSuite where
  id := { name := "BLS_AGGREGATE" }
  unit := #[]
  oracle := Tests.Gen.Crypto.casesFor "BLS_AGGREGATE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_AGGREGATE

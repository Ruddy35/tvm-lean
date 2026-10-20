import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.ECRECOVER

def suite : InstrSuite where
  id := { name := "ECRECOVER" }
  unit := Tests.Gen.Crypto.unitFor "ECRECOVER"
  oracle := Tests.Gen.Crypto.casesFor "ECRECOVER"
  fuzz := Tests.Gen.Crypto.fuzzFor "ECRECOVER"

initialize registerSuite suite

end Tests.Instr.Crypto.ECRECOVER

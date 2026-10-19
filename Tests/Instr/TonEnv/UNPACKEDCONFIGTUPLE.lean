import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.UNPACKEDCONFIGTUPLE

def suite : InstrSuite where
  id := { name := "UNPACKEDCONFIGTUPLE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "UNPACKEDCONFIGTUPLE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.UNPACKEDCONFIGTUPLE

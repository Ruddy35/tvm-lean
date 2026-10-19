import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PARSEMSGADDR

def suite : InstrSuite where
  id := { name := "PARSEMSGADDR" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "PARSEMSGADDR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PARSEMSGADDR

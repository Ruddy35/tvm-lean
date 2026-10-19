import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PREVKEYBLOCK

def suite : InstrSuite where
  id := { name := "PREVKEYBLOCK" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "PREVKEYBLOCK"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PREVKEYBLOCK

import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INMSGPARAMS

def suite : InstrSuite where
  id := { name := "INMSGPARAMS" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "INMSGPARAMS"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INMSGPARAMS

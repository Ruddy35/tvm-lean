import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETSTORAGEFEE

def suite : InstrSuite where
  id := { name := "GETSTORAGEFEE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETSTORAGEFEE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETSTORAGEFEE

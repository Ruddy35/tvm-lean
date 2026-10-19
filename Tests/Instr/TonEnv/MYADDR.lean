import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.MYADDR

def suite : InstrSuite where
  id := { name := "MYADDR" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "MYADDR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.MYADDR

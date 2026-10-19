import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.MYCODE

def suite : InstrSuite where
  id := { name := "MYCODE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "MYCODE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.MYCODE

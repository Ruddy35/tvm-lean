import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GLOBALID

def suite : InstrSuite where
  id := { name := "GLOBALID" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GLOBALID"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GLOBALID

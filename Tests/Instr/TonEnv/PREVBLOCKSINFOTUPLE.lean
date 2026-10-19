import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PREVBLOCKSINFOTUPLE

def suite : InstrSuite where
  id := { name := "PREVBLOCKSINFOTUPLE" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "PREVBLOCKSINFOTUPLE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PREVBLOCKSINFOTUPLE

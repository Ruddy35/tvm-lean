import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETPRECOMPILEDGAS

def suite : InstrSuite where
  id := { name := "GETPRECOMPILEDGAS" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GETPRECOMPILEDGAS"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETPRECOMPILEDGAS

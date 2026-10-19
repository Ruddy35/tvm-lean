import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.SETGASLIMIT

def suite : InstrSuite where
  id := { name := "SETGASLIMIT" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "SETGASLIMIT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.SETGASLIMIT

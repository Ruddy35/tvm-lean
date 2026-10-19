import Tests.Harness.Registry
import Tests.Harness.Gen.TonEnv
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GASCONSUMED

def suite : InstrSuite where
  id := { name := "GASCONSUMED" }
  unit := #[]
  oracle := Tests.Gen.TonEnv.casesFor "GASCONSUMED"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GASCONSUMED

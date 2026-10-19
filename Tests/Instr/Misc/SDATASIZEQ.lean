import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Misc.SDATASIZEQ

def suite : InstrSuite where
  id := { name := "SDATASIZEQ" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "SDATASIZEQ"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Misc.SDATASIZEQ

import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Misc.CDATASIZEQ

def suite : InstrSuite where
  id := { name := "CDATASIZEQ" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "CDATASIZEQ"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Misc.CDATASIZEQ

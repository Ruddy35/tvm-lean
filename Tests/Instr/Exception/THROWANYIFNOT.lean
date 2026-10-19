import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWANYIFNOT

def suite : InstrSuite where
  id := { name := "THROWANYIFNOT" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWANYIFNOT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWANYIFNOT

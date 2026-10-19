import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWIFNOT

def suite : InstrSuite where
  id := { name := "THROWIFNOT" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWIFNOT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWIFNOT

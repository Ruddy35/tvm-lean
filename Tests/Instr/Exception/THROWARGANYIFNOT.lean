import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWARGANYIFNOT

def suite : InstrSuite where
  id := { name := "THROWARGANYIFNOT" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWARGANYIFNOT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWARGANYIFNOT

import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWARGIFNOT

def suite : InstrSuite where
  id := { name := "THROWARGIFNOT" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWARGIFNOT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWARGIFNOT

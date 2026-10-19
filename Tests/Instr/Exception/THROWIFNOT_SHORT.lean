import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWIFNOT_SHORT

def suite : InstrSuite where
  id := { name := "THROWIFNOT_SHORT" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWIFNOT_SHORT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWIFNOT_SHORT

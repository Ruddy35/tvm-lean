import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.DEBUG_1

def suite : InstrSuite where
  id := { name := "DEBUG_1" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "DEBUG_1"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.DEBUG_1

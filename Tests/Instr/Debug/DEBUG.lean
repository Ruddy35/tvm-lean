import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.DEBUG

def suite : InstrSuite where
  id := { name := "DEBUG" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "DEBUG"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.DEBUG

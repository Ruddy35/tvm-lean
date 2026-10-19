import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.DEBUGSTR

def suite : InstrSuite where
  id := { name := "DEBUGSTR" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "DEBUGSTR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.DEBUGSTR

import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Flow.SETCP

def suite : InstrSuite where
  id := { name := "SETCP" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "SETCP"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Flow.SETCP

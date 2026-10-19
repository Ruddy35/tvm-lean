import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Flow.SETCP_SHORT

def suite : InstrSuite where
  id := { name := "SETCP_SHORT" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "SETCP_SHORT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Flow.SETCP_SHORT

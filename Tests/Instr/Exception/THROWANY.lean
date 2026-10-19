import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWANY

def suite : InstrSuite where
  id := { name := "THROWANY" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWANY"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWANY

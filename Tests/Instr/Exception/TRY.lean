import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.TRY

def suite : InstrSuite where
  id := { name := "TRY" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "TRY"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.TRY

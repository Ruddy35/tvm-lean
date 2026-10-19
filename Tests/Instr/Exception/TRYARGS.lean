import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.TRYARGS

def suite : InstrSuite where
  id := { name := "TRYARGS" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "TRYARGS"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.TRYARGS

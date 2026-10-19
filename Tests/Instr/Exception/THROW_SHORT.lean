import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROW_SHORT

def suite : InstrSuite where
  id := { name := "THROW_SHORT" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROW_SHORT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROW_SHORT

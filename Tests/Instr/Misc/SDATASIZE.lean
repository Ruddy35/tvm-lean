import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Misc.SDATASIZE

def suite : InstrSuite where
  id := { name := "SDATASIZE" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "SDATASIZE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Misc.SDATASIZE

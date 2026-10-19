import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.STRDUMP

def suite : InstrSuite where
  id := { name := "STRDUMP" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "STRDUMP"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.STRDUMP

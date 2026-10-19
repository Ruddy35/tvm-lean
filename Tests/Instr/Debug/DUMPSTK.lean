import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.DUMPSTK

def suite : InstrSuite where
  id := { name := "DUMPSTK" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "DUMPSTK"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.DUMPSTK

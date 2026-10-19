import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWIF_SHORT

def suite : InstrSuite where
  id := { name := "THROWIF_SHORT" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWIF_SHORT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWIF_SHORT

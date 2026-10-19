import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWIF

def suite : InstrSuite where
  id := { name := "THROWIF" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWIF"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWIF

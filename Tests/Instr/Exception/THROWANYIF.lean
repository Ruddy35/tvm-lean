import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWANYIF

def suite : InstrSuite where
  id := { name := "THROWANYIF" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWANYIF"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWANYIF

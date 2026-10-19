import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWARGANYIF

def suite : InstrSuite where
  id := { name := "THROWARGANYIF" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWARGANYIF"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWARGANYIF

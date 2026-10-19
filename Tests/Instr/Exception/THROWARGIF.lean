import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWARGIF

def suite : InstrSuite where
  id := { name := "THROWARGIF" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWARGIF"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWARGIF

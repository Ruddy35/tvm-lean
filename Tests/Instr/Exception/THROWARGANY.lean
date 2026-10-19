import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWARGANY

def suite : InstrSuite where
  id := { name := "THROWARGANY" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWARGANY"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWARGANY

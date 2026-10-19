import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWARG

def suite : InstrSuite where
  id := { name := "THROWARG" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "THROWARG"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWARG

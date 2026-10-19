import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.UNTUPLE

def suite : InstrSuite where
  id := { name := "UNTUPLE" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "UNTUPLE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.UNTUPLE

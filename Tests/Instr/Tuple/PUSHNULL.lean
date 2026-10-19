import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.PUSHNULL

def suite : InstrSuite where
  id := { name := "PUSHNULL" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "PUSHNULL"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.PUSHNULL

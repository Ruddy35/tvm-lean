import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.ISNULL

def suite : InstrSuite where
  id := { name := "ISNULL" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "ISNULL"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.ISNULL

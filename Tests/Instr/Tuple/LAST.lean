import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.LAST

def suite : InstrSuite where
  id := { name := "LAST" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "LAST"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.LAST

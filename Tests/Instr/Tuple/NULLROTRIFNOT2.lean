import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLROTRIFNOT2

def suite : InstrSuite where
  id := { name := "NULLROTRIFNOT2" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "NULLROTRIFNOT2"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLROTRIFNOT2

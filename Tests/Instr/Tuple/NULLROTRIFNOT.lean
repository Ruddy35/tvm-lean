import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLROTRIFNOT

def suite : InstrSuite where
  id := { name := "NULLROTRIFNOT" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "NULLROTRIFNOT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLROTRIFNOT

import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLSWAPIFNOT2

def suite : InstrSuite where
  id := { name := "NULLSWAPIFNOT2" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "NULLSWAPIFNOT2"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLSWAPIFNOT2

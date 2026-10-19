import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLSWAPIFNOT

def suite : InstrSuite where
  id := { name := "NULLSWAPIFNOT" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "NULLSWAPIFNOT"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLSWAPIFNOT

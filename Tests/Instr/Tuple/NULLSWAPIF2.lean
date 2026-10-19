import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLSWAPIF2

def suite : InstrSuite where
  id := { name := "NULLSWAPIF2" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "NULLSWAPIF2"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLSWAPIF2

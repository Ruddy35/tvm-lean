import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLSWAPIF

def suite : InstrSuite where
  id := { name := "NULLSWAPIF" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "NULLSWAPIF"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLSWAPIF

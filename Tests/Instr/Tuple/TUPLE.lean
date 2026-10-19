import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.TUPLE

def suite : InstrSuite where
  id := { name := "TUPLE" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "TUPLE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.TUPLE

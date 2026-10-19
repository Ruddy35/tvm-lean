import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.INDEX3

def suite : InstrSuite where
  id := { name := "INDEX3" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "INDEX3"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.INDEX3

import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLROTRIF2

def suite : InstrSuite where
  id := { name := "NULLROTRIF2" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "NULLROTRIF2"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLROTRIF2

import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLROTRIF

def suite : InstrSuite where
  id := { name := "NULLROTRIF" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "NULLROTRIF"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLROTRIF

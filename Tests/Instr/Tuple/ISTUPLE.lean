import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.ISTUPLE

def suite : InstrSuite where
  id := { name := "ISTUPLE" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "ISTUPLE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.ISTUPLE

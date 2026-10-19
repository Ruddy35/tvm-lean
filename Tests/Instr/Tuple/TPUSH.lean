import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.TPUSH

def suite : InstrSuite where
  id := { name := "TPUSH" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "TPUSH"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.TPUSH

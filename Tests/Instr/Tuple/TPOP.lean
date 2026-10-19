import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.TPOP

def suite : InstrSuite where
  id := { name := "TPOP" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "TPOP"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.TPOP

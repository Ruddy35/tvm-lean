import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.TLEN

def suite : InstrSuite where
  id := { name := "TLEN" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "TLEN"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.TLEN

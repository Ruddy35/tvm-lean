import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.INDEXVARQ

def suite : InstrSuite where
  id := { name := "INDEXVARQ" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "INDEXVARQ"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.INDEXVARQ

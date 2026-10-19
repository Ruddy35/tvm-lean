import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.SETINDEXQ

def suite : InstrSuite where
  id := { name := "SETINDEXQ" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "SETINDEXQ"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.SETINDEXQ

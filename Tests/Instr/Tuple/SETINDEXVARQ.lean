import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.SETINDEXVARQ

def suite : InstrSuite where
  id := { name := "SETINDEXVARQ" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "SETINDEXVARQ"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.SETINDEXVARQ

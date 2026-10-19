import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.SETINDEXVAR

def suite : InstrSuite where
  id := { name := "SETINDEXVAR" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "SETINDEXVAR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.SETINDEXVAR

import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.TUPLEVAR

def suite : InstrSuite where
  id := { name := "TUPLEVAR" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "TUPLEVAR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.TUPLEVAR

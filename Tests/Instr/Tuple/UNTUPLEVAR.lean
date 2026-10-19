import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.UNTUPLEVAR

def suite : InstrSuite where
  id := { name := "UNTUPLEVAR" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "UNTUPLEVAR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.UNTUPLEVAR

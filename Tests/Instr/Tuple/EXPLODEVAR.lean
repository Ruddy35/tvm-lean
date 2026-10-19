import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.EXPLODEVAR

def suite : InstrSuite where
  id := { name := "EXPLODEVAR" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "EXPLODEVAR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.EXPLODEVAR

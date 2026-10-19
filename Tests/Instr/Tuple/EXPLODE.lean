import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.EXPLODE

def suite : InstrSuite where
  id := { name := "EXPLODE" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "EXPLODE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.EXPLODE

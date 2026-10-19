import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.UNPACKFIRSTVAR

def suite : InstrSuite where
  id := { name := "UNPACKFIRSTVAR" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "UNPACKFIRSTVAR"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.UNPACKFIRSTVAR

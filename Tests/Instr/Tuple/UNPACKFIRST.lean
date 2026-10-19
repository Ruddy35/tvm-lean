import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.UNPACKFIRST

def suite : InstrSuite where
  id := { name := "UNPACKFIRST" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "UNPACKFIRST"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.UNPACKFIRST

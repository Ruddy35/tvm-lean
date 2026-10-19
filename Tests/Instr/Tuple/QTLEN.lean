import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.QTLEN

def suite : InstrSuite where
  id := { name := "QTLEN" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "QTLEN"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.QTLEN

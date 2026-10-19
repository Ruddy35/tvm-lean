import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.INDEX

def suite : InstrSuite where
  id := { name := "INDEX" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "INDEX"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.INDEX

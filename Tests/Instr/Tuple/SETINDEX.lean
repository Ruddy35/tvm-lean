import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.SETINDEX

def suite : InstrSuite where
  id := { name := "SETINDEX" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "SETINDEX"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.SETINDEX

import Tests.Harness.Registry
import Tests.Harness.Gen.Tuple
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.INDEXQ

def suite : InstrSuite where
  id := { name := "INDEXQ" }
  unit := #[]
  oracle := Tests.Gen.Tuple.casesFor "INDEXQ"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.INDEXQ

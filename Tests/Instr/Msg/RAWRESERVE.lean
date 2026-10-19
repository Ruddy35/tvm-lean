import Tests.Harness.Registry
import Tests.Harness.Gen.Msg
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.RAWRESERVE

def suite : InstrSuite where
  id := { name := "RAWRESERVE" }
  unit := #[]
  oracle := Tests.Gen.Msg.casesFor "RAWRESERVE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.RAWRESERVE

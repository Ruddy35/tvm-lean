import Tests.Harness.Registry
import Tests.Harness.Gen.Msg
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.SETCODE

def suite : InstrSuite where
  id := { name := "SETCODE" }
  unit := #[]
  oracle := Tests.Gen.Msg.casesFor "SETCODE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.SETCODE

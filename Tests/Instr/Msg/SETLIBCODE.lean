import Tests.Harness.Registry
import Tests.Harness.Gen.Msg
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.SETLIBCODE

def suite : InstrSuite where
  id := { name := "SETLIBCODE" }
  unit := #[]
  oracle := Tests.Gen.Msg.casesFor "SETLIBCODE"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.SETLIBCODE

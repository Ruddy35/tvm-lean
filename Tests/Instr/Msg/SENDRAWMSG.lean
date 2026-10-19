import Tests.Harness.Registry
import Tests.Harness.Gen.Msg
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.SENDRAWMSG

def suite : InstrSuite where
  id := { name := "SENDRAWMSG" }
  unit := #[]
  oracle := Tests.Gen.Msg.casesFor "SENDRAWMSG"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.SENDRAWMSG

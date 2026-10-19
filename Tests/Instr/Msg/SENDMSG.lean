import Tests.Harness.Registry
import Tests.Harness.Gen.Msg
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.SENDMSG

def suite : InstrSuite where
  id := { name := "SENDMSG" }
  unit := #[]
  oracle := Tests.Gen.Msg.casesFor "SENDMSG"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.SENDMSG

import Tests.Harness.Registry
import Tests.Harness.Gen.Msg
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.CHANGELIB

def suite : InstrSuite where
  id := { name := "CHANGELIB" }
  unit := #[]
  oracle := Tests.Gen.Msg.casesFor "CHANGELIB"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.CHANGELIB

import Tests.Harness.Registry
import Tests.Harness.Gen.Msg
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.RAWRESERVEX

def suite : InstrSuite where
  id := { name := "RAWRESERVEX" }
  unit := #[]
  oracle := Tests.Gen.Msg.casesFor "RAWRESERVEX"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.RAWRESERVEX

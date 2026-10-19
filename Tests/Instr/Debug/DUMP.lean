import Tests.Harness.Registry
import Tests.Harness.Gen.Control
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.DUMP

def suite : InstrSuite where
  id := { name := "DUMP" }
  unit := #[]
  oracle := Tests.Gen.Control.casesFor "DUMP"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.DUMP

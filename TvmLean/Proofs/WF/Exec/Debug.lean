import TvmLean.Proofs.WF.Step

/-!
# The Debug family keeps states well-formed

`execInstrDebug_WF : FamilyWF execInstrDebug`: the debug instructions (`DUMPSTK`, `STRDUMP`,
`DUMP`, `DEBUG`, `DEBUGSTR`, ...) do nothing in the model (C++ `runvmx` only logs them when
debugging is enabled), so they keep the state as it is.
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

theorem execInstrDebug_WF : FamilyWF execInstrDebug := by
  intro i next hi hnext
  mvcgen [execInstrDebug, hnext]
  all_goals wf_vc

end TvmLean

import TvmLean.Semantics.Exec.Dispatch
import TvmLean.Semantics.Step.Core

namespace TvmLean

def VmState.step (st : VmState) : StepResult :=
  st.stepWith execInstr

end TvmLean

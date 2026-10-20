import TvmLean.Semantics.Exec.Dispatch
import TvmLean.Semantics.Step.Core

namespace TvmLean

def VmState.step (host : Host) (st : VmState) : StepResult :=
  st.stepWith (execInstr host)

end TvmLean

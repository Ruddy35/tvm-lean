import TvmLean.Semantics.Step.Step

namespace TvmLean

def VmState.run (fuel : Nat) (st : VmState) : StepResult :=
  st.runWith execInstr fuel

end TvmLean

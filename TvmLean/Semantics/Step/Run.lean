import TvmLean.Semantics.Step.Step

namespace TvmLean

def VmState.run (host : Host) (fuel : Nat) (st : VmState) : StepResult :=
  st.runWith (execInstr host) fuel

end TvmLean

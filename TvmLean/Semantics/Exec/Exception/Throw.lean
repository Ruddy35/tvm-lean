import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrExceptionThrow (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .throw exc =>
      VM.throwToHandler fun st => st.throwException exc
  | _ => next

end TvmLean

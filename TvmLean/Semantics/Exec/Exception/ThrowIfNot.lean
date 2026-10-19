import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrExceptionThrowIfNot (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .throwIfNot exc =>
      let flag ← VM.popBool
      if flag then
        pure ()
      else
        VM.throwToHandler fun st => st.throwException exc
  | _ => next

end TvmLean

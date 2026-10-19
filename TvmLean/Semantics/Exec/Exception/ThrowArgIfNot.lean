import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrExceptionThrowArgIfNot (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .throwArgIfNot exc =>
      let cond ← VM.popBool
      if cond then
        let _ ← VM.pop
        pure ()
      else
        let arg ← VM.pop
        VM.throwToHandler fun st => st.throwExceptionArg exc arg
  | _ => next

end TvmLean

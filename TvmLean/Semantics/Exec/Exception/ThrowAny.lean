import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrExceptionThrowAny (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .throwAny hasParam hasCond throwCond =>
      -- C++ `exec_throw_any`: `check_underflow(1 + has_cond + has_param)` before the pops
      VM.checkUnderflow (1 + (if hasCond then 1 else 0) + (if hasParam then 1 else 0))
      let flag ←
        if hasCond then
          VM.popBool
        else
          pure throwCond
      let excnoNat ← VM.popNatUpTo 0xffff
      let excno : Int := Int.ofNat excnoNat
      if flag != throwCond then
        if hasParam then
          let _ ← VM.pop
          pure ()
        else
          pure ()
      else
        if hasParam then
          let arg ← VM.pop
          VM.throwToHandler fun st => st.throwExceptionArg excno arg
        else
          VM.throwToHandler fun st => st.throwException excno
  | _ => next

end TvmLean

import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvCommit (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .commit =>
      -- C++ `force_commit`: `try_commit` or cell_ov
      let (ok, st') := (← get).tryCommit
      if ok then
        set st'
      else
        throw .cellOv
  | _ => next

end TvmLean

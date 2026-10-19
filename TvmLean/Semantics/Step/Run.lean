import TvmLean.Semantics.Step.Step

namespace TvmLean

def VmState.run (host : Host) (fuel : Nat) (st : VmState) : StepResult :=
  match fuel with
  | 0 => .halt (Excno.fatal.toInt) st
  | fuel + 1 =>
      match st.step host with
      | .continue st' => VmState.run host fuel st'
      | .halt exitCode st' =>
          -- C++ `run_inner`: after exit code 0 or 1 (`(res | 1) == -1`), `try_commit`.
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              -- C++: clear stack, push 0, return ~cell_ov on commit failure.
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

end TvmLean

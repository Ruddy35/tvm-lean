import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvInMsgParam (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.inMsgParam idx) =>
      -- Matches C++ `exec_get_in_msg_param` / `exec_get_var_in_msg_param` (tonops.cpp).
      -- Stack: ... -- ... value
      -- `get_param(st, inmsgparams_idx)` (tonops.cpp:169, 121-128): `c7[0]` as
      -- `as_tuple_range(255)` (stack.cpp:312-319), type_chk for more than 255 entries; the
      -- message's parameters `as_tuple()`, of any length.
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if 255 < params.size then
              throw .typeChk
            if 17 < params.size then
              match params[17]! with
              | .tuple inMsgParams =>
                  if idx < inMsgParams.size then
                    VM.push (inMsgParams[idx]!)
                  else
                    throw .rangeChk
              | _ =>
                  throw .typeChk
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | _ => next

end TvmLean

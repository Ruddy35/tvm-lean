import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetParam (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.getParam idx) =>
      -- C++ `get_param` (tonops.cpp:121-128): `c7[0]` as `as_tuple_range(255)` (stack.cpp:312-319),
      -- type_chk for a tuple of more than 255 entries; then `tuple_index`, range_chk past its end.
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if 255 < params.size then
              throw .typeChk
            if idx < params.size then
              VM.push (params[idx]!)
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | _ => next

end TvmLean

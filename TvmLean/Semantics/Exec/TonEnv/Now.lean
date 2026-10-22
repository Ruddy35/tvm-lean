import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvNow (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .now =>
      -- NOW is `GETPARAM 3` in the TON opcode table; it reads `c7[0]` as the "params" tuple
      -- (`get_param`, tonops.cpp:121-128: `as_tuple_range(255)`, stack.cpp:312-319, type_chk for a
      -- tuple of more than 255 entries).
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
          if 255 < params.size then
            throw .typeChk
          if 3 < params.size then
            VM.push (params[3]!)
          else
            throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | _ => next

end TvmLean

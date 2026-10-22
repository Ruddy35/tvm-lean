import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetPrecompiledGas (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getPrecompiledGas =>
      -- Same semantics as `GETPARAM 16` in the TON opcode table (`get_param(st, 16)`,
      -- tonops.cpp:343-348, 121-128: `as_tuple_range(255)`, stack.cpp:312-319, type_chk for a
      -- tuple of more than 255 entries).
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if 255 < params.size then
              throw .typeChk
            if 16 < params.size then
              VM.push (params[16]!)
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | _ => next

end TvmLean

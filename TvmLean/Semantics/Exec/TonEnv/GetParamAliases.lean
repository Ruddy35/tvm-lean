import TvmLean.Semantics.Exec.Common

namespace TvmLean

/-- C++ `get_param(st, idx)` pushed (tonops.cpp:121-128): `c7[0]` as `as_tuple_range(255)`
(stack.cpp:312-319), type_chk for a tuple of more than 255 entries; then `tuple_index`, range_chk
past its end. -/
def VM.pushC7Param (idx : Nat) : VM Unit := do
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

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetParamAliases (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .blockLt => VM.pushC7Param 4
  | .tonEnvOp .lTime => VM.pushC7Param 5
  | .tonEnvOp .randSeed => VM.pushC7Param 6
  | .tonEnvOp .myAddr => VM.pushC7Param 8
  | .tonEnvOp .configRoot => VM.pushC7Param 9
  | .tonEnvOp .myCode => VM.pushC7Param 10
  | .tonEnvOp .incomingValue => VM.pushC7Param 11
  | .tonEnvOp .storageFees => VM.pushC7Param 12
  | .tonEnvOp .prevBlocksInfoTuple => VM.pushC7Param 13
  | .tonEnvOp .unpackedConfigTuple => VM.pushC7Param 14
  | .tonEnvOp .duePayment => VM.pushC7Param 15
  | _ => next

end TvmLean

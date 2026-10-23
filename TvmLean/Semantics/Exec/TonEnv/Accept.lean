import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvAccept (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .accept =>
      let st ← get
      -- C++ `exec_accept` (tonops.cpp:82-85): `exec_set_gas_generic` with `GasLimits::infty`, never
      -- below the gas consumed (a `long long`), so the limit changes
      let st' := { st with gas := st.gas.changeLimit GasLimits.infty }
      set st'
  | _ => next

end TvmLean

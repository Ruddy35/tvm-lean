import TvmLean.Proofs.Exec.Spec.TonEnv

/-!
# Specification: `GLOBALID` from version 6

`GLOBALID` (C++ `exec_get_global_id`, tonops.cpp:277-304) from version 6: the global id is the
first 32 bits (signed) of entry 1 of the unpacked configuration (`c7[0][14]`, each tuple at most
255 entries, `VM.getUnpackedConfigTuple`), a slice; cell_und if it is shorter. Before version 6 the
model reads it from the configuration dictionary (entry 19), which this file does not cover.
-/

namespace TvmLean.Spec

/-- `GLOBALID` from version 6, entry 1 of the unpacked configuration the slice `cs`. -/
@[vm_spec] theorem globalId (st : VmState) (params unpacked : Array Value) (cs : Slice)
    (hv : 6 ≤ st.globalVersion) (hc7 : st.regs.c7[0]? = some (.tuple params)) (hp : params.size ≤ 255)
    (h14 : params[14]? = some (.tuple unpacked)) (hu : unpacked.size ≤ 255)
    (h1 : unpacked[1]? = some (.slice cs)) :
    ExceptT.run (execInstr (.tonEnvOp .globalId)) st =
      if cs.haveBits 32 then
        (.ok (), { st with stack := st.stack.push (.int (.num (bitsToIntSignedTwos (cs.readBits 32)))) })
      else (.error .cellUnd, st) := by
  have hp' : ¬ 255 < params.size := by omega
  have hu' : ¬ 255 < unpacked.size := by omega
  vm_simp [hv, VM.getUnpackedConfigTuple, hc7, hp', h14, hu', h1]

end TvmLean.Spec

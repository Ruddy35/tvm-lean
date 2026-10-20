import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.TonEnv.GetParamAliases

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGlobalId (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .globalId =>
      -- Matches C++ `exec_get_global_id` (tonops.cpp:277-304).
      if (← get).globalVersion ≥ 6 then
        let unpacked ← VM.getUnpackedConfigTuple
        match unpacked[1]? with
        | none => throw .rangeChk
        | some (Value.slice cs) =>
            if !cs.haveBits 32 then
              throw .cellUnd
            let gid : Int := bitsToIntSignedTwos (cs.readBits 32)
            VM.pushSmallInt gid
        | some _ => throw .typeChk
      else
        -- Before version 6: parameter 19 of `c7` is taken as the configuration dictionary
        -- (`get_param(st, 19)`, type_chk if not a cell); its entry 19 (`lookup_ref`, which charges
        -- the nodes it loads) is loaded, and the global id is its first 32 bits; a missing entry
        -- or a shorter one is `unknown`.
        VM.pushC7Param 19
        let config ← match (← VM.pop) with
          | .cell c => pure c
          | _ => throw .typeChk
        let keyBits : BitString := natToBits 19 32
        let entry : Cell ←
          match dictLookupWithCells (resolve := (← VM.cellResolver)) (some config) keyBits with
          | .error e =>
              for c in dictLookupVisitedCells (resolve := (← VM.cellResolver)) (some config) keyBits do
                VM.registerCellLoad c
              throw e
          | .ok (none, loaded) =>
              for c in loaded do
                VM.registerCellLoad c
              throw .unknown
          | .ok (some valueSlice, loaded) =>
              for c in loaded do
                VM.registerCellLoad c
              -- `extract_value_ref`: the value must be exactly one reference
              if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
                pure valueSlice.cell.refs[valueSlice.refPos]!
              else
                throw .dictErr
        let cs ← VM.loadCellSlice entry
        if !cs.haveBits 32 then
          throw .unknown
        VM.pushSmallInt (bitsToIntSignedTwos (cs.readBits 32))
  | _ => next

end TvmLean

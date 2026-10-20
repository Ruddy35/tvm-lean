import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.TonEnv.GetParamAliases

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvConfigParam (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.configParam opt) =>
      -- Mirrors C++ `exec_get_config_param` (tonops.cpp).
      let idxVal ← VM.popInt
      VM.pushC7Param 9
      let dictRoot? ← VM.popMaybeCell
      -- `idx->export_bits(key, 32, true)`: a signed 32-bit key; out of range or NaN: not found
      let keyBits? : Option BitString :=
        match idxVal with
        | .nan => none
        | .num n => dictKeyBits? n 32 false
      match keyBits? with
      | none =>
          if opt then
            VM.push .null
          else
            VM.pushSmallInt 0
      | some keyBits =>
          match dictLookupWithCells (resolve := (← VM.cellResolver)) dictRoot? keyBits with
          | .error e =>
              -- `Dictionary::lookup_ref` charges the nodes it loads before the malformed one
              for c in dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictRoot? keyBits do
                VM.registerCellLoad c
              throw e
          | .ok (none, loaded) =>
              for c in loaded do
                VM.registerCellLoad c
              if opt then
                VM.push .null
              else
                VM.pushSmallInt 0
          | .ok (some valueSlice, loaded) =>
              for c in loaded do
                VM.registerCellLoad c
              if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
                let c := valueSlice.cell.refs[valueSlice.refPos]!
                if opt then
                  VM.push (.cell c)
                else
                  VM.push (.cell c)
                  VM.pushSmallInt (-1)
              else
                throw .dictErr
  | _ => next

end TvmLean


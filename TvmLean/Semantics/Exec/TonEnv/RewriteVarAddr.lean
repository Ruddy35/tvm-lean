import TvmLean.Semantics.Exec.Common

namespace TvmLean

/-- C++ `do_rewrite_addr` (tonops.cpp:1837-1853): the address with its first bits replaced by the
anycast prefix; the second component tells whether a new cell was built for it (`CellBuilder::
finalize` and `load_cell_slice_ref`, charged by the caller), which happens when the prefix is
non-empty and shorter than the address. -/
def rewriteMessageAddr (addr : Slice) (pfxVal : Value) : Except Excno (Slice × Bool) := do
  match pfxVal with
  | .null =>
      return (addr, false)
  | .slice pfx =>
      let pLen : Nat := pfx.bitsRemaining
      if pLen = 0 then
        return (addr, false)
      let aLen : Nat := addr.bitsRemaining
      if pLen > aLen then
        throw .cellUnd
      if pLen = aLen then
        return (pfx, false)
      let pBits := pfx.readBits pLen
      let aBits := addr.readBits aLen
      let newBits := pBits ++ aBits.drop pLen
      return (Slice.ofCell (Cell.mkOrdinary newBits #[]), true)
  | _ =>
      throw .cellUnd

set_option maxHeartbeats 1000000 in
def execInstrTonEnvRewriteVarAddr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.rewriteVarAddr quiet) =>
      let csr0 ← VM.popSlice
      let gv : Nat := (← get).globalVersion
      let parsed : Except Excno (Int × Slice × Bool) := do
        let (tup, rest) ← csr0.parseMessageAddr gv
        if rest.bitsRemaining != 0 || rest.refsRemaining != 0 then
          throw .cellUnd
        if tup.size != 4 then
          throw .cellUnd
        match tup[0]!, tup[1]!, tup[2]!, tup[3]! with
        | .int (.num t), pfxVal, .int (.num wc), .slice addr =>
            if t != 2 && t != 3 then
              throw .cellUnd
            let (addr', built) ← rewriteMessageAddr addr pfxVal
            return (wc, addr', built)
        | _, _, _, _ =>
            throw .cellUnd
      match parsed with
      | .ok (wc, addr, built) =>
          if built then
            -- the new cell is created, then loaded (`vm::load_cell_slice_ref(cb.finalize())`)
            VM.chargeCellCreates 1
            VM.registerCellLoad addr.cell
          VM.pushSmallInt wc
          VM.push (.slice addr)
          if quiet then
            VM.pushSmallInt (-1)
      | .error e =>
          if quiet then
            VM.pushSmallInt 0
          else
            throw e
  | _ => next

end TvmLean

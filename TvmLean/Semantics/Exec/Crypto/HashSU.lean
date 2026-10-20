import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCryptoHashSU (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cryptoOp .hashSU =>
      let s ← VM.popSlice
      -- C++ `HASHSU` builds a temporary cell from the slice and hashes it; `CellBuilder::finalize()`
      -- charges `cell_create_gas_price`.
      modify fun st => st.consumeGas cellCreateGasPrice
      let c := s.toCellRemaining
      -- `DataCell::create`: the slice of a Merkle proof (`XCTOS`) may have a reference deep at
      -- level 0, under which an ordinary cell is too deep
      VM.checkNewCellDepth c.refs
      let h := Cell.hashBytes c
      let n := bytesToNatBE h
      VM.pushIntQuiet (.num (Int.ofNat n)) false
  | _ => next

end TvmLean

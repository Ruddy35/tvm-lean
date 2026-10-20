import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackBlkSwapX (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .blkSwapX =>
      VM.checkUnderflow 2
      let y ← VM.popStackCount
      let x ← VM.popStackCount
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        if x > 0 && y > 0 then
          -- C++ charges the entries over 255 from version 4 (stackops.cpp:443-445)
          if total > 255 ∧ st.globalVersion ≥ 4 then
            modify fun st => st.consumeGas (Int.ofNat (total - 255))
          let st ← get
          let n := st.stack.size
          let front := st.stack.take (n - total)
          let below := st.stack.extract (n - total) (n - y)
          let top := st.stack.extract (n - y) n
          set { st with stack := front ++ top ++ below }
        else
          pure ()
      else
        throw .stkUnd
  | _ => next

end TvmLean

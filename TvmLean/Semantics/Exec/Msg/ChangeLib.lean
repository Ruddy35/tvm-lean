import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrMsgChangeLib (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .changeLib =>
      -- Mirrors C++ `exec_change_lib` (tonops.cpp:2427-2438): from version 4 the mode is in
      -- {0,1,2} ∪ {16,17,18}, other values up to 31 are rangeChk; before, it is up to 2.
      -- C++ checks the depth first: with one value on the stack it is stk_und, not range_chk.
      VM.checkUnderflow 2
      let mode ←
        if (← get).globalVersion ≥ 4 then
          let mode ← VM.popNatUpTo 31
          if (mode &&& 0x0f) > 2 then
            throw .rangeChk
          pure mode
        else
          VM.popNatUpTo 2
      let hash ← VM.popIntFinite
      if decide (hash < 0 ∨ hash ≥ intPow2 256) then
        throw .rangeChk
      modify fun st => st.consumeGas cellCreateGasPrice
      let st ← get
      let prev := st.regs.c5
      let modeByte : Nat := mode * 2
      let bits :=
        natToBits 0x26fa1dd4 32 ++
        natToBits modeByte 8 ++
        natToBits hash.toNat 256
      let newHead : Cell := Cell.mkOrdinary bits #[prev]
      -- `install_output_action(st, cb.finalize())`
      VM.checkNewCellDepth newHead.refs
      set { st with regs := { st.regs with c5 := newHead } }
  | _ => next

end TvmLean


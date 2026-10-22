import TvmLean.Proofs.WF.Exec.Stack
import TvmLean.Proofs.WF.Exec.Arith
import TvmLean.Proofs.WF.Exec.Cell
import TvmLean.Proofs.WF.Exec.CellOp
import TvmLean.Proofs.WF.Exec.Cont
import TvmLean.Proofs.WF.Exec.Flow
import TvmLean.Proofs.WF.Exec.Msg
import TvmLean.Proofs.WF.Exec.Exception
import TvmLean.Proofs.WF.Exec.Debug
import TvmLean.Proofs.WF.Exec.Tuple
import TvmLean.Proofs.WF.Exec.Misc
import TvmLean.Proofs.WF.Exec.TonEnv
import TvmLean.Proofs.WF.Exec.Crypto
import TvmLean.Proofs.WF.Exec.Dict

/-!
# Every step of the VM keeps the state well-formed

The obligations of `execInstr_WF` (`Step.lean`), one per instruction family, are all discharged
(`TvmLean/Proofs/WF/Exec/`); the Flow family takes the families a `RUNVM` child runs besides its
own. Hence, with no hypothesis left: every instruction keeps `VmState.WF` (`execInstr_keepsWF`),
and so do a step of the VM (`VmState.WF.step'`) and a run (`VmState.WF.run'`), the commit of c4 and
c5 included.
-/

namespace TvmLean

/-- Every instruction keeps the VM state well-formed. -/
theorem execInstr_keepsWF : ExecWF execInstr :=
  execInstr_WF execInstrStack_WF execInstrCont_WF execInstrCell_WF
    (execInstrFlow_WF execInstrTuple_WF execInstrTonEnv_WF execInstrCrypto_WF execInstrMisc_WF
      execInstrDebug_WF execInstrException_WF execInstrDict_WF)
    execInstrArith_WF execInstrTuple_WF execInstrCellOp_WF execInstrTonEnv_WF execInstrCrypto_WF
    execInstrMsg_WF execInstrMisc_WF execInstrDebug_WF execInstrException_WF execInstrDict_WF

/-- A step of the VM keeps the state well-formed. -/
theorem VmState.WF.step' {st : VmState} (h : st.WF) : st.step.state.WF :=
  h.step execInstr_keepsWF

/-- A run of the VM keeps the state well-formed. -/
theorem VmState.WF.run' (fuel : Nat) {st : VmState} (h : st.WF) : (st.run fuel).state.WF :=
  VmState.WF.run execInstr_keepsWF fuel h

end TvmLean

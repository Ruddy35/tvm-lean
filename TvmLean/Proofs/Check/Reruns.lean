import TvmLean.Proofs.Contracts.Wallet3Run.Tactic
import TvmLean.Proofs.Exec.Spec.SendMsg

/-!
# A step run again with libraries refused, in symbolic execution

With `max_library_loads` set, `VmState.stepWith` runs a step again with the libraries C++ refuses
(those the run notes in `librariesMissed`) until a run notes none (`VmState.stepRefusingWith`).
Symbolic execution writes the step as `VmState.stepFinish` of its run, which is the run itself when
the run notes no refused library (`VmState.stepFinish_continue`, `VmState.stepFinish_halt`: every
instruction whose loads are known). The run of `SENDMSG` is a term (`sendMsgRun`), and so are the
refusals it notes; for a step that ends with them:

* `VmState.stepFinish_continue_sendMsg`, `VmState.stepFinish_halt_sendMsg`: `stepFinish` written
  out, the cases of `max_library_loads` and of the refusals noted, which the run splits on;
* the steps run again are one run with the libraries they end with refused (`VmState.refusedAfter`,
  a term), its notes cleared (`VmState.stepRefusingWith_eq`): one more run of the instruction, not
  one per run again.

The two lemmas of `vm_run` apply only to a state whose refusals noted are those of a run of
`SENDMSG` (its field `librariesMissed` written out); any other `stepFinish` that `stepFinish_continue`
and `stepFinish_halt` do not rewrite at once is left as it is. Stated for every state (after those
two, at a low priority), they would also rewrite the steps of other instructions whose refusals the
discharger does not show to be none at once, and run them again: contract-check of the wallets v2
and v3 took 44% and 30% longer so.
-/

namespace TvmLean

/-- The libraries refused in the last run of `VmState.stepRefusingWith exec st refused n`: `refused`,
and those each run notes while a run notes some, at most `n` times again. -/
def VmState.refusedAfter (exec : Instr → VM Unit) (st : VmState) : Array BitString → Nat → Array BitString
  | refused, 0 => refused
  | refused, n + 1 =>
      if (VmState.stepOnceWith exec { st with librariesRefused := refused, librariesMissed := #[] }).state.librariesMissed.isEmpty
      then refused
      else VmState.refusedAfter exec st
        (refused ++ (VmState.stepOnceWith exec { st with librariesRefused := refused, librariesMissed := #[] }).state.librariesMissed) n

/-- **The step run again** (`VmState.stepRefusingWith`): the run with the libraries it ends with
refused (`VmState.refusedAfter`), its notes of libraries cleared. -/
theorem VmState.stepRefusingWith_eq (exec : Instr → VM Unit) (st : VmState) (refused : Array BitString)
    (n : Nat) :
    st.stepRefusingWith exec refused n =
      (VmState.stepOnceWith exec { st with librariesRefused := st.refusedAfter exec refused n, librariesMissed := #[] }).mapState
        fun st => { st with librariesRefused := #[], librariesMissed := #[] } := by
  induction n generalizing refused with
  | zero => rfl
  | succ n ih =>
    unfold VmState.stepRefusingWith VmState.refusedAfter
    dsimp only
    split
    · rfl
    · rw [ih]

/-- `VmState.stepFinish` of a step that continues in a state whose refusals noted are those of the
run of `SENDMSG` from `t` (`sendMsgRun t`), written out: the step itself without
`max_library_loads`; else the state with its notes cleared if the run noted none, else the step run
again with the libraries refused (`VmState.stepRefusingWith_eq`). -/
@[vm_run] theorem VmState.stepFinish_continue_sendMsg (exec : Instr → VM Unit) (st t : VmState)
    (stack : Stack) (regs : Regs) (cc : Continuation) (cp : Int) (gas : GasLimits) (chk : Nat)
    (lc : Array (Array UInt8)) (libs : Array Cell) (cs : Array CallFrame) (cst : CommittedState)
    (mdd gv : Nat) (fgc : Int) (gebc cj steps : Nat) (mll : Option Nat) (ll lr : Array BitString) :
    VmState.stepFinish exec st (.continue
      { stack := stack, regs := regs, cc := cc, cp := cp, gas := gas, chksgnCounter := chk,
        loadedCells := lc, libraries := libs, callStack := cs, cstate := cst, maxDataDepth := mdd,
        globalVersion := gv, freeGasConsumed := fgc, getExtraBalanceCounter := gebc, chainJumps := cj,
        steps := steps, maxLibraryLoads := mll, loadedLibraries := ll, librariesRefused := lr,
        librariesMissed := (sendMsgRun t).2.librariesMissed }) =
      if st.maxLibraryLoads.isNone then .continue
        { stack := stack, regs := regs, cc := cc, cp := cp, gas := gas, chksgnCounter := chk,
          loadedCells := lc, libraries := libs, callStack := cs, cstate := cst, maxDataDepth := mdd,
          globalVersion := gv, freeGasConsumed := fgc, getExtraBalanceCounter := gebc, chainJumps := cj,
          steps := steps, maxLibraryLoads := mll, loadedLibraries := ll, librariesRefused := lr,
          librariesMissed := (sendMsgRun t).2.librariesMissed }
      else if (sendMsgRun t).2.librariesMissed.isEmpty then .continue
        { stack := stack, regs := regs, cc := cc, cp := cp, gas := gas, chksgnCounter := chk,
          loadedCells := lc, libraries := libs, callStack := cs, cstate := cst, maxDataDepth := mdd,
          globalVersion := gv, freeGasConsumed := fgc, getExtraBalanceCounter := gebc, chainJumps := cj,
          steps := steps, maxLibraryLoads := mll, loadedLibraries := ll, librariesRefused := #[],
          librariesMissed := #[] }
      else (VmState.stepOnceWith exec { st with
          librariesRefused := st.refusedAfter exec (#[] ++ (sendMsgRun t).2.librariesMissed) 7,
          librariesMissed := #[] }).mapState
        fun st => { st with librariesRefused := #[], librariesMissed := #[] } := by
  unfold VmState.stepFinish
  rw [VmState.stepRefusingWith_eq]
  try rfl

/-- `VmState.stepFinish_continue_sendMsg` for a step that halts. -/
@[vm_run] theorem VmState.stepFinish_halt_sendMsg (exec : Instr → VM Unit) (st t : VmState) (ec : Int)
    (stack : Stack) (regs : Regs) (cc : Continuation) (cp : Int) (gas : GasLimits) (chk : Nat)
    (lc : Array (Array UInt8)) (libs : Array Cell) (cs : Array CallFrame) (cst : CommittedState)
    (mdd gv : Nat) (fgc : Int) (gebc cj steps : Nat) (mll : Option Nat) (ll lr : Array BitString) :
    VmState.stepFinish exec st (.halt ec
      { stack := stack, regs := regs, cc := cc, cp := cp, gas := gas, chksgnCounter := chk,
        loadedCells := lc, libraries := libs, callStack := cs, cstate := cst, maxDataDepth := mdd,
        globalVersion := gv, freeGasConsumed := fgc, getExtraBalanceCounter := gebc, chainJumps := cj,
        steps := steps, maxLibraryLoads := mll, loadedLibraries := ll, librariesRefused := lr,
        librariesMissed := (sendMsgRun t).2.librariesMissed }) =
      if st.maxLibraryLoads.isNone then .halt ec
        { stack := stack, regs := regs, cc := cc, cp := cp, gas := gas, chksgnCounter := chk,
          loadedCells := lc, libraries := libs, callStack := cs, cstate := cst, maxDataDepth := mdd,
          globalVersion := gv, freeGasConsumed := fgc, getExtraBalanceCounter := gebc, chainJumps := cj,
          steps := steps, maxLibraryLoads := mll, loadedLibraries := ll, librariesRefused := lr,
          librariesMissed := (sendMsgRun t).2.librariesMissed }
      else if (sendMsgRun t).2.librariesMissed.isEmpty then .halt ec
        { stack := stack, regs := regs, cc := cc, cp := cp, gas := gas, chksgnCounter := chk,
          loadedCells := lc, libraries := libs, callStack := cs, cstate := cst, maxDataDepth := mdd,
          globalVersion := gv, freeGasConsumed := fgc, getExtraBalanceCounter := gebc, chainJumps := cj,
          steps := steps, maxLibraryLoads := mll, loadedLibraries := ll, librariesRefused := #[],
          librariesMissed := #[] }
      else (VmState.stepOnceWith exec { st with
          librariesRefused := st.refusedAfter exec (#[] ++ (sendMsgRun t).2.librariesMissed) 7,
          librariesMissed := #[] }).mapState
        fun st => { st with librariesRefused := #[], librariesMissed := #[] } := by
  unfold VmState.stepFinish
  rw [VmState.stepRefusingWith_eq]
  try rfl

end TvmLean

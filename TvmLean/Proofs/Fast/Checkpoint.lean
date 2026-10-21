import TvmLean.Proofs.Fast.Run

/-!
# Checkpoints: long runs in segments

The kernel keeps everything it evaluated until the declaration it checks ends, so the memory of a
run by kernel evaluation grows with its length. A run can be cut into segments, each checked in its
own declaration: `VmState.stepsC k s = some s'` (`k` steps from `s`, none of which halts, end in `s'`)
gives `VmState.run (k + n) s = VmState.run n s'` (`VmState.run_of_stepsC`), and the next segment
starts from `s'` written out as a term.

`fast_checkpoint s' := VmState.stepsC k s` evaluates the steps natively (the compiled model), defines
`s'` as the resulting state written out (`ToExpr`), and proves `s'.eq : VmState.stepsC k s = some s'`
by kernel evaluation over the fast twins (`fastRflProof`): the native evaluation only finds the
state, the kernel checks it.
-/

namespace TvmLean

open Lean Meta Elab Command

deriving instance ToExpr for IntVal
deriving instance ToExpr for Cell
deriving instance ToExpr for Slice
deriving instance ToExpr for Builder
deriving instance ToExpr for Value, Continuation, OrdCregs, OrdCdata
deriving instance ToExpr for Regs
deriving instance ToExpr for GasLimits
deriving instance ToExpr for CommittedState
deriving instance ToExpr for CallFrame
deriving instance ToExpr for VmState

/-- `k` steps of `VmState.step`, none of which halts: the state after them (`none` if the VM halts
within them). -/
def VmState.stepsC : Nat → VmState → Option VmState
  | 0, s => some s
  | k + 1, s =>
    match s.step with
    | .continue s' => VmState.stepsC k s'
    | .halt _ _ => none

/-- A run is its first `k` steps, when none of them halts, then the rest. -/
theorem VmState.run_of_stepsC : ∀ (k n : Nat) (s s' : VmState), VmState.stepsC k s = some s' →
    VmState.run (k + n) s = VmState.run n s'
  | 0, n, s, s', h => by
    simp only [VmState.stepsC, Option.some.injEq] at h
    subst h
    simp
  | k + 1, n, s, s', h => by
    simp only [VmState.stepsC] at h
    split at h
    · rename_i s1 hs
      rw [show k + 1 + n = (k + n) + 1 by omega]
      show VmState.runWith execInstr ((k + n) + 1) s = _
      rw [VmState.runWith, show s.stepWith execInstr = s.step from rfl, hs]
      exact VmState.run_of_stepsC k n s1 s' h
    · simp at h

namespace Fast

unsafe def evalStepsUnsafe (e : Expr) : MetaM (Option VmState) :=
  evalExpr (Option VmState) (mkApp (mkConst ``Option [levelZero]) (mkConst ``VmState)) e

/-- Native evaluation of an `Option VmState` term (the compiled model). -/
@[implemented_by evalStepsUnsafe]
opaque evalSteps (e : Expr) : MetaM (Option VmState)

/-- `fast_checkpoint s' := e`: `e : Option VmState` (`VmState.stepsC k s`) evaluated natively to
`some st`; defines `s' : VmState` as `st` written out and proves `s'.eq : e = some s'` by the kernel
over the fast twins. -/
elab "fast_checkpoint " id:ident " := " t:term : command => liftTermElabM do
  let ty := mkApp (mkConst ``Option [levelZero]) (mkConst ``VmState)
  let e ← Term.elabTermEnsuringType t ty
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let some st ← evalSteps e | throwError "fast_checkpoint: the VM halts within the steps"
  let name := (← getCurrNamespace) ++ id.getId
  let dv : DefinitionVal :=
    { name, levelParams := [], type := mkConst ``VmState, value := toExpr st, hints := .regular 0,
      safety := .safe }
  addAndCompile (.defnDecl dv)
  let stmt ← mkEq e (mkApp2 (mkConst ``Option.some [levelZero]) (mkConst ``VmState) (mkConst name))
  let pf ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) (fastRflProof stmt)
  addDecl <| .thmDecl { name := name ++ `eq, levelParams := [], type := stmt, value := pf }

end Fast

set_option Elab.async false

fast_twin TvmLean.VmState.stepsC

end TvmLean

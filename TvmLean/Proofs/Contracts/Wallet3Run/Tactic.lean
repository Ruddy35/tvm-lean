import TvmLean.Proofs.Exec.Tactic

/-!
# Runs from every state the compute phase starts from: what `vm_run` needs besides

`TvmLean/Proofs/Exec/Tactic.lean` runs code from a state written out. The compute phase of a
transaction (`TvmLean.Tx.VmStart`, `TvmLean/Proofs/Tx/Compute.lean`) may start the VM with any gas
limits, any `max_library_loads` and an action list that grows in a loop; this module adds what a run
from such a state needs:

* `VmState.stepFinish`: `VmState.stepWith` of a state between steps is `stepFinish` of its step
  (`VmState.stepWith_finish`, a pre-rewrite for `vm_run`), which goes into the cases of the step
  (`stepFinish_ite`) and is the step itself on a state that notes no refused library
  (`stepFinish_continue`, `stepFinish_halt`): the step of a run whatever `max_library_loads` is
  (C++ `VmState::load_library`, vm.cpp:644-656, refuses only libraries, and only libraries are
  noted).
* `GasLimits.changeLimit_infty_min`: the gas limits after `ACCEPT` for any gas maximum (the limit
  becomes `min gasMax (2^63 - 1)`, C++ `GasLimits::change_limit`, vm.h).
* `SendList`: an action list of `SENDRAWMSG` actions only (`OutAction.sendMsg`), from the empty list.
* `vm_loop_c5 Q` and `vm_loop_close_c5`: the loop rule of `vm_loop` with the invariant `Q` of the
  action list `c5` added (closed at the loop head by `vm_c5_close`), so that what a loop adds to
  `c5` is known after it.
-/

namespace TvmLean

/-! ## A step whatever `max_library_loads` is -/

/-- What `VmState.stepWith` makes of the step `r` from `st` (`VmState.stepOnceWith`): `r`, unless
`max_library_loads` is set and `r` noted a library C++ refuses (then the step again). -/
def VmState.stepFinish (exec : Instr → VM Unit) (st : VmState) (r : StepResult) : StepResult :=
  if st.maxLibraryLoads.isNone then r
  else if r.state.librariesMissed.isEmpty then
    r.mapState fun st => { st with librariesRefused := #[], librariesMissed := #[] }
  else st.stepRefusingWith exec (#[] ++ r.state.librariesMissed) 7

/-- `VmState.stepWith` on a state between steps (no library refused or noted) is `stepFinish` of
the step. -/
theorem VmState.stepWith_finish (exec : Instr → VM Unit) (st : VmState)
    (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[]) :
    st.stepWith exec = VmState.stepFinish exec st (st.stepOnceWith exec) := by
  rw [VmState.stepWith_unfold exec st hr hm]
  rfl

theorem VmState.stepFinish_continue (exec : Instr → VM Unit) (st s : VmState)
    (hr : s.librariesRefused = #[]) (hm : s.librariesMissed = #[]) :
    VmState.stepFinish exec st (.continue s) = .continue s := by
  unfold VmState.stepFinish
  split
  · rfl
  · simp only [StepResult.state, hm, Array.isEmpty_empty, if_true, StepResult.mapState,
      VmState.with_libraries_self s hr hm]

theorem VmState.stepFinish_halt (exec : Instr → VM Unit) (st s : VmState) (ec : Int)
    (hr : s.librariesRefused = #[]) (hm : s.librariesMissed = #[]) :
    VmState.stepFinish exec st (.halt ec s) = .halt ec s := by
  unfold VmState.stepFinish
  split
  · rfl
  · simp only [StepResult.state, hm, Array.isEmpty_empty, if_true, StepResult.mapState,
      VmState.with_libraries_self s hr hm]

theorem VmState.stepFinish_ite (exec : Instr → VM Unit) (st : VmState) (c : Prop) [Decidable c]
    (a b : StepResult) :
    VmState.stepFinish exec st (if c then a else b) =
      if c then VmState.stepFinish exec st a else VmState.stepFinish exec st b := by
  split <;> rfl

theorem VmState.stepFinish_dite (exec : Instr → VM Unit) (st : VmState) (c : Prop) [Decidable c]
    (a : c → StepResult) (b : ¬c → StepResult) :
    VmState.stepFinish exec st (if h : c then a h else b h) =
      if h : c then VmState.stepFinish exec st (a h) else VmState.stepFinish exec st (b h) := by
  split <;> rfl

/-! ## `ACCEPT` for any gas maximum -/

/-- The gas limits after `ACCEPT` (`GasLimits.changeLimit` to `GasLimits.infty` = 2^63 - 1, stated as
the literal): limit and base become `min gasMax (2^63 - 1)`, the credit 0, and the gas left grows by
the difference of the bases. -/
theorem GasLimits.changeLimit_infty_min (g : GasLimits) :
    g.changeLimit GasLimits.infty =
      { g with gasCredit := 0, gasLimit := min g.gasMax 9223372036854775807,
               gasRemaining := g.gasRemaining + (min g.gasMax 9223372036854775807 - g.gasBase),
               gasBase := min g.gasMax 9223372036854775807 } := by
  have hi : GasLimits.infty = 9223372036854775807 := by decide
  have h0 : ¬ (GasLimits.infty < 0) := by rw [hi]; decide
  have hl : (if GasLimits.infty > g.gasMax then g.gasMax else GasLimits.infty) =
      min g.gasMax 9223372036854775807 := by
    rw [hi]; split <;> omega
  simp only [GasLimits.changeLimit, GasLimits.changeBase, h0, if_false, hl]

/-! ## Action lists of `SENDRAWMSG` actions -/

/-- An action list made of `SENDRAWMSG` actions only (`OutAction.sendMsg`), from the empty list. -/
inductive SendList : Cell → Prop
  | empty : SendList Cell.empty
  | send {prev : Cell} (mode : Nat) (msg : Cell) : SendList prev → SendList (OutAction.sendMsg mode prev msg)

/-- Closes `SendList c5` for the action list at a loop head or at the end of a run: the empty
list, a hypothesis, or a `SENDRAWMSG` added to a list of the hypotheses. -/
macro "vm_c5_close" : tactic => `(tactic| first
  | exact SendList.empty
  | assumption
  | (refine SendList.send _ _ ?_; assumption))

end TvmLean

namespace TvmLean.Exec

open Lean Meta Elab Tactic

/-- Proves `∃ x₁ ... xₙ, (S' = S[x] ∧ c) ∧ q` (the invariant of `vm_loop_c5`) by unification
(reducible), `c` (the jump counter) by `decide` or `omega`, `q` (the invariant of `c5`) by
`vm_c5_close`. -/
def solveInvC5 (g : MVarId) : TacticM Unit := do
  let mut g := g
  for _ in [0:64] do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    if ty.isAppOfArity ``Exists 2 then
      let α := ty.getArg! 0
      let p := ty.getArg! 1
      let w ← mkFreshExprMVar α
      let g' ← mkFreshExprMVar (mkApp p w).headBeta
      g.assign (← mkAppOptM ``Exists.intro #[α, p, w, g'])
      g := g'.mvarId!
    else
      unless ty.isAppOfArity ``And 2 do throwError "vm_loop_close_c5: not the invariant"
      let left := ty.getArg! 0
      let q := ty.getArg! 1
      unless left.isAppOfArity ``And 2 do throwError "vm_loop_close_c5: not the invariant"
      let eq := left.getArg! 0
      let c := left.getArg! 1
      let some (_, a, b) := eq.eq? | throwError "vm_loop_close_c5: not an equation"
      unless ← withReducible (isDefEq a b) do throwError "vm_loop_close_c5: the state is not the loop head"
      let hc ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars c)
      let r ← Tactic.run hc.mvarId! do
        evalTactic (← `(tactic| first | decide | (simp only [freeNestedContJump]; omega)))
      unless r.isEmpty do throwError "vm_loop_close_c5: the bound of the jump counter"
      let hq ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars q)
      let r ← Tactic.run hq.mvarId! do evalTactic (← `(tactic| vm_c5_close))
      unless r.isEmpty do throwError "vm_loop_close_c5: the invariant of c5"
      g.assign (← mkAppM ``And.intro #[← mkAppM ``And.intro #[← mkEqRefl a, hc], hq])
      return
  throwError "vm_loop_close_c5: too many parts"

end TvmLean.Exec

namespace TvmLean

open Lean Meta in
/-- `vm_loop_c5 Q`: `vm_loop` (`TvmLean/Proofs/Exec/Tactic.lean`) with the invariant `Q c5` of the
action list added: at the loop head `S`, the goal `P (S.runWith exec n)` by the loop rule
(`VmState.runWith_inv`) with the invariant "the state is `S` but for the gas, the loaded cells, the
counters of jumps (fewer than `freeNestedContJump`) and steps, `c5` (satisfying `Q`), and the payload
of the top stack entry". The invariant holds at `S` by `vm_c5_close`. Leaves the run out of fuel and
the run with one more step from such a state, with the hypothesis `ih`, which `vm_loop_close_c5`
applies when the run is back at the loop head. -/
elab "vm_loop_c5 " q:term : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_loop_c5: no run in the goal"
  let exec := r.getArg! 0
  let n := r.getArg! 1
  let S := r.getArg! 2
  let Q ← Lean.Elab.Tactic.elabTerm q (some (← mkArrow (mkConst ``Cell) (mkSort levelZero)))
  let (vals, fill, iChain) ← Exec.loopHoles S 1
  -- the holes: gas, loaded cells, jump counter, steps, then `c5`, then the top payload
  let iC5 := 4
  let tys ← vals.mapM fun v => (inferType v : MetaM Expr)
  let stTy := mkConst ``VmState
  let inv ← withLocalDeclD `st stTy fun st => do
    let decls := (List.range vals.size).toArray.map fun i =>
      (Name.mkSimple s!"x{i}", fun (_ : Array Expr) => pure tys[i]!)
    let body ← withLocalDeclsD decls fun xs => do
      let bound ← mkAppM ``LT.lt #[xs[iChain]!, mkConst ``freeNestedContJump]
      let mut e ← mkAppM ``And #[← mkAppM ``And #[← mkEq st (fill xs), bound], (mkApp Q xs[iC5]!).headBeta]
      for x in xs.reverse do
        e ← mkAppM ``Exists #[← mkLambdaFVars #[x] e]
      return e
    mkLambdaFVars #[st] body
  let motive ← withLocalDeclD `r (mkConst ``StepResult) fun rv => do
    mkLambdaFVars #[rv] ((← kabstract t r).instantiate1 rv)
  let hzTy ← withLocalDeclD `st stTy fun st => do
    mkForallFVars #[st] (← mkArrow (mkApp inv st).headBeta
      (mkApp motive (← mkAppM ``VmState.runWith #[exec, mkNatLit 0, st])).headBeta)
  let hz ← mkFreshExprSyntheticOpaqueMVar hzTy
  let hinv ← mkFreshExprMVar (mkApp inv S).headBeta
  Exec.solveInvC5 hinv.mvarId!
  let rule ← mkAppOptM ``VmState.runWith_inv #[exec, inv, motive, hz]
  let .forallE _ hsTy _ _ ← whnf (← inferType rule) | throwError "vm_loop_c5: the loop rule"
  let hs ← mkFreshExprSyntheticOpaqueMVar hsTy
  let pf ← mkAppOptM ``VmState.runWith_inv #[exec, inv, motive, hz, hs, n, S, hinv]
  unless ← isDefEq (← inferType pf) t do throwError "vm_loop_c5: the goal is not a property of the run"
  g.assign pf
  let (_, gz) ← hz.mvarId!.intro `st
  let (h0, gz) ← gz.intro `hinv
  let gz ← Exec.destructInv gz h0
  let (_, gs) ← hs.mvarId!.intro `n
  let (_, gs) ← gs.intro `st
  let (h1, gs) ← gs.intro `hinv
  let (_, gs) ← gs.intro `ih
  let gs ← Exec.destructInv gs h1
  Lean.Elab.Tactic.replaceMainGoal [gz, gs]

open Lean Meta in
/-- `vm_not_at_pos n`: fails if the run in the goal (`VmState.runWith exec fuel st`) is about to run
the code at bit `n` of a cell (the current continuation is an ordinary continuation on a slice
`⟨_, n, _⟩`), so that a run stops there (a cut of a proof into a run up to a code position and a
lemma about the runs from there). -/
elab "vm_not_at_pos " n:num : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let some st := Exec.runState? (← instantiateMVars (← g.getType)) | return
  let cc ← whnfCore (← whnfR (← mkAppM ``VmState.cc #[st]))
  unless cc.isAppOfArity ``Continuation.ordinary 4 do return
  let code ← whnfR (cc.getArg! 0)
  unless code.isAppOfArity ``Slice.mk 3 do return
  let pos ← whnfCore (← whnfR (code.getArg! 1))
  if pos.rawNatLit? == some n.getNat || pos.nat? == some n.getNat then
    throwError "vm_not_at_pos: at bit {n.getNat}"

open Lean Meta in
/-- `vm_loop_close_c5`: the run is back at the loop head of `vm_loop_c5`: by the hypothesis `ih`,
its fuel at most that of `ih` (`omega`), its state the loop head with other parts (unification), the
invariant of `c5` by `vm_c5_close`. -/
elab "vm_loop_close_c5" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let some d := (← getLCtx).findFromUserName? `ih | throwError "vm_loop_close_c5: no `ih`"
  let gs ← g.apply d.toExpr
  let mut rest := #[]
  for g' in gs do
    if ← g'.isAssigned then continue
    let ty ← whnfR (← instantiateMVars (← g'.getType))
    if ty.isAppOf ``LE.le then
      let r ← Lean.Elab.Tactic.run g' (do Lean.Elab.Tactic.evalTactic (← `(tactic| omega)))
      unless r.isEmpty do throwError "vm_loop_close_c5: the fuel"
    else if ty.isAppOf ``Exists then
      Exec.solveInvC5 g'
    else rest := rest.push g'
  Lean.Elab.Tactic.replaceMainGoal rest.toList

end TvmLean

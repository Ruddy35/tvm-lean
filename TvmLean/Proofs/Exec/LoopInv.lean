import TvmLean.Proofs.Exec.Tactic

/-!
# The loop rule with an invariant of the user

`vm_loop k` (`Proofs/Exec/Tactic.lean`) applies the loop rule (`VmState.runWith_inv`) at a loop
head with the invariant "the state is the loop head but for the gas, the loaded cells, the counters
of jumps and steps, `c5`, and the payloads of the top `k` stack entries": what the loop computes in
those entries is then unknown after it. `vm_loop k (inv := P)` adds a property `P` of the payloads
(the deepest of the `k` entries first): `P x₁ … xₖ` is a hypothesis of every iteration (so that
`vm_run` decides the loop's conditions with it, by `omega`) and of the exit, and is proved again
when an iteration comes back to the loop head (`vm_loop_close`, by `omega` or `decide`; else the
goal is left). At the loop head it is proved of the payloads there the same way, else left as a
goal (the first one).
-/

namespace TvmLean.Exec

open Lean Meta Elab Tactic

/-- `∃ x₁ … xₙ, S' = S[x] ∧ c`: the witnesses by unification (reducible), then `c` by `decide` or
`omega`; returns the goal of `c` if they fail. -/
def solveInvExistsOrLeave (g : MVarId) : TacticM (Option MVarId) := do
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
      let some (eq, c) := (if ty.isAppOfArity ``And 2 then some (ty.getArg! 0, ty.getArg! 1) else none)
        | throwError "vm_loop: not the invariant"
      let some (_, a, b) := eq.eq? | throwError "vm_loop: not an equation"
      unless ← withReducible (isDefEq a b) do throwError "vm_loop: the state is not the loop head"
      let hc ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars c)
      g.assign (← mkAppM ``And.intro #[← mkEqRefl a, hc])
      let r ← try
          Tactic.run hc.mvarId! do
            evalTactic (← `(tactic| first | decide | (simp only [freeNestedContJump]; omega)))
        catch _ => pure [hc.mvarId!]
      return r.head?
  throwError "vm_loop: too many parts"

/-- Splits the hypothesis `chainJumps < freeNestedContJump ∧ P ...` that `destructInv` leaves into
its two parts, so that the bound of the jump counter is a hypothesis of its own (the discharger
of `vm_step` finds it by `assumption`). -/
def splitUserInv (g : MVarId) : MetaM MVarId := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``And 2 then
      let a := ty.getArg! 0
      if a.isAppOfArity ``LT.lt 4 && (a.getArg! 3).isConstOf ``freeNestedContJump then
        let #[sg] ← g.cases d.fvarId | throwError "vm_loop: cases"
        return sg.mvarId
  return g

end TvmLean.Exec

namespace TvmLean

open Lean Meta in
/-- `vm_loop k (inv := P)`: `vm_loop k` with the property `P x₁ … xₖ` of the payloads of the top
`k` stack entries (deepest first) added to the invariant. Leaves the goal of `P` at the loop head
if `decide`/`omega` do not prove it, then the run out of fuel and the run with one more step, both
from any state of the invariant (with `P` of its payloads as a hypothesis). -/
syntax (name := vmLoopInv) "vm_loop" (ppSpace num)? " (" &"inv" " := " term ")" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| vm_loop $[$k]? (inv := $p)) => withMainContext do
  let k := (k.map (·.getNat)).getD 1
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_loop: no run in the goal"
  let exec := r.getArg! 0
  let n := r.getArg! 1
  let S := r.getArg! 2
  let (vals, fill, iChain) ← Exec.loopHoles S k
  let tys ← vals.mapM fun v => (inferType v : MetaM Expr)
  -- the payload holes are the last `k`
  let nPay := k
  let firstPay := vals.size - nPay
  let mut expected : Expr := mkSort levelZero
  for i in (List.range nPay).reverse do
    expected := mkForall `x .default tys[firstPay + i]! expected
  let P ← Term.elabTermEnsuringType p expected
  Term.synthesizeSyntheticMVarsNoPostponing
  let P ← instantiateMVars P
  let stTy := mkConst ``VmState
  let inv ← withLocalDeclD `st stTy fun st => do
    let decls := (List.range vals.size).toArray.map fun i =>
      (Name.mkSimple s!"x{i}", fun (_ : Array Expr) => pure tys[i]!)
    let body ← withLocalDeclsD decls fun xs => do
      let bound ← mkAppM ``LT.lt #[xs[iChain]!, mkConst ``freeNestedContJump]
      let user := (mkAppN P (xs.extract firstPay xs.size)).headBeta
      let mut e ← mkAppM ``And #[← mkEq st (fill xs), ← mkAppM ``And #[bound, user]]
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
  let left ← Exec.solveInvExistsOrLeave hinv.mvarId!
  let rule ← mkAppOptM ``VmState.runWith_inv #[exec, inv, motive, hz]
  let .forallE _ hsTy _ _ ← whnf (← inferType rule) | throwError "vm_loop: the loop rule"
  let hs ← mkFreshExprSyntheticOpaqueMVar hsTy
  let pf ← mkAppOptM ``VmState.runWith_inv #[exec, inv, motive, hz, hs, n, S, hinv]
  unless ← isDefEq (← inferType pf) t do throwError "vm_loop: the goal is not a property of the run"
  g.assign pf
  let (_, gz) ← hz.mvarId!.intro `st
  let (h0, gz) ← gz.intro `hinv
  let gz ← Exec.splitUserInv (← Exec.destructInv gz h0)
  let (_, gs) ← hs.mvarId!.intro `n
  let (_, gs) ← gs.intro `st
  let (h1, gs) ← gs.intro `hinv
  let (_, gs) ← gs.intro `ih
  let gs ← Exec.splitUserInv (← Exec.destructInv gs h1)
  replaceMainGoal (left.toList ++ [gz, gs])

end TvmLean

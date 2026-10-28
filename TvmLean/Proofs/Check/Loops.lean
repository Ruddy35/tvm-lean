import TvmLean.Proofs.Check.Tactic

/-!
# Loops with an invariant of the user

A loop whose iterations change more than its top stack entry, `c5` and the counters (`check_loop`)
is run by `ran_case` with a loop invariant the invariant's file gives (`-- contract-check: loop k Q`,
`tools/contract-check`): at a loop head whose top `k` stack entries satisfy `Q`, the loop rule
(`runWith_invLe`) lets them be any values that satisfy `Q` (`check_loop_user`, through
`check_loop_any`); a path back at the head proves `Q` of the entries there (`check_loop_close_user`,
`solveInvUser`, `closeUserFact`), else it is reported. The syntax of `check_loop_any` and
`check_loop_close_user` is declared in TvmLean/Proofs/Check/Tactic.lean (`check_one_step` tries
them); their elaborators are here.
-/

namespace TvmLean.Check

open Lean Meta Elab Tactic

/-- With `check.debug`, a line of the progress log (`progressLine`) and the time since `t0`. -/
def debugLine (t0 : Nat) (s : String) : CoreM Unit := do
  if check.debug.get (← getOptions) then
    progressLine s!"  {s} ({(← IO.monoMsNow) - t0} ms)"

/-- `g` by the theorem `thm` (a hint: `Queries.set`), its hypotheses from the context: the equations
of results (`f … = .ok …`) first, by `assumption` (they fix the theorem's arguments), then the
others by `assumption`, the size of a key of an integer (`dictKeyBits?_size`), the first case of a
disjunction by `rfl`, `omega`; the hypotheses by `assumption` at reducible transparency (at the
default one, a hypothesis `dictDeleteWithLoads … = .ok …` against the goal `Dict.setSetRes ?r ?k …
= .ok …` unfolds the walks), all within a budget of heartbeats. Whether it closes `g` (nothing kept
if not). -/
def closeByHint (g : MVarId) (thm : Name) : TacticM Bool := do
  let s ← saveState
  tryCatchRuntimeEx (withCurrHeartbeats <|
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 100000 * 1000 }) do
    let gs ← g.apply (← mkConstWithFreshMVarLevels thm)
    let isResultEq (h : MVarId) : TacticM Bool := do
      let some (_, _, rhs) := (← instantiateMVars (← h.getType)).eq? | return false
      return rhs.isAppOf ``Except.ok
    let first ← gs.filterM isResultEq
    let rest ← gs.filterM fun h => return !(← isResultEq h)
    for h in first ++ rest do
      if ← h.isAssigned then continue
      let byHyp ← (do withReducible h.assumption; pure true) <|> pure false
      unless byHyp do
        let r ← tryTac h (← `(tactic| first
          | exact dictKeyBits?_size (by assumption)
          | (left; rfl)
          | omega)) 20000
        unless r == some [] do throwError "closeByHint: a hypothesis"
    return true)
    (fun _ => do s.restore; return false)

/-- A fact of a loop invariant of the user (`check_loop_user`) where a path comes back to the loop
head, or at the loop's entry: its witnesses by unification (`checkExists`), the rest by `rfl`,
`assumption`, `omega`, `decide`, `simp only` with the hints, the theorems among the hints with their
hypotheses from the context (`closeByHint`: `Queries.set` from the set it is about and the size of
its key), each within a budget of heartbeats. -/
def closeUserFact (g : MVarId) (args : Array Syntax) : TacticM Bool := do
  let sargs : Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨args⟩
  let sargs' : Syntax.TSepArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] "," := ⟨args⟩
  let mut thms : Array Name := #[]
  for a in args do
    if let some id := a.find? (·.isIdent) then
      try
        let n ← realizeGlobalConstNoOverload id
        if let some (.thmInfo _) := (← getEnv).find? n then thms := thms.push n
      catch _ => pure ()
  let t0 ← IO.monoMsNow
  let parts ← checkExists g
  debugLine t0 s!"closeUserFact: the witnesses, {parts.length} parts left"
  for g' in parts do
    let closers : Array (TSyntax `tactic) := #[← `(tactic| with_reducible rfl), ← `(tactic| assumption),
      ← `(tactic| omega), ← `(tactic| (dsimp only; omega)), ← `(tactic| decide),
      ← `(tactic| (simp only [$sargs,*]; done)), ← `(tactic| (simp_all only [$sargs',*]; done)),
      ← `(tactic| (dsimp only; simp only [$sargs,*]; omega))]
    let mut closed := false
    for t in thms do
      if closed then break
      let t0 ← IO.monoMsNow
      if ← closeByHint g' t then closed := true
      debugLine t0 s!"closeUserFact: the hint {t}: {closed}"
    for c in closers do
      if closed then break
      let t0 ← IO.monoMsNow
      if let some [] ← tryTac g' c 50000 then closed := true
      debugLine t0 s!"closeUserFact: {c.raw.prettyPrint}: {closed}"
    unless closed do
      if check.debug.get (← getOptions) then
        let f ← g'.withContext do ppExpr (← instantiateMVars (← g'.getType))
        progressLine s!"  a fact of the loop invariant not shown: {(toString f).take 1500}"
      return false
  return true

/-- The invariant of a loop at a state (`∃ holes, (st = S[holes] ∧ chainJumps < bound) ∧ q`): the
holes by unification, the bound by `decide`/`omega`, `q` the invariant `SafeActs` of `c5`
(`vm_c5_close`), with the invariant of the user (`check_loop_user`: `SafeActs c5 ∧ P xs`, `P xs` by
`closeUserFact`). -/
def solveInvUser (g : MVarId) (args : Array Syntax) : TacticM Unit := do
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
      unless ty.isAppOfArity ``And 2 do throwError "check_loop: not the invariant"
      let left := ty.getArg! 0
      unless left.isAppOfArity ``And 2 do throwError "check_loop: not the invariant"
      let some (_, a, b) := (left.getArg! 0).eq? | throwError "check_loop: not an equation"
      unless ← withReducible (isDefEq a b) do throwError "check_loop: the state is not the loop head"
      let t0 ← IO.monoMsNow
      let hc ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (left.getArg! 1))
      let r ← Tactic.run hc.mvarId! do
        evalTactic (← `(tactic| first | decide | (simp only [freeNestedContJump]; omega)))
      unless r.isEmpty do throwError "check_loop: the bound of the jump counter"
      debugLine t0 "solveInvUser: the bound of the jump counter"
      let q ← instantiateMVars (ty.getArg! 1)
      let (qa, qb?) := if q.isAppOfArity ``And 2 && (q.getArg! 0).isAppOf ``SafeActs then
          (q.getArg! 0, some (q.getArg! 1)) else (q, none)
      let hqa ← mkFreshExprSyntheticOpaqueMVar qa
      let r ← Tactic.run hqa.mvarId! do evalTactic (← `(tactic| vm_c5_close))
      unless r.isEmpty do throwError "check_loop: the invariant of c5"
      debugLine t0 "solveInvUser: the invariant of c5"
      let hq ← match qb? with
        | none => pure hqa
        | some qb => do
          -- the user's predicate unfolded (`Cleanup key sub lc …`: its parts)
          let hqb ← mkFreshExprSyntheticOpaqueMVar (← whnfD (← instantiateMVars qb))
          unless ← closeUserFact hqb.mvarId! args do
            throwError "check_loop: the loop invariant of the user is not shown here"
          mkAppM ``And.intro #[hqa, hqb]
      g.assign (← mkAppM ``And.intro #[← mkAppM ``And.intro #[← mkEqRefl a, hc], hq])
      return
  throwError "check_loop: too many parts"

/-- `check_loop_close_user [hints]`: the run is back at the head of a loop of `check_loop` or
`check_loop_user`: by its hypothesis `ih` (the latest that applies, for a loop inside a loop), the
invariant there by `solveInvUser`. -/
@[tactic checkLoopCloseUser] def evalCheckLoopCloseUser : Tactic := fun stx => withMainContext do
  let args := stx[2].getSepArgs
  let g ← getMainGoal
  let ihs := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.userName == `ih && !d.isImplementationDetail then acc.push d.fvarId else acc
  for ih in ihs.reverse do
    let s ← saveState
    let t0 ← IO.monoMsNow
    try
      let gs ← g.apply (mkFVar ih)
      debugLine t0 s!"check_loop_close_user: ih applied, {gs.length} goals"
      let mut rest := #[]
      for g' in gs do
        if ← g'.isAssigned then continue
        let ty ← whnfR (← instantiateMVars (← g'.getType))
        if ty.isAppOf ``LE.le then
          let r ← Tactic.run g' (evalTactic (← `(tactic| omega)))
          unless r.isEmpty do throwError "check_loop_close_user: the fuel"
          debugLine t0 "check_loop_close_user: the fuel"
        else if ty.isAppOf ``Exists then
          solveInvUser g' args
        else rest := rest.push g'
      replaceMainGoal rest.toList
      return
    catch ex =>
      debugLine t0 s!"check_loop_close_user: {← ex.toMessageData.toString}"
      s.restore
  throwError "check_loop_close_user: no loop head to close"

/-- The holes of a loop head `S` for a loop invariant of the user: those of `loopHolesX` (the gas,
the loaded cells and libraries, the counters of jumps and steps, `c5`), the top `k` stack entries
as values (the deepest first), which the iterations may change in any way, and of a `REPEAT` loop
the count of its iterations left (the last). -/
def loopHolesV (S : Expr) (k : Nat) : MetaM (Array Expr × (Array Expr → Expr) × Nat × Nat) := do
  unless S.isAppOfArity ``VmState.mk 20 do throwError "check_loop: the state is not written out"
  let fields := getStructureFields (← getEnv) ``VmState
  let idx (n : Name) : MetaM Nat := do
    let some i := fields.idxOf? n | throwError "check_loop: no field {n}"
    return i
  let args := S.getAppArgs
  let plainNames := [`gas, `loadedCells, `loadedLibraries, `chainJumps, `steps]
  let plain ← plainNames.mapM idx
  let mut vals : Array Expr := plain.toArray.map (args[·]!)
  let iRegs ← idx `regs
  let regs := args[iRegs]!
  unless regs.isAppOfArity ``Regs.mk 7 do throwError "check_loop: the registers are not written out"
  vals := vals.push (regs.getArg! 5)
  let iStack ← idx `stack
  let mut stk := args[iStack]!
  let mut top : Array Expr := #[]
  for _ in [0:k] do
    unless stk.isAppOfArity ``Array.push 3 do
      throwError "check_loop: fewer than {k} stack entries written out"
    top := top.push (stk.getArg! 2)
    stk := stk.getArg! 1
  let nPlain := plain.length
  vals := vals ++ top.reverse
  -- a `REPEAT` loop: the count of the iterations left (`c0`), the last hole
  let c0 ← whnfR (regs.getArg! 0)
  let isRepeat := c0.isAppOfArity ``Continuation.repeatBody 3
  if isRepeat then vals := vals.push (c0.getArg! 2)
  let iCount := vals.size - 1
  let base := stk
  let fill (xs : Array Expr) : Expr := Id.run do
    let mut a := args
    for j in [0:nPlain] do a := a.set! plain[j]! xs[j]!
    let mut ra := regs.getAppArgs.set! 5 xs[nPlain]!
    if isRepeat then
      ra := ra.set! 0 (mkApp3 (mkConst ``Continuation.repeatBody) (c0.getArg! 0) (c0.getArg! 1) xs[iCount]!)
    a := a.set! iRegs (mkAppN regs.getAppFn ra)
    let mut s := base
    for j in [0:k] do
      s := mkApp3 (mkConst ``Array.push [0]) (mkConst ``Value) s xs[nPlain + 1 + j]!
    a := a.set! iStack s
    return mkAppN S.getAppFn a
  return (vals, fill, 3, nPlain)

/-- `check_loop_user k P [hints]` (`check_loop_any`): the loop rule at the loop head of the run in
the goal, with the invariant of `check_loop` (the state is the loop head but for the gas, the loaded
cells and libraries, the counters, `c5` satisfying `SafeActs`) where the top `k` stack entries may
be any values `x₁ … xₖ` (the deepest first) with `P x₁ … xₖ`: `P` a loop invariant the user gives
(`-- contract-check: loop k P` in the invariant's file). Fails if `P` is not shown of the entries at
the loop head (`closeUserFact`). Leaves the run out of fuel and the run with one more step, the
parts of `P` as hypotheses (`destructUser`). -/
def checkLoopUser (k : Nat) (p : Syntax) (args : Array Syntax) (names : Array Name) :
    TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "check_loop: no run in the goal"
  let exec := r.getArg! 0
  let n := r.getArg! 1
  let S := r.getArg! 2
  let (vals, fill, iChain, iC5) ← loopHolesV S k
  let tys ← vals.mapM fun v => (inferType v : MetaM Expr)
  let mut expected : Expr := mkSort levelZero
  for _ in [0:k] do expected := mkForall `x .default (mkConst ``Value) expected
  let P ← Term.elabTermEnsuringType p expected
  Term.synthesizeSyntheticMVarsNoPostponing
  -- a loop invariant `ran_case` bound before the invariant was taken apart (`loopInv0`): its value,
  -- the parameters of the invariant as they are now
  let P ← zetaReduce (← instantiateMVars P)
  let mut names := names
  if let .const c _ := P.getAppFn then names := names.push c
  let stTy := mkConst ``VmState
  let inv ← withLocalDeclD `st stTy fun st => do
    let decls := (List.range vals.size).toArray.map fun i =>
      (Name.mkSimple s!"x{i}", fun (_ : Array Expr) => pure tys[i]!)
    let body ← withLocalDeclsD decls fun xs => do
      let bound ← mkAppM ``LT.lt #[xs[iChain]!, mkConst ``freeNestedContJump]
      let user := (mkAppN P (xs.extract (iC5 + 1) (iC5 + 1 + k))).headBeta
      let q ← mkAppM ``And #[mkApp (mkConst ``SafeActs) xs[iC5]!, user]
      let mut e ← mkAppM ``And #[← mkAppM ``And #[← mkEq st (fill xs), bound], q]
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
  solveInvUser hinv.mvarId! args
  let rule ← mkAppOptM ``runWith_invLe #[exec, inv, motive, n, hz]
  let .forallE _ hsTy _ _ ← whnf (← inferType rule) | throwError "check_loop: the loop rule"
  let hs ← mkFreshExprSyntheticOpaqueMVar hsTy
  let pf ← mkAppOptM ``runWith_invLe #[exec, inv, motive, n, hz, hs, n, ← mkAppM ``Nat.le_refl #[n], S, hinv]
  unless ← isDefEq (← inferType pf) t do throwError "check_loop: the goal is not a property of the run"
  g.assign pf
  let old := (← getLCtx).getFVarIds
  let (_, gz) ← hz.mvarId!.intro `st
  let (h0, gz) ← gz.intro `hinv
  let gzs ← destructUser (← Exec.destructInv gz h0) names old
  let (_, gs) ← hs.mvarId!.intro `n
  let (_, gs) ← gs.intro `hfuel
  let (_, gs) ← gs.intro `st
  let (h1, gs) ← gs.intro `hinv
  let (_, gs) ← gs.intro `ih
  let gss ← destructUser (← Exec.destructInv gs h1) names old
  replaceMainGoal (gzs ++ gss)

/-- `check_loop_any [hints] (loop k := P)*`: at a loop head, the loop rule with the first loop
invariant of the user that holds there (`check_loop_user`), else with that of `check_loop`. -/
@[tactic checkLoopAny] def evalCheckLoopAny : Tactic := fun stx => do
  let args := stx[2].getSepArgs
  let mut names : Array Name := #[]
  for a in args do
    if let some id := a.find? (·.isIdent) then
      try
        let n ← realizeGlobalConstNoOverload id
        if let some (.defnInfo _) := (← getEnv).find? n then names := names.push n
      catch _ => pure ()
  for l in stx[4].getArgs do
    let k := l[2].isNatLit?.getD 1
    let s ← saveState
    try
      checkLoopUser k l[4] args names
      return
    catch ex =>
      s.restore
      -- with `check.debug`, why the loop invariant of the user does not apply here
      if check.debug.get (← getOptions) then
        progressLine s!"  check_loop_any: (loop {k}) not used: {← ex.toMessageData.toString}"
  evalTactic (← `(tactic| check_loop))

end TvmLean.Check

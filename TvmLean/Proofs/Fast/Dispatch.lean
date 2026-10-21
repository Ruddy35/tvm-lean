import TvmLean.Proofs.Fast.Twin

/-!
# Flattening a dispatch chain

The model runs an instruction with `execInstr`, a chain of some 300 handlers, each a `match` on the
instruction that runs its case or passes to the next handler. In the kernel each test unfolds the
handler's matcher, whose ~400 branches mention `next`: instantiating it copies them, about 250 ms and
tens of megabytes per instruction late in the chain, kept until the declaration ends.

`fast_dispatch f` (for `f` taking one argument of an inductive type) makes `fFast`, one `casesOn` on
the argument and on its fields of the inductive types declared in `TvmLean.Model.Instr.Ast` (the
sub-instructions), each branch the chain evaluated for that case: the functions of the chain (named
`execInstr…`) unfolded, their matches reduced, which leaves the handler's own code. Each branch is a
lemma `∀ fields, f (case) = branch` proved by `rfl` (one declaration per branch, so that the kernel's
evaluation of the chain is freed after each), and `f_eq_fast : f = fFast` follows by the same case
split. It is registered as a fast replacement (`@[fast_repl]`), so the twins call `fFast`.
-/

namespace TvmLean.Fast

open Lean Meta Elab Command

/-- The context of a flattening. -/
structure DispCtx where
  f : Name
  fFast : Name
  chain : Name → Bool
  splitOn : Name → Bool
  resTy : Expr
  /-- the universe level of `resTy` (as `resTy : Sort resLvl`) -/
  resLvl : Level
  counter : IO.Ref Nat

/-- Unfolds the chain at the head of `e` and reduces matches, as far as it goes. -/
partial def unfoldChain (chain : Name → Bool) (e : Expr) (fuel : Nat := 100000) : MetaM Expr := do
  let e ← whnfCore e
  if fuel == 0 then return e
  if let .const n _ := e.getAppFn then
    if chain n then
      if let some e' ← unfoldDefinition? e then
        return ← unfoldChain chain e' (fuel - 1)
  return e

/-- `e` with every application of a chain function inside it unfolded as far as it goes (the
continuation of a handler that reads the state before it matches the instruction). -/
def unfoldChainInside (chain : Name → Bool) (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun t => do
    if let .const n _ := t.getAppFn then
      if chain n then
        let t' ← unfoldChain chain t
        if t' != t then return .visit t'
    return .continue)

/-- The value and the proof of the case tree of `e` (`≡ f arg` in the local context `vars`): the
value (definitionally `f arg`) and a proof of `f arg = fFast arg`. -/
partial def dispatchTree (ctx : DispCtx) (e arg : Expr) (vars : Array Expr) (fuel : Nat := 100000) :
    MetaM (Expr × Expr) := do
  let e ← whnfCore e
  if fuel != 0 then
    if let .const n _ := e.getAppFn then
      if ctx.chain n then
        if let some e' ← unfoldDefinition? e then
          return ← dispatchTree ctx e' arg vars (fuel - 1)
      if let some info ← getMatcherInfo? n then
        let args := e.getAppArgs
        for d in args[info.getFirstDiscrPos:info.getFirstDiscrPos + info.numDiscrs] do
          let d ← whnfCore d
          if d.isFVar && vars.contains d then
            let ty ← whnf (← inferType d)
            if let .const ind lvls := ty.getAppFn then
              if ctx.splitOn ind then
                return ← split ctx e arg vars d ind lvls ty.getAppArgs fuel
  -- a leaf: the lemma `∀ vars, f arg = e`, by `rfl`
  let e ← unfoldChainInside ctx.chain e
  let k ← ctx.counter.modifyGet fun k => (k, k + 1)
  let lemmaName := ctx.fFast ++ Name.mkSimple s!"eq_{k}"
  let lhs := mkApp (mkConst ctx.f) arg
  let stmt ← mkForallFVars vars (mkApp3 (mkConst ``Eq [ctx.resLvl]) ctx.resTy lhs e)
  let pf ← mkLambdaFVars vars (mkApp2 (mkConst ``Eq.refl [ctx.resLvl]) ctx.resTy lhs)
  addDecl <| .thmDecl { name := lemmaName, levelParams := [], type := stmt, value := pf }
  return (e, mkAppN (mkConst lemmaName) vars)
where
  split (ctx : DispCtx) (e arg : Expr) (vars : Array Expr) (d : Expr) (ind : Name) (lvls : List Level)
      (tyArgs : Array Expr) (fuel : Nat) : MetaM (Expr × Expr) := do
    let ival ← getConstInfoInduct ind
    let params := tyArgs[:ival.numParams].toArray
    let dTy ← inferType d
    let mut vMinors := #[]
    let mut pMinors := #[]
    for c in ival.ctors do
      let cty ← instantiateForall (← inferType (mkConst c lvls)) params
      let (vm, pm) ← forallTelescope cty fun ys _ => do
        let ca := mkAppN (mkAppN (mkConst c lvls) params) ys
        let vars' := (vars.filter (· != d)) ++ ys
        let (v, p) ← dispatchTree ctx (e.replaceFVar d ca) (arg.replaceFVar d ca) vars' (fuel - 1)
        return (← mkLambdaFVars ys v, ← mkLambdaFVars ys p)
      vMinors := vMinors.push vm
      pMinors := pMinors.push pm
    -- the value: `ind.casesOn (motive := fun _ => resTy) d minors`
    let vMotive ← withLocalDeclD `z dTy fun z => mkLambdaFVars #[z] ctx.resTy
    let v := mkAppN (mkConst (Name.mkStr ind "casesOn") (ctx.resLvl :: lvls))
      (params ++ #[vMotive, d] ++ vMinors)
    -- the proof: motive `fun z => f arg[z] = fFast arg[z]`
    let pMotive ← mkLambdaFVars #[d] (mkApp3 (mkConst ``Eq [ctx.resLvl]) ctx.resTy (mkApp (mkConst ctx.f) arg)
      (mkApp (mkConst ctx.fFast) arg))
    let p := mkAppN (mkConst (Name.mkStr ind "casesOn") (levelZero :: lvls)) (params ++ #[pMotive, d] ++ pMinors)
    return (v, p)

/-- `fast_dispatch f`: flattens the dispatch chain `f` (see the module docstring). -/
elab "fast_dispatch " id:ident : command => liftTermElabM do
  let f ← realizeGlobalConstNoOverloadWithInfo id
  let fci ← getConstInfo f
  unless fci.levelParams.isEmpty do throwError "fast_dispatch: {f} has universe parameters"
  let env ← getEnv
  let some astMod := env.getModuleIdx? `TvmLean.Model.Instr.Ast | throwError "fast_dispatch: no Ast module"
  let splitOn (n : Name) : Bool := env.getModuleIdxFor? n == some astMod && (env.find? n matches some (.inductInfo _))
  let chain (n : Name) : Bool := match n with
    | .str _ s => s.startsWith "execInstr" && (`TvmLean).isPrefixOf n
    | _ => false
  let fFast := f.appendAfter "Fast"
  -- one declaration at a time; no heartbeat limit (the chain is unfolded some 300 times per case)
  withOptions (Elab.async.set · false) do
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  forallTelescope fci.type fun xs resTy => do
    unless xs.size == 1 do throwError "fast_dispatch: {f} must take one argument"
    let i := xs[0]!
    let resLvl ← getLevel resTy
    let ctx : DispCtx := { f, fFast, chain, splitOn, resTy, resLvl, counter := ← IO.mkRef 0 }
    let (v, p) ← dispatchTree ctx (mkApp (mkConst f) i) i #[i]
    let value ← mkLambdaFVars #[i] v
    let dv : DefinitionVal :=
      { name := fFast, levelParams := [], type := fci.type, value := value, hints := .regular 0, safety := .safe }
    addDecl (.defnDecl dv)
    -- `f = fFast` by `funext`
    let eqPt ← mkLambdaFVars #[i] p
    let stmt ← mkEq (mkConst f) (mkConst fFast)
    let argTy ← inferType i
    let argLvl ← getLevel argTy
    let pf := mkApp5 (mkConst ``funext [argLvl, resLvl]) argTy (← mkLambdaFVars #[i] resTy) (mkConst f)
      (mkConst fFast) eqPt
    let thm := f.appendAfter "_eq_fast"
    addDecl <| .thmDecl { name := thm, levelParams := [], type := stmt, value := pf }
    modifyEnv (fastReplExt.addEntry · (f, fFast, thm))
    logInfo m!"fast_dispatch: {fFast} with {← ctx.counter.get} branches"

end TvmLean.Fast

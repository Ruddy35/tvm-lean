import Lean

/-!
# Fast twins: the model's definitions with kernel-friendly primitives, proved equal

The kernel evaluates a definition by unfolding it, so a fast form of a primitive (`Slice.readBitsFast`
for `Slice.readBits`, ...) speeds up nothing that calls the primitive through another definition.
A *twin* of a definition `c` is `TvmLean.Fast.Twin.c`: the same value with every registered primitive
replaced by its fast form and every definition that (transitively) calls one replaced by its own twin;
`TvmLean.Fast.Twin.c.eq_twin : @c = @TvmLean.Fast.Twin.c` is proved by congruence from the equalities
of what was replaced. Evaluating the twin of `VmState.run` evaluates the model with the fast primitives,
and its result is the model's.

* `@[fast_repl] theorem t : @orig = @fast` registers a replacement (the universe parameters of `t`
  those of `orig`, in order).
* `fast_twin c₁ c₂ …` makes the twins of the constants and of everything they need (a command, so
  that a module can hold them compiled once).
* `fast_decide` closes a decidable goal `P` (a code fact, a concrete run): it makes the twins of
  what `P` and its `Decidable` instance mention (or finds them), proves `decide P = decide P'` (`P'`
  with the twins) by congruence, and `decide P' = true` by the kernel's evaluation (as `decide +kernel`
  does, in an auxiliary lemma). No axiom beyond those of the equalities used.
* `fast_rfl` closes a closed equation `lhs = rhs` the same way, `lhs' = rhs'` by `Eq.refl` checked
  by the kernel (for types without `DecidableEq`, such as VM states); `fast_eval` tries `fast_decide`,
  then `fast_rfl`.
* `simp only [fast_forms]` rewrites a goal into the fast forms (the pointwise equalities).

What gets a twin: a definition whose value mentions a constant that has a replacement or a twin, and
a theorem whose statement does (its twin is its statement over the twins, proved by transport, so that
the twins of the definitions that use it as a proof typecheck). A constant that occurs in the *type*
of a definition, an inductive type or a constructor of what is being twinned is never twinned (its twin
would change those types); it keeps calling the slow primitives, which only matters if it is evaluated.

The equality of a twin is proved without unfolding anything: with `M := fun x₁ h₁ … xₖ hₖ => v[xᵢ]`
(the value with each replaced occurrence `cᵢ` abstracted, `hᵢ : cᵢ = xᵢ`, the proofs whose statements
mention a `cᵢ` cast along the `hᵢ`), `M c₁ rfl … cₖ rfl = M c₁' e₁ … cₖ' eₖ` by one `Eq.rec` per
position; the two sides are `c` and its twin up to beta and proof irrelevance, which the kernel checks.
-/

namespace TvmLean.Fast

open Lean Meta Elab Command Tactic

/-- The registered replacements: an original constant, its fast form, and the theorem
`@orig = @fast` (`@[fast_repl]`). -/
initialize fastReplExt : SimplePersistentEnvExtension (Name × Name × Name) (NameMap (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (o, f, t) => m.insert o (f, t)
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (o, f, t) => m.insert o (f, t)) m) {}
  }

/-- The simp set of the fast forms: the pointwise equalities `orig … = fast …` of
`TvmLean/Proofs/Fast/` (`simp only [fast_forms]` rewrites a goal into the fast forms; the function-level
equalities `@orig = @fast` are the `@[fast_repl]` ones). -/
register_simp_attr fast_forms

/-- The twin of `n`: `TvmLean.Fast.Twin.<n>`. -/
def twinName (n : Name) : Name := `TvmLean.Fast.Twin ++ n

/-- The theorem `@n = @twin` of a definition's twin. -/
def twinEqName (n : Name) : Name := twinName n ++ `eq_twin

initialize registerBuiltinAttribute {
  name := `fast_repl
  descr := "registers a theorem `@orig = @fast` for the fast twins (TvmLean.Proofs.Fast.Twin)"
  add := fun decl _stx _kind => do
    let ci ← getConstInfo decl
    let some (_, lhs, rhs) := ci.type.eq? | throwError "fast_repl: {decl} is not an equation"
    let .const o ls := lhs | throwError "fast_repl: the left side of {decl} is not a constant"
    unless ls == ci.levelParams.map mkLevelParam do
      throwError "fast_repl: the universe parameters of {decl} must be those of {o}, in order"
    let .const f _ := rhs.getAppFn | throwError "fast_repl: the right side of {decl} is not a constant"
    modifyEnv (fastReplExt.addEntry · (o, f, decl))
}

/-- What replaces the occurrence `.const n ls`: the new term, and the proof of `old = new` (`none` for
a proof, whose twin is its transport). A twin comes first: a replaced constant whose fast form needs
a twin itself gets one (`ensureTwin`), the fast form's twin. -/
def lookupRepl (env : Environment) (n : Name) (ls : List Level) : Option (Expr × Option Expr) :=
  let tw := twinName n
  if env.contains tw then
    some (mkConst tw ls, if env.contains (twinEqName n) then some (mkConst (twinEqName n) ls) else none)
  else
    match (fastReplExt.getState env).find? n with
    | some (_, t) =>
      match env.find? t with
      | some tci =>
        match tci.type.eq? with
        | some (_, _, rhs) => some (rhs.instantiateLevelParams tci.levelParams ls, some (mkConst t ls))
        | none => none
      | none => none
    | none => none

/-- `n` has a replacement or a twin. -/
def hasRepl (env : Environment) (n : Name) : Bool :=
  (fastReplExt.getState env).contains n || env.contains (twinName n)

/-- The state of a twin generation: which constants need a twin, and the constants that must keep
their identity (they occur in types). -/
structure TwinState where
  needs : NameMap Bool := {}
  frozen : NameSet := {}

abbrev TwinM := StateT TwinState MetaM

/-- The walk of `freezeTypes`: pops a constant, marks the constants of its type as frozen (unless it
is a theorem) and pushes those of its type, of its value (unless it is a theorem) and its
constructors; at most `fuel` steps. -/
def freezeLoop (env : Environment) : Nat → List Name → NameSet → NameSet → Except String NameSet
  | 0, _, _, _ => .error "fast twin: the closure of the roots is too large"
  | _, [], _, frozen => .ok frozen
  | fuel + 1, n :: rest, seen, frozen =>
    if seen.contains n then freezeLoop env fuel rest seen frozen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => freezeLoop env fuel rest seen frozen
      | some ci =>
        let isThm := ci matches .thmInfo _
        let tyCs := ci.type.getUsedConstants
        let frozen := if isThm then frozen else tyCs.foldl (fun f c => f.insert c) frozen
        let push (st : List Name) (cs : Array Name) : List Name :=
          cs.foldl (fun st c => if seen.contains c then st else c :: st) st
        let stack := push rest tyCs
        let stack := match ci.value? (allowOpaque := false) with
          | some v => if isThm then stack else push stack v.getUsedConstants
          | none => stack
        let stack := match ci with
          | .inductInfo iv => push stack iv.ctors.toArray
          | _ => stack
        freezeLoop env fuel stack seen frozen

/-- Marks as frozen the constants occurring in the types of the definitions, inductive types and
constructors reachable from `roots` (through values and types). -/
def freezeTypes (roots : Array Name) : TwinM Unit := do
  match freezeLoop (← getEnv) 100000000 roots.toList {} (← get).frozen with
  | .ok frozen => modify fun s => { s with frozen }
  | .error msg => throwError msg

/-- Whether `n` needs a twin: it is replaced, or it is a definition whose value, or a theorem whose
statement, mentions a constant that needs one; never a frozen constant. `fuel` bounds the depth of
the dependencies followed. -/
def needsF : Nat → Name → TwinM Bool
  | 0, n => throwError "fast twin: the dependencies of {n} are nested too deeply"
  | fuel + 1, n => do
    if let some b := (← get).needs.find? n then return b
    let env ← getEnv
    if hasRepl env n then
      modify fun s => { s with needs := s.needs.insert n true }
      return true
    if (← get).frozen.contains n then
      modify fun s => { s with needs := s.needs.insert n false }
      return false
    modify fun s => { s with needs := s.needs.insert n false }
    let some ci := env.find? n | return false
    let deps : Array Name := match ci with
      | .defnInfo d => d.value.getUsedConstants
      | .thmInfo t => t.type.getUsedConstants
      | _ => #[]
    let mut r := false
    for d in deps do
      if ← needsF fuel d then
        r := true
        break
    modify fun s => { s with needs := s.needs.insert n r }
    return r

/-- The depth of dependencies `needs` and `ensureTwin` follow at most. -/
def twinFuel : Nat := 100000

/-- `needsF` with `twinFuel`. -/
def needs (n : Name) : TwinM Bool := needsF twinFuel n

/-- The occurrences `.const n ls` in `e` that have a replacement. -/
def replOccs (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let r ← IO.mkRef (#[] : Array Expr)
  e.forEachWhere (fun x => x.isConst && hasRepl env x.constName!) fun x =>
    r.modify fun a => if a.contains x then a else a.push x
  r.get

/-- `e` with every replaced constant replaced. -/
def replaceAll (env : Environment) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n ls => (lookupRepl env n ls).map (·.1)
    | _ => none

/-- Runs `k` with variables `x_i : type of occ_i` and `h_i : occ_i = x_i`. -/
def withTwinVars {α} (occs : List Expr) (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
  go occs #[] #[]
where
  go : List Expr → Array Expr → Array Expr → MetaM α
  | [], xs, hs => k xs hs
  | o :: os, xs, hs => do
    let ty ← inferType o
    withLocalDeclD `x ty fun x => do
      withLocalDeclD `h (← mkEq o x) fun h => go os (xs.push x) (hs.push h)

/-- `e'` (every replaced constant replaced) and a proof of `e = e'`. -/
def mkTwinEq (e : Expr) : MetaM (Expr × Expr) := do
  let env ← getEnv
  let occs ← replOccs e
  let e' := replaceAll env e
  let isFn (o : Expr) : Bool := match lookupRepl env o.constName! o.constLevels! with
    | some (_, some _) => true
    | _ => false
  let prOccs := occs.filter (!isFn ·)
  let mut fnOccs := occs.filter isFn
  for p in prOccs do
    for o in ← replOccs (← inferType p) do
      unless isFn o do throwError "fast twin: the statement of {p} mentions the proof {o}"
      unless fnOccs.contains o do fnOccs := fnOccs.push o
  let ty ← inferType e
  let lvl ← getLevel ty
  withTwinVars fnOccs.toList fun xs hs => do
    let sub (t : Expr) : Expr := t.replace fun x =>
      match fnOccs.idxOf? x with
      | some i => some xs[i]!
      | none => none
    -- the casts of the proofs: `Eq.mp (T = T[x]) p`
    let mut casts : Array (Expr × Expr) := #[]
    for p in prOccs do
      let T ← inferType p
      let mut idx : Array Nat := #[]
      for o in ← replOccs T do
        idx := idx.push (fnOccs.idxOf o)
      let ys := idx.map (xs[·]!)
      let mot ← mkLambdaFVars ys (sub T)
      let mut h ← mkEqRefl mot
      for i in idx do
        h ← mkCongr h hs[i]!
      casts := casts.push (p, mkApp4 (mkConst ``Eq.mp [levelZero]) T (sub T) h p)
    let body := (sub e).replace fun x =>
      match casts.find? (·.1 == x) with
      | some (_, c) => some c
      | none => none
    let vars := (List.range fnOccs.size).foldl (fun a i => a.push xs[i]! |>.push hs[i]!) #[]
    let m ← mkLambdaFVars vars body
    -- the chain: position i goes from (c_i, rfl) to (c_i', e_i)
    let olds ← fnOccs.mapM fun o => do return (o, ← mkEqRefl o)
    let news ← fnOccs.mapM fun o => do
      let some (n, some pf) := lookupRepl env o.constName! o.constLevels! | throwError "fast twin: internal"
      return (n, pf)
    let argsOf (a : Array (Expr × Expr)) : Array Expr := a.foldl (fun r (x, h) => r.push x |>.push h) #[]
    let mut cur := olds
    let start := mkAppN m (argsOf olds)
    let mut proof ← mkEqRefl start
    for i in [0:fnOccs.size] do
      let o := fnOccs[i]!
      let τ ← inferType o
      let lv ← getLevel τ
      let prevApp := mkAppN m (argsOf cur)
      let c := cur
      let motive ← withLocalDeclD `x τ fun x => do
        withLocalDeclD `h (← mkEq o x) fun h => do
          let a := c.set! i (x, h)
          mkLambdaFVars #[x, h] (← mkEq prevApp (mkAppN m (argsOf a)))
      let next := cur.set! i news[i]!
      let nextApp := mkAppN m (argsOf next)
      let step := mkApp6 (mkConst ``Eq.rec [levelZero, lv]) τ o motive (← mkEqRefl prevApp) news[i]!.1 news[i]!.2
      proof := mkApp6 (mkConst ``Eq.trans [lvl]) ty start prevApp nextApp proof step
      cur := next
    return (e', proof)

/-- Whether the fast form `f` of a replaced constant needs a twin itself (it calls constants that are
replaced or have twins). -/
def fastNeedsTwin (f : Name) : TwinM Bool := do
  let env ← getEnv
  if env.contains (twinName f) then return false
  let some (.defnInfo d) := env.find? f | return false
  for c in d.value.getUsedConstants do
    if ← needs c then return true
  return false

/-- Makes the twin of `n` (and of what it needs first), if it needs one. For a replaced constant
whose fast form `f` needs a twin: the twin of `f`, and `twin n := twin f` with
`@n = @twin n` from `@n = @f` and `@f = @twin f`. `fuel` bounds the depth of the dependencies
followed. -/
def ensureTwinF : Nat → Name → TwinM Unit
  | 0, n => throwError "fast twin: the dependencies of {n} are nested too deeply"
  | fuel + 1, n => do
    let env ← getEnv
    if env.contains (twinName n) then return
    if let some (f, t) := (fastReplExt.getState env).find? n then
      if f != n && (← fastNeedsTwin f) then
        ensureTwinF fuel f
        let ci ← getConstInfo n
        let us := ci.levelParams.map mkLevelParam
        let tci ← getConstInfo t
        let some (_, _, rhs) := tci.type.eq? | return
        let fT := rhs.instantiateLevelParams tci.levelParams us
        let some (fT', some fEq) := lookupRepl (← getEnv) f fT.constLevels! | return
        let dv : DefinitionVal :=
          { name := twinName n, levelParams := ci.levelParams, type := ci.type, value := fT', hints := .abbrev,
            safety := .safe }
        addDecl (.defnDecl dv)
        let ty ← mkEq (mkConst n us) (mkConst (twinName n) us)
        let pf ← mkEqTrans (mkConst t us) fEq
        addDecl <| .thmDecl { name := twinEqName n, levelParams := ci.levelParams, type := ty, value := pf }
      return
    unless ← needs n do return
    let ci ← getConstInfo n
    let us := ci.levelParams.map mkLevelParam
    match ci with
    | .defnInfo d =>
      for c in d.value.getUsedConstants do ensureTwinF fuel c
      let (v', pf) ← mkTwinEq d.value
      addDecl <| .defnDecl { d with name := twinName n, value := v', all := [twinName n] }
      let ty ← mkEq (mkConst n us) (mkConst (twinName n) us)
      addDecl <| .thmDecl { name := twinEqName n, levelParams := d.levelParams, type := ty, value := pf }
    | .thmInfo t =>
      for c in t.type.getUsedConstants do ensureTwinF fuel c
      let (T', pf) ← mkTwinEq t.type
      let v := mkApp4 (mkConst ``Eq.mp [levelZero]) t.type T' pf (mkConst n us)
      addDecl <| .thmDecl { name := twinName n, levelParams := t.levelParams, type := T', value := v }
    | _ => throwError "fast twin: {n} is neither a definition nor a theorem"

/-- `ensureTwinF` with `twinFuel`. -/
def ensureTwin (n : Name) : TwinM Unit := ensureTwinF twinFuel n

/-- Makes the twins of `roots` and of all they need. -/
def twinsOf (roots : Array Name) : MetaM Unit := do
  let go : TwinM Unit := do
    freezeTypes roots
    for n in roots do ensureTwin n
  discard <| go.run {}

/-- `fast_twin c₁ c₂ …`: makes the twins of the constants and of all they need. -/
elab "fast_twin " ids:ident+ : command => liftTermElabM do
  let ns ← ids.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
  -- one declaration at a time: the kernel checks each twin as it is added
  withOptions (Elab.async.set · false) <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 })
    (twinsOf ns)

/-- `fast_decide`: closes a decidable goal `P` by kernel evaluation of `P` over the fast twins:
`decide P = decide P'` by congruence (`P'` with the twins), `decide P' = true` by the kernel
(an auxiliary lemma, as `decide +kernel` makes). -/
elab "fast_decide" : tactic => closeMainGoalUsing `fast_decide fun expectedType _ => do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then expectedType ← zetaReduce expectedType
  if expectedType.hasFVar || expectedType.hasMVar then
    throwError "fast_decide: the goal must be closed (no free variables or metavariables){indentExpr expectedType}"
  let pf ← mkDecideProof expectedType
  -- `pf : decide P = true` as `of_decide_eq_true (Eq.refl true)`; take `decide P` from its type
  let d := mkApp2 (mkConst ``Decidable.decide) expectedType pf.appFn!.appArg!
  let roots := (d.getUsedConstants).filter fun n => !(`TvmLean.Fast.Twin).isPrefixOf n
  withOptions (Elab.async.set · false) <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 })
    (twinsOf roots)
  let (d', heq) ← mkTwinEq d
  -- `d' = true` by the kernel, in an auxiliary lemma
  let ty' ← mkEq d' (mkConst ``Bool.true)
  let levels := (collectLevelParams {} ty').params.toList
  let aux ← withOptions (Elab.async.set · false) do
    mkAuxLemma levels ty' (← mkEqRefl (mkConst ``Bool.true))
  let h' := mkConst aux (levels.map mkLevelParam)
  -- `decide P = true` from `decide P = decide P'` and `decide P' = true`
  let h ← mkEqTrans heq h'
  return mkApp3 (mkConst ``of_decide_eq_true) expectedType pf.appFn!.appArg! h

/-- A proof of the closed equation `ty` (`lhs = rhs`) by kernel evaluation over the fast twins:
`lhs = lhs'` and `rhs = rhs'` by congruence, `lhs' = rhs'` by `Eq.refl` checked by the kernel in an
auxiliary lemma (the kernel evaluates both sides as far as it needs to compare them). -/
def fastRflProof (ty : Expr) : MetaM Expr := do
  let some (_, lhs, rhs) := ty.eq? | throwError "fast_rfl: the goal is not an equation{indentExpr ty}"
  let roots := (lhs.getUsedConstants ++ rhs.getUsedConstants).filter fun n => !(`TvmLean.Fast.Twin).isPrefixOf n
  withOptions (Elab.async.set · false) <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 })
    (twinsOf roots)
  let (lhs', h1) ← mkTwinEq lhs
  let (rhs', h2) ← mkTwinEq rhs
  let ty' ← mkEq lhs' rhs'
  let levels := (collectLevelParams {} ty').params.toList
  let aux ← withOptions (Elab.async.set · false) do
    mkAuxLemma levels ty' (← mkEqRefl lhs')
  let h' := mkConst aux (levels.map mkLevelParam)
  mkEqTrans (← mkEqTrans h1 h') (← mkEqSymm h2)

/-- `fast_rfl`: closes a closed equation `lhs = rhs` by kernel evaluation over the fast twins
(`fastRflProof`). For goals whose type has no `DecidableEq` instance, such as an equation of VM
states. -/
elab "fast_rfl" : tactic => closeMainGoalUsing `fast_rfl fun expectedType _ => do
  let mut ty ← instantiateMVars expectedType
  if ty.hasFVar then ty ← zetaReduce ty
  if ty.hasFVar || ty.hasMVar then
    throwError "fast_rfl: the goal must be closed (no free variables or metavariables){indentExpr ty}"
  fastRflProof ty

/-- `fast_eval`: `fast_decide`, or `fast_rfl` for an equation whose type has no `DecidableEq`. -/
macro "fast_eval" : tactic => `(tactic| first | fast_decide | fast_rfl)

end TvmLean.Fast

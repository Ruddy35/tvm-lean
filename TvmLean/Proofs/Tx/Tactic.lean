import Lean

/-!
# Tactics to run a definition of the transaction model symbolically

The phases of a transaction (`TvmLean/Transaction/`) are long `do` blocks over `Option`,
`Except String` and `Id`, with join points, `let`s of whole `Tx` records, early returns and
`match`es. A specification of such a function `f` is stated as `OKo R (f ...)`, `OKe R (f ...)`
or `OKp R (f ...)` (what `f` returns, if anything, satisfies `R`), and proved by:
* `tx_vcg`: one goal per path through the code (a verification condition generator): `bind`,
  `pure`, `<$>` of `Option`, `Except ε` and `Id` on constructors reduced; projections of
  constructors reduced; `if`s and `match`es split (their conditions become hypotheses); a bind on a
  call (`← g x`) split on the call's result, with `OKo_bind` / `OKe_bind`; `let`s of records kept
  as local definitions (never copied into the goal); join points of `do` notation inlined, or, with
  `keep_jps`, kept for `tx_jp_spec` / `tx_vcg_inv`, which prove a join point once under invariants
  of its arguments instead of once per call;
* `tx_specs [L₁, ...]`: the specifications `Lᵢ` of the functions called, as hypotheses;
* `tx_close [fields] [defs]`: `grind` on what is left (`tx_abstract`, `tx_clear_values` and
  `tx_unfold` first turn the local definitions into equations between the fields that matter);
* `tx_split_hyps` and `tx_solve`: a splitter of hypotheses and a small backtracking prover, for
  goals with existentials.
All rewriting of `tx_vcg` is up to definitional equality (no lemma is used but the `OK*` rules).
-/

open Lean Meta Elab Tactic

namespace TvmLean.Proofs.TxTac

/-! ## Rewriting steps (definitional) -/

/-- Whether `e` is a constructor application. -/
def isCtorApp (e : Expr) : MetaM Bool := do
  match e.consumeMData.getAppFn with
  | .const n _ => return (← getEnv).isConstructor n
  | _ => return false

/-- The number of arguments of a function type that carry state (not of type `PUnit`). -/
def jpArity : Expr → Nat
  | .forallE _ t b _ => jpArity b + (if t.isAppOf ``PUnit || t.isConstOf ``Unit then 0 else 1)
  | _ => 0

/-- The structure, its constructor's parameters and its field names, if `e` is an application of
the constructor of a structure with at least four fields (a record such as `Tx`). -/
def recordCtor? (e : Expr) : MetaM (Option (Name × Nat × Array Name)) := do
  let e := e.consumeMData
  let .const c _ := e.getAppFn | return none
  let some (.ctorInfo info) := (← getEnv).find? c | return none
  let some si := getStructureInfo? (← getEnv) info.induct | return none
  if si.fieldNames.size < 4 then return none
  if e.getAppNumArgs != info.numParams + info.numFields then return none
  return some (info.induct, info.numParams, si.fieldNames)

/-- `k a` with `k` a continuation: a `let` when `k` is a `fun` (the value is not copied into each
use). -/
def applyCont (k a : Expr) : MetaM Expr := do
  let some _ ← recordCtor? a | return k.beta #[a]
  match k.consumeMData with
  | .lam n ty body _ => return .letE n ty a body false
  | k => return mkApp k a

/-- Reduce the monadic glue of `do` notation in `e`: `bind`, `pure` and `<$>` of `Option`,
`Except ε` and `Id` on constructors (for `Id` always), `Id.run`, projections of constructor
applications. Join points (`let __do_jp := v; b`) and local definitions of functions are inlined. -/
def reduceExpr (e : Expr) (keepJps : Bool := false) : MetaM Expr := do
  let lctx ← getLCtx
  let e ← Meta.transform e
    (pre := fun e => do
      match e with
      | .mdata _ b => return .visit b
      | .letE n t v b _ =>
        if n.eraseMacroScopes.toString.startsWith "__do_jp" then
          if keepJps && jpArity t ≥ 1 then return .continue
          return .visit (b.instantiate1 v)
        else if t.isForall then
          return .visit (b.instantiate1 v)
        else return .continue
      | .fvar id =>
        match lctx.find? id with
        | some d =>
          if d.isLet && d.type.isForall then return .visit d.value else return .continue
        | none => return .continue
      | _ => return .continue)
    (post := fun e => do
      let e := e.headBeta
      -- float `let`s out of the values of `let`s and out of projections
      if let .letE n t (.letE m u w c _) b _ := e then
        return .visit (.letE m u w (.letE n (t.liftLooseBVars 0 1) c (b.liftLooseBVars 1 1) false) false)
      if let .proj sn i (.letE m u w c _) := e then
        return .visit (.letE m u w (.proj sn i c) false)
      if (e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 ||
          e.isAppOfArity ``MProd.fst 3 || e.isAppOfArity ``MProd.snd 3) then
        if let .letE m u w c _ := e.getArg! 2 then
          let f := e.getAppFn
          let a0 := (e.getArg! 0).liftLooseBVars 0 1
          let a1 := (e.getArg! 1).liftLooseBVars 0 1
          return .visit (.letE m u w (mkApp3 f a0 a1 c) false)
      -- `Id.run x`
      if e.isAppOfArity ``Id.run 2 then return .visit (e.getArg! 1)
      -- `if` on a decided instance
      if e.isAppOfArity ``ite 5 then
        let d := (e.getArg! 2).consumeMData
        if d.isAppOfArity ``Decidable.isTrue 2 then return .visit (e.getArg! 3)
        if d.isAppOfArity ``Decidable.isFalse 2 then return .visit (e.getArg! 4)
      if e.isAppOfArity ``dite 5 then
        let d := (e.getArg! 2).consumeMData
        if d.isAppOfArity ``Decidable.isTrue 2 then return .visit ((e.getArg! 3).beta #[d.getArg! 1])
        if d.isAppOfArity ``Decidable.isFalse 2 then return .visit ((e.getArg! 4).beta #[d.getArg! 1])
      -- projections of constructors
      if let .proj _ i s := e then
        if ← isCtorApp s then
          match (← getEnv).find? s.getAppFn.constName! with
          | some (.ctorInfo info) =>
            if s.getAppNumArgs > info.numParams + i then return .visit (s.getArg! (info.numParams + i))
            else return .continue
          | _ => return .continue
      if (e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3) then
        let s := e.getArg! 2
        if s.isAppOfArity ``Prod.mk 4 then
          return .visit (s.getArg! (if e.isAppOfArity ``Prod.fst 3 then 2 else 3))
      if (e.isAppOfArity ``MProd.fst 3 || e.isAppOfArity ``MProd.snd 3) then
        let s := e.getArg! 2
        if s.isAppOfArity ``MProd.mk 4 then
          return .visit (s.getArg! (if e.isAppOfArity ``MProd.fst 3 then 2 else 3))
      -- `match d with | (x, y) => b`: a single alternative destructuring a structure
      if let .const mn _ := e.getAppFn then
        if let some mi ← getMatcherInfo? mn then
          if mi.numDiscrs == 1 && mi.altNumParams.size == 1 &&
              e.getAppNumArgs == mi.getFirstAltPos + 1 then
            let d := e.getArg! mi.getFirstDiscrPos
            let alt := e.getArg! mi.getFirstAltPos
            let dTy ← whnfR (← inferType d)
            if let .const sn _ := dTy.getAppFn then
              if let some si := getStructureInfo? (← getEnv) sn then
                let n := si.fieldNames.size
                if mi.altNumParams[0]! == n then
                  if d.consumeMData.isFVar then
                    let args := (List.range n).toArray.map fun i => Expr.proj sn i d
                    return .visit (alt.beta args)
                  -- bind the destructured value once
                  let args := (List.range n).toArray.map fun i => Expr.proj sn i (.bvar 0)
                  return .visit (.letE `p (← inferType d) d (alt.beta args) false)
      -- a `match` on constructors
      if let .const mn _ := e.getAppFn then
        if let some mi ← getMatcherInfo? mn then
          if e.getAppNumArgs ≥ mi.getFirstAltPos + mi.numAlts then
            let discrs := (List.range mi.numDiscrs).map fun i => e.getArg! (mi.getFirstDiscrPos + i)
            if ← discrs.allM (fun d => isCtorApp d) then
              if let .reduced e' ← reduceMatcher? e then return .visit e'
      -- `throw e` in `Except ε`
      if e.isAppOfArity ``MonadExcept.throw 5 || e.isAppOfArity ``MonadExceptOf.throw 5 then
        let m := e.getArg! 1
        if m.isAppOfArity ``Except 1 then
          let some v := (m.getAppFn.constLevels!)[0]? | return .continue
          let α := e.getArg! 3
          let α' ← whnfR (← inferType α)
          let some u := (α'.sortLevel!.dec) | return .continue
          return .visit (mkApp3 (mkConst ``Except.error [v, u]) (m.getArg! 0) α (e.getArg! 4))
      -- `pure a`
      if e.isAppOfArity ``Pure.pure 4 then
        let m := e.getArg! 0
        let α := e.getArg! 2
        let a := e.getArg! 3
        let some u := (e.getAppFn.constLevels!)[0]? | return .continue
        if m.isConstOf ``Option then return .visit (mkApp2 (mkConst ``Option.some [u]) α a)
        if m.isAppOfArity ``Except 1 then
          let some v := (m.getAppFn.constLevels!)[0]? | return .continue
          return .visit (mkApp3 (mkConst ``Except.ok [v, u]) (m.getArg! 0) α a)
        if m.isConstOf ``Id then return .visit a
        return .continue
      -- `x >>= k`
      if e.isAppOfArity ``Bind.bind 6 then
        let m := e.getArg! 0
        let β := e.getArg! 3
        let x := e.getArg! 4
        let k := e.getArg! 5
        let some u := (e.getAppFn.constLevels!)[0]? | return .continue
        if m.isConstOf ``Id then return .visit (← applyCont k x)
        if m.isConstOf ``Option then
          if x.isAppOfArity ``Option.some 2 then return .visit (← applyCont k (x.getArg! 1))
          if x.isAppOfArity ``Option.none 1 then return .visit (mkApp (mkConst ``Option.none [u]) β)
        if m.isAppOfArity ``Except 1 then
          let some v := (m.getAppFn.constLevels!)[0]? | return .continue
          if x.isAppOfArity ``Except.ok 3 then return .visit (← applyCont k (x.getArg! 2))
          if x.isAppOfArity ``Except.error 3 then
            return .visit (mkApp3 (mkConst ``Except.error [v, u]) (m.getArg! 0) β (x.getArg! 2))
        return .continue
      -- `f <$> x`
      if e.isAppOfArity ``Functor.map 6 then
        let m := e.getArg! 0
        let β := e.getArg! 3
        let f := e.getArg! 4
        let x := e.getArg! 5
        let some u := (e.getAppFn.constLevels!)[0]? | return .continue
        if m.isConstOf ``Id then return .visit (f.beta #[x])
        if m.isConstOf ``Option then
          if x.isAppOfArity ``Option.some 2 then
            return .visit (mkApp2 (mkConst ``Option.some [u]) β (f.beta #[x.getArg! 1]))
          if x.isAppOfArity ``Option.none 1 then return .visit (mkApp (mkConst ``Option.none [u]) β)
        if m.isAppOfArity ``Except 1 then
          let some v := (m.getAppFn.constLevels!)[0]? | return .continue
          if x.isAppOfArity ``Except.ok 3 then
            return .visit (mkApp3 (mkConst ``Except.ok [v, u]) (m.getArg! 0) β (f.beta #[x.getArg! 2]))
          if x.isAppOfArity ``Except.error 3 then
            return .visit (mkApp3 (mkConst ``Except.error [v, u]) (m.getArg! 0) β (x.getArg! 2))
        return .continue
      return .continue)
  Core.betaReduce e

/-- Whether `e` is, up to projections, an `if` or a `match` (a value chosen by a branch, not a
record with a branch in a field). -/
def hasBranchHead (e : Expr) (depth : Nat := 64) : MetaM Bool := do
  match depth with
  | 0 => return false
  | depth + 1 =>
  let e := e.consumeMData
  if e.isAppOf ``ite || e.isAppOf ``dite then return true
  if let .const n _ := e.getAppFn then
    if (Lean.Meta.Match.Extension.getMatcherInfo? (← getEnv) n).isSome then return true
  if let .proj _ _ b := e then return ← hasBranchHead b depth
  if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 ||
      e.isAppOfArity ``MProd.fst 3 || e.isAppOfArity ``MProd.snd 3 then
    return ← hasBranchHead (e.getArg! 2) depth
  return false

/-! ## Results of a path -/

/-- What a computation in `Option` returns, if anything, satisfies `R`. -/
def OKo {α : Type u} (R : α → Prop) : Option α → Prop
  | none => True
  | some a => R a

/-- What a computation in `Except ε` returns, if it does not throw, satisfies `R`. -/
def OKe {ε α : Type u} (R : α → Prop) : Except ε α → Prop
  | .error _ => True
  | .ok a => R a

/-- A pure computation's value satisfies `R` (`R e`, kept apart so that `tx_vcg` can take `e` apart). -/
def OKp {α : Sort u} (R : α → Prop) (e : α) : Prop := R e

theorem OKp_ite {α : Sort u} {R : α → Prop} (c : Prop) [Decidable c] (a b : α)
    (h1 : c → OKp R a) (h2 : ¬c → OKp R b) : OKp R (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

theorem OKp_dite {α : Sort u} {R : α → Prop} (c : Prop) [Decidable c] (a : c → α) (b : ¬c → α)
    (h1 : ∀ hc : c, OKp R (a hc)) (h2 : ∀ hc : ¬c, OKp R (b hc)) : OKp R (if hc : c then a hc else b hc) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact h1 hc
  · rw [dif_neg hc]; exact h2 hc

theorem OKo_of {α : Type u} {R : α → Prop} {o : Option α} (h : OKo R o) {a : α} (ha : o = some a) : R a := by
  subst ha; exact h

theorem OKe_of {ε α : Type u} {R : α → Prop} {e : Except ε α} (h : OKe R e) {a : α} (ha : e = .ok a) : R a := by
  subst ha; exact h

theorem OKo_bind {α β : Type u} {R : β → Prop} (o : Option α) (k : α → Option β)
    (h : ∀ a, o = some a → OKo R (k a)) : OKo R (o >>= k) := by
  cases o with
  | none => trivial
  | some a => exact h a rfl

theorem OKe_bind {ε α β : Type u} {R : β → Prop} (e : Except ε α) (k : α → Except ε β)
    (h : ∀ a, e = .ok a → OKe R (k a)) : OKe R (e >>= k) := by
  cases e with
  | error _ => trivial
  | ok a => exact h a rfl

theorem OKo_ite {α : Type u} {R : α → Prop} (c : Prop) [Decidable c] (a b : Option α)
    (h1 : c → OKo R a) (h2 : ¬c → OKo R b) : OKo R (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

theorem OKe_ite {ε α : Type u} {R : α → Prop} (c : Prop) [Decidable c] (a b : Except ε α)
    (h1 : c → OKe R a) (h2 : ¬c → OKe R b) : OKe R (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

theorem OKo_dite {α : Type u} {R : α → Prop} (c : Prop) [Decidable c] (a : c → Option α) (b : ¬c → Option α)
    (h1 : ∀ hc : c, OKo R (a hc)) (h2 : ∀ hc : ¬c, OKo R (b hc)) : OKo R (if hc : c then a hc else b hc) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact h1 hc
  · rw [dif_neg hc]; exact h2 hc

theorem OKe_dite {ε α : Type u} {R : α → Prop} (c : Prop) [Decidable c] (a : c → Except ε α) (b : ¬c → Except ε α)
    (h1 : ∀ hc : c, OKe R (a hc)) (h2 : ∀ hc : ¬c, OKe R (b hc)) : OKe R (if hc : c then a hc else b hc) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact h1 hc
  · rw [dif_neg hc]; exact h2 hc

/-! ## Loops -/

/-- A `for` loop over a list in `Except ε`, with an invariant `I rest b` of the list `rest` left and
the state `b`, and `D` of the state an early exit leaves. -/
theorem OKe_forIn_list {ε β : Type u} (l : List Nat) (init : β)
    (f : Nat → β → Except ε (ForInStep β)) (Q : β → Prop)
    (I : List Nat → β → Prop) (D : β → Prop)
    (h0 : I l init)
    (hstep : ∀ i rest b, I (i :: rest) b →
      OKe (fun s => match s with | .yield b' => I rest b' | .done b' => D b') (f i b))
    (hend : ∀ b, I [] b → Q b) (hdone : ∀ b, D b → Q b) :
    OKe Q (forIn l init f) := by
  induction l generalizing init with
  | nil => simpa [forIn] using hend _ h0
  | cons i rest ih =>
    rw [List.forIn_cons]
    have hs := hstep i rest init h0
    revert hs
    cases f i init with
    | error e => intro _; trivial
    | ok s =>
      intro hs
      cases s with
      | done b' => exact hdone b' hs
      | yield b' => exact ih b' hs

/-- A `for i in [:n]` loop in `Except ε` followed by `k`: with an invariant `I i b` of the state `b`
before iteration `i`, and `D` of the state an early exit (`return`, `break`) leaves. -/
theorem OKe_forIn_range {ε β γ : Type u} (n : Nat) (init : β)
    (f : Nat → β → Except ε (ForInStep β)) (k : β → Except ε γ) (R : γ → Prop)
    (I : Nat → β → Prop) (D : β → Prop)
    (h0 : I 0 init)
    (hstep : ∀ i b, i < n → I i b →
      OKe (fun s => match s with | .yield b' => I (i + 1) b' | .done b' => D b') (f i b))
    (hk : ∀ b, I n b ∨ D b → OKe R (k b)) :
    OKe R (forIn [:n] init f >>= k) := by
  apply OKe_bind
  intro b hb
  apply hk
  have key : OKe (fun b => I n b ∨ D b) (forIn [:n] init f) := by
    rw [Std.Range.forIn_eq_forIn_range']
    simp only [Std.Range.size]
    apply OKe_forIn_list (I := fun l b => ∃ j, l = List.range' j (n - j) 1 ∧ j ≤ n ∧ I j b)
    · exact ⟨0, by simp, Nat.zero_le _, h0⟩
    · intro i rest b ⟨j, hl, hj, hI⟩
      have hjn : j < n := by
        rcases Nat.lt_or_ge j n with h | h
        · exact h
        · rw [show n - j = 0 by omega] at hl; simp at hl
      rw [show n - j = (n - (j + 1)) + 1 by omega, List.range'_succ] at hl
      injection hl with hi hrest
      subst hi
      have := hstep i b hjn hI
      revert this
      cases f i b with
      | error e => intro _; trivial
      | ok s =>
        intro hs
        cases s with
        | done b' => exact hs
        | yield b' => exact ⟨i + 1, by simpa using hrest, hjn, hs⟩
    · intro b ⟨j, hl, hj, hI⟩
      left
      have : n - j = 0 := by
        rcases Nat.eq_zero_or_pos (n - j) with h | h
        · exact h
        · rw [show n - j = (n - j - 1) + 1 by omega, List.range'_succ] at hl; simp at hl
      have : j = n := by omega
      subst this; exact hI
    · intro b hb; exact Or.inr hb
  exact OKe_of key hb

/-! ## The generator of path goals -/

/-- The kind of a goal: `OKo R e` (`Option`), `OKe R e` (`Except`) or `OKp R e` (pure). -/
inductive Kind where
  | opt | exc | pure
  deriving BEq

/-- The kind, the predicate `R` and the computation `e` of a goal `OKo R e`, `OKe R e`, `OKp R e`. -/
def spine? (t : Expr) : Option (Kind × Expr × Expr) :=
  let t := t.consumeMData
  if t.isAppOfArity ``OKo 3 then some (.opt, t.getArg! 1, t.getArg! 2)
  else if t.isAppOfArity ``OKe 4 then some (.exc, t.getArg! 2, t.getArg! 3)
  else if t.isAppOfArity ``OKp 3 then some (.pure, t.getArg! 1, t.getArg! 2)
  else none

/-- The goal `OK? R e` of kind `k`. -/
def mkOK (k : Kind) (r e : Expr) : MetaM Expr :=
  match k with
  | .opt => mkAppM ``OKo #[r, e]
  | .exc => mkAppM ``OKe #[r, e]
  | .pure => mkAppM ``OKp #[r, e]

def Kind.lemma (k : Kind) (opt exc pure : Name) : Name :=
  match k with
  | .opt => opt
  | .exc => exc
  | .pure => pure

/-- Replace the goal's target by `reduceExpr` of it. -/
def reduceTarget (g : MVarId) (keepJps : Bool := false) : MetaM (Option MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let t' ← reduceExpr t keepJps
  if t' == t then return none
  return some (← g.replaceTargetDefEq t')

/-- Apply `lemma` to `g` and introduce `n` binders in each new goal. -/
def applyIntro (g : MVarId) (lemma : Name) (n : Nat) : MetaM (List MVarId) := g.withContext do
  let gs ← g.apply (← mkConstWithFreshMVarLevels lemma)
  let mut out := []
  for g' in gs do
    if ← g'.isAssigned then continue
    -- instance arguments are solved by unification; the rest are the branches
    let ty ← instantiateMVars (← g'.getType)
    if ty.isForall then
      let (_, g'') ← g'.introNP n
      out := out ++ [g'']
    else
      out := out ++ [g']
  return out

/-- Case on the `Decidable` instance `inst` in the target: each `if` with that instance is then
decided (`reduceExpr` picks its branch) and its condition or its negation is a hypothesis. -/
def casesTarget (g : MVarId) (inst : Expr) : MetaM (Option (List MVarId)) := g.withContext do
  let st ← saveState
  try
    let (fvars, g) ← g.generalize #[{ expr := inst, xName? := `d }]
    let subgoals ← g.cases fvars[0]!
    return some (subgoals.toList.map (·.mvarId))
  catch _ =>
    st.restore
    return none

/-- If `v` is chosen by a branch (up to projections), split that branch in the goal. -/
def splitBranchIn (g : MVarId) (v : Expr) : MetaM (Option (List MVarId)) := g.withContext do
  if !(← hasBranchHead v) then return none
  if let some ite ← findSplit? v .ite then
    if ite.getAppNumArgs < 3 then return none
    let inst := ite.getArg! 2
    if !inst.hasLooseBVars then
      if let some gs ← casesTarget g inst then return some gs
  if let some m ← findSplit? v .match then
    if !m.hasLooseBVars then
      let st ← saveState
      try
        return some (← Lean.Meta.Split.splitMatch g m)
      catch _ => st.restore
  return none

/-- One step on a goal `OKo R e` / `OKe R e`: `none` if `e` is not taken apart further. -/
def vcgStep (g : MVarId) (keepJps : Bool := false) : MetaM (Option (List MVarId)) := g.withContext do
  if let some g' ← reduceTarget g keepJps then return some [g']
  let t ← instantiateMVars (← g.getType)
  let some (k, r, e) := spine? t | return none
  let e := e.consumeMData
  -- a call of a join point with a specification `∀ xs, hyps → OK R (jp xs)` in the context
  if let .fvar jp := e.getAppFn then
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if !ty.isForall then continue
      let (xs, _, body) ← forallMetaTelescopeReducing ty
      let some (_, _, e') := spine? body | continue
      if e'.getAppFn != .fvar jp then continue
      if ← isDefEq body t then
        let mut out := []
        for x in xs do
          if let .mvar m := x then
            if !(← m.isAssigned) then out := out ++ [m]
        g.assign (mkAppN d.toExpr xs)
        return some out
    if k != .pure then return none
  -- a join point kept (`keepJps`): stop
  if let .letE n ty _ _ _ := e then
    if keepJps && n.eraseMacroScopes.toString.startsWith "__do_jp" && jpArity ty ≥ 1 then return none
  -- `let x := v; b`: split `v` if it is a branch, else introduce `x` as a local definition
  if let .letE n ty v b _ := e then
    -- a record or a tuple chosen by a branch is split (its fields matter); any other value is kept
    -- as a local definition (a `match` on it splits it where it is tested, keeping its equation)
    let isStruct ← do
      let ty' ← whnfR ty
      match ty'.getAppFn with
      | .const sn _ => pure (getStructureInfo? (← getEnv) sn).isSome
      | _ => pure false
    if isStruct then
      if let some gs ← splitBranchIn g v then return some gs
    let t' ← withLetDecl n ty v fun x => do
      mkLetFVars #[x] (← mkOK k r (b.instantiate1 x)) (usedLetOnly := false)
    let g ← g.replaceTargetDefEq t'
    let (_, g) ← g.intro1P
    return some [g]
  if e.isAppOfArity ``ite 5 then
    return some (← applyIntro g (k.lemma ``OKo_ite ``OKe_ite ``OKp_ite) 1)
  if e.isAppOfArity ``dite 5 then
    return some (← applyIntro g (k.lemma ``OKo_dite ``OKe_dite ``OKp_dite) 1)
  if k != .pure && e.isAppOfArity ``Bind.bind 6 && !(← isCtorApp (e.getArg! 4)) then
    -- a loop: left for `OKe_forIn_range` with its invariant
    if (e.getArg! 4).consumeMData.isAppOf ``ForIn.forIn then return none
    if let some gs ← splitBranchIn g (e.getArg! 4) then return some gs
    return some (← applyIntro g (k.lemma ``OKo_bind ``OKe_bind ``OKo_bind) 2)
  if let .const mn _ := e.getAppFn then
    if let some mi ← getMatcherInfo? mn then
      if e.getAppNumArgs < mi.getFirstAltPos + mi.numAlts then return none
      for i in [0:mi.numDiscrs] do
        if let some gs ← splitBranchIn g (e.getArg! (mi.getFirstDiscrPos + i)) then return some gs
      -- a discriminant that is a local definition becomes a variable with its equation
      for i in [0:mi.numDiscrs] do
        if let .fvar x := (e.getArg! (mi.getFirstDiscrPos + i)).consumeMData then
          if let some v ← x.getValue? then
            let st ← saveState
            try
              let ty ← mkEq (.fvar x) (← instantiateMVars v)
              let (_, g') ← g.assertHypotheses #[{ userName := `hdef, type := ty, value := ← mkEqRefl (.fvar x) }]
              return some [← g'.clearValue x]
            catch _ => st.restore
      let st ← saveState
      try
        return some (← Lean.Meta.Split.splitMatch g e)
      catch _ =>
        st.restore
        return none
  match k with
  | .pure =>
    -- the value: the goal is `R e`
    return some [← g.replaceTargetDefEq (r.beta #[e]).headBeta]
  | _ =>
    -- `none` / `.error _`: nothing to show
    if e.isAppOfArity ``Option.none 1 || e.isAppOfArity ``Except.error 3 then
      g.assign (mkConst ``True.intro)
      return some []
    -- `some a` / `.ok a`: the goal is `R a`
    if e.isAppOfArity ``Option.some 2 || e.isAppOfArity ``Except.ok 3 then
      return some [← g.replaceTargetDefEq (r.beta #[e.appArg!]).headBeta]
    return none

/-- `vcgStep` until no step applies, at most `fuel` steps along each path. -/
def vcgLoop (g : MVarId) (fuel : Nat) (keepJps : Bool := false) : MetaM (List MVarId) := do
  match fuel with
  | 0 => return [g]
  | fuel + 1 =>
  match ← vcgStep g keepJps with
  | none => return [g]
  | some gs => return (← gs.mapM (vcgLoop · fuel keepJps)).flatten

syntax (name := txVcg) "tx_vcg" ("(" &"fuel" " := " num ")")? (&" keep_jps")? : tactic

/-- `tx_vcg`: on a goal `OKo R e` or `OKe R e`, one goal per path through the code `e` (its
conditions as hypotheses, its `let`s as local definitions, its result `a` in a goal `R a`).
`tx_vcg (fuel := n)` stops each path after `n` steps. With `keep_jps`, the join points that carry
state (`do` blocks with `let mut`) are not inlined: the goal stops at their definition, for
`tx_jp_inline` or `tx_jp_spec`. -/
@[tactic txVcg] def evalTxVcg : Tactic := fun stx => do
  let fuel := if stx[1].getNumArgs == 0 then 100000 else stx[1][3].isNatLit?.getD 100000
  let keepJps := stx[2].getNumArgs != 0
  let gs ← vcgLoop (← getMainGoal) fuel keepJps
  replaceMainGoal gs

/-- The join point defined at the head of the computation of the goal: its name, type, value and
the computation after it. -/
def headJp? (g : MVarId) : MetaM (Option (Kind × Expr × Name × Expr × Expr × Expr)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (k, r, e) := spine? t | return none
  let .letE n ty v b _ := e.consumeMData | return none
  return some (k, r, n, ty, v, b)

/-- `tx_jp_inline`: inline the join point at the head of the computation (then continue with
`tx_vcg keep_jps`). -/
elab "tx_jp_inline" : tactic => do
  let g ← getMainGoal
  let some (k, r, _, _, v, b) ← headJp? g | throwError "tx_jp_inline: no join point"
  let e' := b.instantiate1 v
  let t' ← g.withContext do mkOK k r e'
  let g ← g.replaceTargetDefEq t'
  let gs ← vcgLoop g 100000 true
  replaceMainGoal gs

/-- Apply the specification rule to the join point at the head of `g` with the invariants
`invs` (see `tx_jp_spec`): the goal for the body and the goal for the rest, arguments and
hypotheses introduced. -/
def jpSpec (g : MVarId) (invs : Array Expr) : MetaM (Option (MVarId × MVarId)) := do
  let some (k, r, n, ty, v, b) ← headJp? g | return none
  g.withContext do
    -- every argument carrying state must have an invariant
    let covered ← forallTelescopeReducing ty fun xs _ => xs.allM fun x => do
      let xt ← inferType x
      if xt.isAppOf ``PUnit || xt.isConstOf ``Unit then return true
      invs.anyM fun inv => do
        let it ← inferType inv
        match it with
        | .forallE _ dom _ _ => isDefEq dom xt
        | _ => return false
    if !covered then return none
    let ok (e : Expr) : MetaM Expr := mkOK k r e
    let spec (jp : Expr) : MetaM Expr := forallTelescopeReducing ty fun xs _ => do
      let mut hyps : Array Expr := #[]
      for x in xs do
        let xt ← inferType x
        for inv in invs do
          let it ← inferType inv
          if let .forallE _ dom _ _ := it then
            if ← isDefEq dom xt then hyps := hyps.push (mkApp inv x).headBeta
      let body ← ok (mkAppN jp xs)
      mkForallFVars xs (← hyps.foldrM (fun h acc => mkArrow h acc) body)
    let specV ← spec v
    let g1 ← mkFreshExprSyntheticOpaqueMVar specV
    let restT ← withLocalDeclD n ty fun jp => do
      let s ← spec jp
      mkForallFVars #[jp] (← mkArrow s (← ok (b.instantiate1 jp)))
    let g2 ← mkFreshExprSyntheticOpaqueMVar restT
    g.assign (mkApp2 g2 v g1)
    let (_, g1') ← g1.mvarId!.intros
    let (_, g2') ← g2.mvarId!.intros
    return some (g1', g2')

/-- `vcgLoop` with every join point that carries state specified with the invariants `invs`. -/
def vcgSpecLoop (g : MVarId) (invs : Array Expr) (depth : Nat := 1000) (fuel : Nat := 100000) :
    MetaM (List MVarId) := do
  match depth with
  | 0 => return [g]
  | depth + 1 =>
  let gs ← vcgLoop g fuel true
  let mut out := []
  for g in gs do
    match ← jpSpec g invs with
    | some (g1, g2) => out := out ++ (← vcgSpecLoop g1 invs depth fuel) ++ (← vcgSpecLoop g2 invs depth fuel)
    | none =>
      -- a join point without invariants for its arguments is inlined
      match ← headJp? g with
      | some (k, r, _, _, v, b) =>
        let g' ← g.withContext do g.replaceTargetDefEq (← mkOK k r (b.instantiate1 v))
        out := out ++ (← vcgSpecLoop g' invs depth fuel)
      | none => out := out ++ [g]
  return out

/-- `tx_jp_spec [inv₁, ...]`: for the join point `jp := f` at the head of the computation, prove
once that `f xs` satisfies the goal's predicate for all arguments `xs` satisfying the invariants
(`invᵢ x` for each argument `x` of the type of `invᵢ`), then use that at each call. Two goals
(then `tx_vcg keep_jps` on each): the body under the invariants, and the rest, where each call
leaves the invariants of its arguments to prove. -/
elab "tx_jp_spec" " [" invs:term,* "]" : tactic => do
  let g ← getMainGoal
  let invs ← g.withContext do
    let invs ← invs.getElems.mapM fun i => Term.elabTerm i none
    invs.mapM instantiateMVars
  let some (g1, g2) ← jpSpec g invs | throwError "tx_jp_spec: no join point"
  let gs1 ← vcgLoop g1 100000 true
  let gs2 ← vcgLoop g2 100000 true
  replaceMainGoal (gs1 ++ gs2)

/-- `tx_vcg_inv [inv₁, ...]`: `tx_vcg`, every join point that carries state being specified with
the same invariants (`tx_jp_spec`). The goals left are the results of the paths and the
invariants at the calls of join points. -/
elab "tx_vcg_inv" " [" invs:term,* "]" : tactic => do
  let g ← getMainGoal
  let invs ← g.withContext do
    let invs ← invs.getElems.mapM fun i => Term.elabTerm i none
    invs.mapM instantiateMVars
  replaceMainGoal (← vcgSpecLoop g invs)

end TvmLean.Proofs.TxTac

namespace TvmLean.Proofs.TxTac
open Lean Meta Elab Tactic

/-! ## Closing the goals of the paths -/

/-- The kind and computation of the conclusion of a specification lemma `∀ xs, OK? R c`. -/
def specOf? (concl : Expr) : Option (Kind × Expr × Expr) := spine? concl

/-- The closed subterms of `e` that are applications of the constant `f` (at most `fuel` nodes
deep). -/
def appsOfAux (f : Name) (fuel : Nat) (e : Expr) (acc : Array Expr) : Array Expr :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    let acc := if e.isAppOf f && !e.hasLooseBVars then acc.push e else acc
    match e with
    | .app a b => appsOfAux f fuel b (appsOfAux f fuel a acc)
    | .lam _ t b _ | .forallE _ t b _ => appsOfAux f fuel b (appsOfAux f fuel t acc)
    | .letE _ t v b _ => appsOfAux f fuel b (appsOfAux f fuel v (appsOfAux f fuel t acc))
    | .mdata _ b | .proj _ _ b => appsOfAux f fuel b acc
    | _ => acc

/-- The closed subterms of `e` that are applications of the constant `f`. -/
def appsOf (f : Name) (e : Expr) : Array Expr := appsOfAux f 10000 e #[]

/-- `tx_specs [L₁, ...]`, each `Lᵢ : ∀ xs, OK? R (f ...)`: add `R r` for each hypothesis
`f ... = some r` / `f ... = .ok r` of the goal; when `Lᵢ` is about a pure function (`OKp`), add
`R v` for each local definition `x := v` and `R (f ...)` for each call `f ...` in the value of a
local definition or in a hypothesis. -/
elab "tx_specs" " [" ls:ident,* "]" : tactic => withMainContext do
  let mut g ← getMainGoal
  for l in ls.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo l
    let lctx ← getLCtx
    -- the head constant of the lemma's computation
    let head? ← do
      let (_, _, concl) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels name))
      pure ((specOf? concl).bind fun (_, _, c) => c.getAppFn.constName?)
    let mut seen : Array Expr := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      -- the candidates: the value of a local definition (then `R x`), calls of the head constant in
      -- it or in a hypothesis (then `R call`), the left-hand side of a hypothesis `call = some r`
      let mut cands : Array (Expr × Expr) := #[]
      if let some v := d.value? then cands := cands.push (v, d.toExpr)
      if let some f := head? then
        let src ← instantiateMVars (if let some v := d.value? then v else d.type)
        for a in appsOf f src do cands := cands.push (a, a)
      for (cand, subj) in cands do
        if seen.contains subj then continue
        let found ← g.withContext do
          let lemmaConst ← mkConstWithFreshMVarLevels name
          let (xs, _, concl) ← forallMetaTelescope (← inferType lemmaConst)
          let some (k, r, c) := specOf? concl | return none
          if k != .pure then return none
          if !(← isDefEq c cand) then return none
          let ty ← instantiateMVars (r.beta #[subj])
          if ty.hasExprMVar then return none
          return some (ty, ← instantiateMVars (mkAppN lemmaConst xs))
        if let some (ty, pf) := found then
          seen := seen.push subj
          let (_, g') ← g.withContext do g.assertHypotheses #[{ userName := `hspec, type := ty, value := pf }]
          g := g'
      if d.isLet then continue
      let found ← g.withContext do
        let lemmaConst ← mkConstWithFreshMVarLevels name
        let (xs, _, concl) ← forallMetaTelescope (← inferType lemmaConst)
        let some (k, r, c) := specOf? concl | return none
        let lemmaApp := mkAppN lemmaConst xs
        if k == .pure then return none
        let ty ← instantiateMVars d.type
        let some (_, lhs, rhs) := ty.consumeMData.eq? | return none
        let rhs := rhs.consumeMData
        let res? : Option Expr :=
          if k == .opt && rhs.isAppOfArity ``Option.some 2 then some rhs.appArg!
          else if k == .exc && rhs.isAppOfArity ``Except.ok 3 then some rhs.appArg!
          else none
        let some res := res? | return none
        if !(← isDefEq c lhs) then return none
        let ty ← instantiateMVars (r.beta #[res])
        if ty.hasExprMVar then return none
        let ofLemma := if k == .opt then ``OKo_of else ``OKe_of
        let pf ← mkAppM ofLemma #[← instantiateMVars lemmaApp, d.toExpr]
        return some (ty, pf)
      if let some (ty, pf) := found then
        let (_, g') ← g.withContext do g.assertHypotheses #[{ userName := `hspec, type := ty, value := pf }]
        g := g'
  replaceMainGoal [g]

/-- `tx_destruct`: split the hypotheses that are conjunctions, existentials or disjunctions (one
goal for each side), also behind reducible definitions. -/
elab "tx_destruct" : tactic => withMainContext do
  let g ← getMainGoal
  let gs ← g.casesRec fun d => do
    if d.isLet || d.isImplementationDetail then return false
    let ty ← whnfR (← instantiateMVars d.type)
    return ty.isAppOf ``And || ty.isAppOf ``Exists || ty.isAppOf ``Or
  replaceMainGoal gs

/-- Normalize `f x` for a record `x`: projections through local definitions and constructors. -/
def projNorm (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  -- an `Expr.proj` of a variable back to the projection function
  if let .proj sn i b := e then
    if let some si := getStructureInfo? (← getEnv) sn then
      if h : i < si.fieldNames.size then
        let pn := sn ++ si.fieldNames[i]
        return ← mkAppOptM pn ((Array.replicate ((← getConstInfo pn).type.getForallBinderNames.length - 1) none).push (some b))
  return e

/-- `tx_abstract [f₁, ...]`: for each local definition `x` whose value is a record (a structure with
at least four fields), the equations `fᵢ x = v` (`v` the value of `fᵢ x` followed through projections
and local definitions), for the functions `fᵢ` that apply to it: facts `simp` can use without
unfolding the definitions. -/
elab "tx_abstract" " [" fs:term,* "]" : tactic => withMainContext do
  let mut g ← getMainGoal
  let fs ← fs.getElems.mapM fun f => do instantiateMVars (← Term.elabTerm f none)
  -- the equations, computed while every definition still has its value
  let mut eqs : Array Hypothesis := #[]
  let mut recs : Array FVarId := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail || !d.isLet then continue
    let v ← instantiateMVars d.value
    if (← recordCtor? v).isNone then continue
    recs := recs.push d.fvarId
    for f in fs do
      let fty ← inferType f
      let .forallE _ dom _ _ := fty | continue
      if !(← isDefEq dom d.type) then continue
      let lhs := (mkApp f d.toExpr).headBeta
      let rhs ← projNorm lhs
      if rhs == lhs then continue
      eqs := eqs.push { userName := `hrec, type := ← mkEq lhs rhs, value := ← mkEqRefl lhs }
  let (_, g') ← g.assertHypotheses eqs
  replaceMainGoal [g']

/-- `tx_clear_values`: turn the local definitions into variables: the equation `x = v` of each
local definition whose value is not a record is kept as a hypothesis (for a record, `tx_abstract`
gives the equations of its fields), then the values are cleared. What is left is a goal over
variables and equations, for `grind`. -/
elab "tx_clear_values" : tactic => do
  let mut g ← getMainGoal
  let eqs ← g.withContext do
    let mut eqs : Array Hypothesis := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || !d.isLet then continue
      let v ← instantiateMVars d.value
      if (← recordCtor? v).isSome then continue
      if (← inferType d.type).isProp then continue
      eqs := eqs.push { userName := `hlet, type := ← mkEq d.toExpr v, value := ← mkEqRefl d.toExpr }
    return eqs
  let (_, g') ← g.assertHypotheses eqs
  g := g'
  let lctx ← g.withContext getLCtx
  for d in lctx.decls.toArray.reverse do
    let some d := d | continue
    if d.isImplementationDetail || !d.isLet then continue
    try g ← g.clearValue d.fvarId catch _ => pure ()
  replaceMainGoal [g]

/-- `tx_unfold [d₁, ...]`: unfold each definition `dᵢ` everywhere it occurs (none of them need
occur). -/
elab "tx_unfold" " [" ds:ident,* "]" : tactic => do
  for d in ds.getElems do
    evalTactic (← `(tactic| try unfold $d:ident at *))

/-- `tx_close [f₁, ...] [d₁, ...]`: close a goal of a path with `grind`, after `tx_abstract [f₁, ...]`
(the fields of the records that matter), `tx_clear_values` and `tx_unfold [d₁, ...]` (the
definitions of the statement). -/
macro "tx_close" " [" fs:term,* "]" " [" ds:ident,* "]" : tactic =>
  `(tactic| (tx_abstract [$fs,*]; tx_clear_values; tx_unfold [$ds,*]; (try dsimp only at *); grind))

end TvmLean.Proofs.TxTac

namespace TvmLean.Proofs.TxTac
open Lean Meta Elab Tactic

/-- Close `g` by an assumption (up to definitional unfolding). -/
def assumptionCore (g : MVarId) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  for d in (← getLCtx) do
    if d.isImplementationDetail || d.isLet then continue
    let st ← saveState
    if ← isDefEq d.type ty then
      g.assign d.toExpr
      return true
    st.restore
  return false

/-- The hypotheses that close `g` (each tried in turn by `solveList`). -/
def hypsFor (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail || d.isLet then continue
    out := out.push d.toExpr
  return out

/-- A small prover for the goals of the paths, with backtracking over the list of pending goals:
conjunctions, disjunctions (left, then right), existentials (the witness found by unification),
implications and `∀` (introduced), equations (a hypothesis either way round, or `rfl` up to
definitional unfolding), `True`, any other goal by a hypothesis, and definitions at the head
unfolded. `fuel` bounds the steps. -/
def solveList (gs : List MVarId) (fuel : Nat) (dbg : Bool) : MetaM Bool := do
  match gs, fuel with
  | [], _ => return true
  | _ :: _, 0 => return false
  | g :: rest, fuel + 1 =>
  if ← g.isAssigned then return ← solveList rest fuel dbg
  g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  -- a goal without metavariables is proved on its own (no backtracking into it)
  if !rest.isEmpty && !ty.hasExprMVar then
    if ← solveList [g] fuel dbg then return ← solveList rest fuel dbg
    return false
  -- try one alternative: run `act` (which assigns `g` and returns new goals), then the rest
  let attempt (act : MetaM (Option (List MVarId))) : MetaM Bool := do
    let st ← saveState
    try
      if let some new := ← act then
        if ← solveList (new ++ rest) fuel dbg then return true
    catch _ => pure ()
    st.restore
    return false
  if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return ← solveList rest fuel dbg
  if ty.isAppOfArity ``And 2 then
    return ← attempt do
      let a ← mkFreshExprMVar (ty.getArg! 0)
      let b ← mkFreshExprMVar (ty.getArg! 1)
      g.assign (← mkAppM ``And.intro #[a, b])
      return some [a.mvarId!, b.mvarId!]
  if ty.isAppOfArity ``Or 2 then
    for (i, side) in [(0, ``Or.inl), (1, ``Or.inr)] do
      if ← attempt (do
          let a ← mkFreshExprMVar (ty.getArg! i)
          g.assign (← mkAppOptM side #[ty.getArg! 0, ty.getArg! 1, a])
          return some [a.mvarId!]) then return true
    return false
  if ty.isAppOfArity ``Exists 2 then
    return ← attempt do
      let p := ty.getArg! 1
      let w ← mkFreshExprMVar (ty.getArg! 0)
      let body ← mkFreshExprMVar (p.beta #[w]).headBeta
      g.assign (← mkAppOptM ``Exists.intro #[ty.getArg! 0, p, w, body])
      return some [body.mvarId!]
  if ty.isForall then
    return ← attempt do
      let (_, g') ← g.intro1P
      return some [g']

  -- hypotheses (for an equation, either way round), those with the same heads first
  let headOk (x y : Expr) : Bool :=
    let x := x.consumeMData
    let y := y.consumeMData
    x.isMVar || y.isMVar || x.getAppFn.isMVar || y.getAppFn.isMVar ||
      (x.getAppFn.isConst && x.getAppFn == y.getAppFn) || (x.isFVar || y.isFVar) ||
      (!x.getAppFn.isConst && !y.getAppFn.isConst)
  for h in ← hypsFor g do
    let hty ← instantiateMVars (← inferType h)
    let cheap : Bool := match hty.consumeMData.eq?, ty.eq? with
      | some (_, c, d), some (_, a, b) => headOk c a && headOk d b
      | _, _ => hty.consumeMData.getAppFn == ty.getAppFn
    if !cheap then continue
    if ← attempt (do
        if ← isDefEq hty ty then
          g.assign h
          return some []
        return none) then return true
  if let some (_, a, b) := ty.eq? then
    for h in ← hypsFor g do
      let hty ← instantiateMVars (← inferType h)
      let some (_, c, d) := hty.consumeMData.eq? | continue
      if !(headOk c b && headOk d a) then continue
      if ← attempt (do
          if (← isDefEq c b) && (← isDefEq d a) then
            g.assign (← mkEqSymm h)
            return some []
          return none) then return true
    if ← attempt (do
        if ← isDefEq a b then
          g.assign (← mkEqRefl a)
          return some []
        return none) then return true
  -- unfold a definition at the head
  if let .const n _ := ty.getAppFn then
    if (← getConstInfo n).isDefinition then
      if let some ty' ← unfoldDefinition? ty then
        return ← attempt do
          let g' ← g.replaceTargetDefEq ty'
          return some [g']
  if dbg then IO.eprintln s!"tx_solve: no proof of {← ppExpr ty}"
  return false

/-- `tx_solve_dbg`: `tx_solve`, logging the goals it finds no proof of. -/
elab "tx_solve_dbg" : tactic => do
  let g ← getMainGoal
  if ← solveList [g] 2000 true then replaceMainGoal [] else throwError "tx_solve failed"

/-- `tx_solve`: close the goal with `solve` (see there), or fail. -/
elab "tx_solve" : tactic => do
  let g ← getMainGoal
  if ← solveList [g] 2000 false then replaceMainGoal [] else throwError "tx_solve failed"

end TvmLean.Proofs.TxTac

namespace TvmLean.Proofs.TxTac
open Lean Meta Elab Tactic

/-- `tx_goals`: log the number of goals and the head of each target (for developing proofs). -/
elab "tx_goals" : tactic => do
  let gs ← getGoals
  let mut heads : Std.HashMap String Nat := {}
  for g in gs do
    let ty ← g.withContext do instantiateMVars (← g.getType)
    let s := toString (← g.withContext do ppExpr ty)
    let key := (s.take 60).replace "\n" " "
    heads := heads.insert key ((heads.getD key 0) + 1)
  logInfo m!"{gs.length} goals: {heads.toList}"

end TvmLean.Proofs.TxTac

namespace TvmLean.Proofs.TxTac
open Lean Meta Elab Tactic

/-- `tx_show`: log each goal compactly: the hypotheses that are not local definitions of records,
each cut at 160 characters, and the target (for developing proofs). -/
elab "tx_show" : tactic => do
  let gs ← getGoals
  let mut out : MessageData := m!""
  let mut i := 0
  for g in gs do
    i := i + 1
    let s ← g.withContext do
      let mut lines : Array String := #[]
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        let tyS := toString (← ppExpr ty)
        let valS ← match d.value? with
          | some v =>
            if (← recordCtor? v).isSome then pure " := <record>"
            else pure (" := " ++ (toString (← ppExpr v)).take 100)
          | none => pure ""
        lines := lines.push (((toString d.userName) ++ " : " ++ tyS).take 160 ++ valS)
      let tgt := toString (← ppExpr (← instantiateMVars (← g.getType)))
      pure (String.intercalate "\n" lines.toList ++ "\n⊢ " ++ tgt.take 300)
    out := out ++ m!"=== goal {i}\n{s}\n"
  logInfo out

end TvmLean.Proofs.TxTac

namespace TvmLean.Proofs.TxTac
open Lean Meta Elab Tactic

/-- `cases` on the term `x` of the hypothesis `h` (generalized there), keeping the equation
`x = c` for each constructor `c` (not for a `Decidable` instance). -/
def casesInHyp (g : MVarId) (h : FVarId) (x : Expr) : MetaM (List MVarId) := g.withContext do
  let (reverted, g) ← g.revert #[h] (preserveOrder := true)
  let isDec := (← whnfR (← inferType x)).isAppOf ``Decidable
  let (fvars, g) ← g.generalize #[{ expr := x, xName? := `r, hName? := if isDec then none else some `hx }]
  let subgoals ← g.cases fvars[0]!
  let mut out := []
  for sg in subgoals do
    let (_, g') ← sg.mvarId.introNP reverted.size
    out := out ++ [g']
  return out

/-- `tx_split_hyps`: take apart the hypotheses that are equations: `if`s by cases on their
`Decidable` instance, `match`es by cases on their discriminants (keeping the equation of the
discriminant), with the reductions of `reduceExpr`; equations between constructors injected,
equations of a variable substituted. -/
def splitHypsLoop (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := do
  match fuel with
  | 0 => return [g]
  | fuel + 1 =>
  let step? : MetaM (Option (List MVarId)) := g.withContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail || d.isLet then continue
      let ty ← instantiateMVars d.type
      let some (_, a, b) := ty.consumeMData.eq? | continue
      -- reductions
      let ty' ← reduceExpr ty
      if ty' != ty then return some [← g.changeLocalDecl d.fvarId ty' (checkDefEq := false)]
      -- `c₁ = c₂` with constructors: injection
      if (← isCtorApp a) && (← isCtorApp b) then
        let st ← saveState
        try
          match ← injection g d.fvarId with
          | .solved => return some []
          | .subgoal g' _ _ => return some [g']
        catch _ => st.restore
      -- `x = y` with a variable: substitute
      let isVar (e : Expr) : MetaM Bool := do
        match e.consumeMData with
        | .fvar x => return !(← x.getDecl).isLet
        | _ => return false
      if (← isVar a) || (← isVar b) then
        let st ← saveState
        try return some [← subst g d.fvarId] catch _ => st.restore
      -- an `if`: cases on its instance
      if let some ite ← findSplit? ty .ite then
        if ite.getAppNumArgs ≥ 3 && !(ite.getArg! 2).hasLooseBVars then
          let st ← saveState
          try return some (← casesInHyp g d.fvarId (ite.getArg! 2)) catch _ => st.restore
      -- a `match`: cases on its first discriminant that is not a constructor
      if let some m ← findSplit? ty .match then
        if let .const mn _ := m.getAppFn then
          if let some mi ← getMatcherInfo? mn then
            if m.getAppNumArgs ≥ mi.getFirstAltPos then
              for i in [0:mi.numDiscrs] do
                let x := m.getArg! (mi.getFirstDiscrPos + i)
                if x.hasLooseBVars then continue
                -- a constructor: its arguments that are not constructors (nested patterns)
                let cands ← if ← isCtorApp x then
                    x.consumeMData.getAppArgs.filterM fun a => do
                      return !a.hasLooseBVars && !(← isCtorApp a) && !(← isProp (← inferType a)) &&
                        !(← inferType a).isSort
                  else pure #[x]
                for c in cands do
                  let st ← saveState
                  try return some (← casesInHyp g d.fvarId c) catch _ => st.restore
    return none
  match ← step? with
  | none => return [g]
  | some gs => return (← gs.mapM (splitHypsLoop · fuel)).flatten

elab "tx_split_hyps" : tactic => do
  replaceMainGoal (← splitHypsLoop (← getMainGoal) 200)

end TvmLean.Proofs.TxTac

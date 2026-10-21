import Lean
import TvmLean.Proofs.WF.Defs

/-!
# The decoder keeps the code well-formed

`decodeCp0WithBits_WF`: decoding an instruction from a well-formed code slice gives a well-formed
instruction (`Instr.WF`: the cells and slices it carries, taken from the code) and a well-formed rest
of the code.

The decoder is one `do` block of about 2500 lines in the `Except` monad, which Lean elaborates into
some 600 nested join points (`have __do_jp := fun y => <the rest of the decoder>; <one branch>`).
Unfolding the join points would copy the rest of the decoder into every branch, so the proof walks
the term instead (`except_sat`, below): every `have` is kept abstract behind what it satisfies (a
join point, that every value it returns satisfies the postcondition, which is shown once, from its
definition; a value, that it equals its definition), conditions become hypotheses, and the slice
operations of the decoder are replaced by their specifications (`Slice.takeBitsAsNat_sat`, ...).
A join point called once (after the calls that follow a `throw` are dropped: a guard
`if !c then throw e`) is inlined instead, so that its code keeps the hypothesis of the guard. A
`match` on constructors is reduced; a `match` on natural number literals is unfolded to the chain
of `dite`s it is compiled to (its discriminants made variables, substituted in each branch; the
casts of the branches then reduce), since building its splitter is too slow for the literals of the
decoder; any other `match` is split. What is left are the `return`s of the decoder, each closed by
`decode_leaf`. The walk takes some 6000 steps; the whole proof about 90 seconds.

`Except.Sat`, `except_sat` and the slice specifications serve any proof about a program in the
`Except` monad of this shape (the dictionary functions, for example).
-/

namespace TvmLean

/-- Every value `x` returns satisfies `P`. -/
def Except.Sat {ε α : Type} (x : Except ε α) (P : α → Prop) : Prop :=
  ∀ a, x = .ok a → P a

namespace Except.Sat

variable {ε α β : Type}

theorem of_pure {P : α → Prop} {a : α} (h : P a) : Except.Sat (pure a : Except ε α) P := by
  intro b hb; cases hb; exact h

theorem of_throw {P : α → Prop} {e : ε} : Except.Sat (throw e : Except ε α) P := by
  intro b hb; cases hb

theorem of_error {P : α → Prop} {e : ε} : Except.Sat (Except.error e : Except ε α) P := by
  intro b hb; cases hb

theorem of_bind {P : β → Prop} {x : Except ε α} {f : α → Except ε β}
    (h : Except.Sat x fun a => Except.Sat (f a) P) : Except.Sat (x >>= f) P := by
  intro b hb
  cases hx : x with
  | error e => rw [hx] at hb; cases hb
  | ok a => rw [hx] at hb; exact h a hx b hb

theorem of_ite {P : α → Prop} {c : Prop} [Decidable c] {t e : Except ε α}
    (ht : c → Except.Sat t P) (he : ¬c → Except.Sat e P) : Except.Sat (if c then t else e) P := by
  by_cases hc : c
  · rw [if_pos hc]; exact ht hc
  · rw [if_neg hc]; exact he hc

theorem of_dite {P : α → Prop} {c : Prop} [Decidable c] {t : c → Except ε α} {e : ¬c → Except ε α}
    (ht : ∀ h : c, Except.Sat (t h) P) (he : ∀ h : ¬c, Except.Sat (e h) P) :
    Except.Sat (if h : c then t h else e h) P := by
  by_cases hc : c
  · rw [dif_pos hc]; exact ht hc
  · rw [dif_neg hc]; exact he hc

theorem mono {P Q : α → Prop} {x : Except ε α} (h : Except.Sat x P) (hq : ∀ a, P a → Q a) :
    Except.Sat x Q :=
  fun a ha => hq a (h a ha)

/-- A `have` (a join point or a value): what its value satisfies is shown once, and the body is
shown for any value that satisfies it. -/
theorem of_have {P : α → Prop} (v : β) (b : β → Except ε α) (inv : β → Prop) (hv : inv v)
    (hb : ∀ x, inv x → Except.Sat (b x) P) : Except.Sat (b v) P :=
  hb v hv

end Except.Sat

/-! ## The slice operations of the decoder -/

theorem Slice.takeBitsAsNat_sat {s : Slice} (hs : s.WF) {n : Nat} {Q : Nat × Slice → Prop}
    (h : ∀ v s', s'.WF → s'.cell = s.cell → s'.cell.bits.size = s.cell.bits.size →
      s'.cell.refs.size = s.cell.refs.size → s'.bitPos = s.bitPos + n → s'.refPos = s.refPos →
      s.bitPos + n ≤ s.cell.bits.size → Q (v, s')) :
    Except.Sat (s.takeBitsAsNat n) Q := by
  intro r hr
  unfold Slice.takeBitsAsNat at hr
  split at hr
  · rename_i hb
    rw [Slice.haveBits_iff] at hb
    cases hr
    exact h _ _ (Slice.advanceBits_WF hs hb) rfl rfl rfl rfl rfl hb
  · cases hr

theorem Slice.peekBitsAsNat_sat {s : Slice} {n : Nat} {Q : Nat → Prop} (h : ∀ v, Q v) :
    Except.Sat (s.peekBitsAsNat n) Q := by
  intro r _; exact h r

theorem Slice.takeRefInv_sat {s : Slice} (hs : s.WF) {Q : Cell × Slice → Prop}
    (h : ∀ c s', c.WF → s'.WF → s'.cell = s.cell → s'.cell.bits.size = s.cell.bits.size →
      s'.cell.refs.size = s.cell.refs.size → s'.bitPos = s.bitPos → s'.refPos = s.refPos + 1 →
      Q (c, s')) :
    Except.Sat s.takeRefInv Q := by
  intro r hr
  unfold Slice.takeRefInv at hr
  split at hr
  · rename_i hb
    rw [Slice.haveRefs_iff] at hb
    cases hr
    exact h _ _ (hs.ref! _) (Slice.withRefPos_WF hs hb) rfl rfl rfl rfl rfl
  · cases hr

theorem Slice.takeRefsInv_sat : ∀ (n : Nat) {s : Slice} {acc : Array Cell}, s.WF →
    (∀ c ∈ acc, c.WF) → ∀ {Q : Array Cell × Slice → Prop},
    (∀ cs s', (∀ c ∈ cs, c.WF) → cs.size = acc.size + n → s'.WF → s'.cell = s.cell →
      s'.cell.bits.size = s.cell.bits.size → s'.cell.refs.size = s.cell.refs.size →
      s'.bitPos = s.bitPos → s'.refPos = s.refPos + n → Q (cs, s')) →
    Except.Sat (Slice.takeRefsInv n s acc) Q
  | 0, s, acc, hs, hacc, Q, h => by
    intro r hr
    cases hr
    exact h _ _ hacc rfl hs rfl rfl rfl rfl rfl
  | n + 1, s, acc, hs, hacc, Q, h => by
    simp only [Slice.takeRefsInv]
    refine Except.Sat.of_bind (Slice.takeRefInv_sat hs ?_)
    intro c s' hc hs' h1 _ _ h2 h3
    refine Slice.takeRefsInv_sat n hs' ?_ ?_
    · simp only [Array.forall_mem_push]; exact ⟨hc, hacc⟩
    · intro cs s'' hcs hsz hs'' h1' _ _ h2' h3'
      have hc' := h1'.trans h1
      exact h cs s'' hcs (by simp at hsz; omega) hs'' hc' (by rw [hc']) (by rw [hc'])
        (h2'.trans h2) (by omega)

theorem Slice.WF.refs_le_four {s : Slice} (h : s.WF) : s.cell.refs.size ≤ 4 := h.1.refs_le

theorem Slice.WF.bits_le_max {s : Slice} (h : s.WF) : s.cell.bits.size ≤ 1023 := h.1.bits_le

theorem bitsStripTrailingMarker_size_le (bs : BitString) :
    (bitsStripTrailingMarker bs).size ≤ bs.size := by
  unfold bitsStripTrailingMarker
  simp only [Id.run]
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.zero_le _
    · show (Array.extract bs 0 _).size ≤ _
      simp

end TvmLean

/-! ## The walk over the term -/

namespace TvmLean.ExceptSatTactic

open Lean Meta Elab Tactic

/-- `Except.Sat x P` as its arguments `#[ε, α, x, P]`. -/
def satArgs? (e : Expr) : Option (Array Expr) :=
  if e.isAppOfArity ``TvmLean.Except.Sat 4 then some e.getAppArgs else none

def mkSat (ε α x P : Expr) : Expr :=
  mkAppN (mkConst ``TvmLean.Except.Sat) #[ε, α, x, P]

/-- Replaces the goal by one whose program is in head-beta normal form. -/
def normalize (g : MVarId) : MetaM MVarId := do
  let tgt ← instantiateMVars (← g.getType)
  let tgt := tgt.headBeta
  match satArgs? tgt with
  | some #[ε, α, x, P] =>
    let x' := x.headBeta
    if x' == x && tgt == (← g.getType) then return g
    g.replaceTargetDefEq (mkSat ε α x' P)
  | _ =>
    if tgt == (← g.getType) then return g
    g.replaceTargetDefEq tgt

/-- Applies `e` to the goal, the new goals in order. -/
def applyTo (g : MVarId) (e : Expr) : MetaM (List MVarId) :=
  g.apply e (cfg := { newGoals := .all })

/-- Introduces every binder of the goal. -/
def introAll (g : MVarId) : MetaM MVarId := do
  let (_, g) ← g.intros
  normalize g

/-- Introduces the hypothesis of a branch; an equation of a variable is substituted. -/
def introCond (g : MVarId) : MetaM MVarId := do
  let (h, g) ← g.intro1
  let g ← g.withContext do
    let ty ← instantiateMVars (← h.getType)
    match ty.eq? with
    | some (_, a, b) =>
      if a.isFVar || b.isFVar then
        try subst g h catch _ => pure g
      else pure g
    | none => pure g
  normalize g

/-- The value of a cast whose two sides agree (`Eq.ndrec`, `Eq.rec`, `Eq.mpr`, `cast`), applied to
the remaining arguments. -/
def stripCast? (x : Expr) : MetaM (Option Expr) := do
  let fn := x.getAppFn
  let args := x.getAppArgs
  let some c := fn.constName? | return none
  -- (number of arguments of the cast, position of the value, positions of the two sides)
  let info? : Option (Nat × Nat × Nat × Nat) :=
    if c == ``Eq.ndrec then some (6, 3, 1, 4)
    else if c == ``Eq.rec then some (6, 3, 1, 4)
    else if c == ``Eq.mpr then some (4, 3, 0, 1)
    else if c == ``cast then some (4, 3, 0, 1)
    else none
  let some (n, iv, ia, ib) := info? | return none
  if args.size < n then return none
  unless ← isDefEq args[ia]! args[ib]! do return none
  return some (mkAppN args[iv]! (args.extract n args.size))

/-- Is `e` a `throw` (of `Except`)? Its exception. -/
def throwArg? (e : Expr) : Option Expr :=
  match e.getAppFn.constName? with
  | some c =>
    if c == ``MonadExcept.throw || c == ``MonadExceptOf.throw || c == ``throwThe ||
        c == ``Except.error then
      some e.appArg!
    else none
  | none => none

/-- Replaces `throw e >>= f` by `Except.error e` (the same value): the code after a `throw` is
never run. -/
def dropAfterThrow (e : Expr) : Expr :=
  e.replace fun x =>
    if x.isAppOfArity ``Bind.bind 6 then
      let args := x.getAppArgs
      match throwArg? args[4]! with
      | some err =>
        let m := args[0]!
        if m.isAppOfArity ``Except 1 then
          some (mkAppN (mkConst ``Except.error [0, 0]) #[m.appArg!, args[3]!, err])
        else none
      | none => none
    else none

/-- The number of occurrences of the loose bound variable 0 in `e`. -/
def countLooseBVar0 (e : Expr) : Nat :=
  go e 0
where
  go (e : Expr) (d : Nat) : Nat :=
    if !e.hasLooseBVars then 0 else
    match e with
    | .bvar i => if i == d then 1 else 0
    | .app f a => go f d + go a d
    | .lam _ t b _ => go t d + go b (d + 1)
    | .forallE _ t b _ => go t d + go b (d + 1)
    | .letE _ t v b _ => go t d + go v d + go b (d + 1)
    | .mdata _ b => go b d
    | .proj _ _ b => go b d
    | _ => 0

/-- The `have`, its invariant: for a join point (a function returning `Except`), that every value it
returns satisfies the postcondition; for a value, that it equals its definition. -/
def stepHave (g : MVarId) (ε α P : Expr) (n : Name) (ty v b : Expr) : MetaM (List MVarId) := do
  let isJp ← forallTelescope ty fun _ body => return body.isAppOf ``Except
  -- a join point called once, once the calls after a `throw` are dropped, is inlined: the branch
  -- that calls it keeps its hypotheses (a guard `if !c then throw e` is such a join point)
  if isJp then
    let b' := dropAfterThrow b
    if countLooseBVar0 b' ≤ 1 then
      return [← g.replaceTargetDefEq (mkSat ε α (b'.instantiate1 v).headBeta P)]
  let inv ← withLocalDeclD n ty fun j => do
    if isJp then
      let body ← forallTelescope ty fun ys _ =>
        mkForallFVars ys (mkSat ε α (mkAppN j ys) P)
      mkLambdaFVars #[j] body
    else
      mkLambdaFVars #[j] (← mkEq j v)
  let hvTy := (mkApp inv v).headBeta
  let hbTy ← withLocalDeclD n ty fun x => do
    let t ← mkArrow (mkApp inv x).headBeta (mkSat ε α (b.instantiate1 x) P)
    mkForallFVars #[x] t
  let hv ← mkFreshExprSyntheticOpaqueMVar hvTy
  let hb ← mkFreshExprSyntheticOpaqueMVar hbTy
  let pf := mkAppN (mkConst ``TvmLean.Except.Sat.of_have) #[ε, α, ty, P, v, .lam n ty b .default, inv, hv, hb]
  g.assign pf
  let hvGoals ←
    if isJp then pure [← introAll hv.mvarId!]
    else do hv.mvarId!.refl; pure []
  return hvGoals ++ [← introAll hb.mvarId!]

/-- The specifications of the slice operations of the decoder. -/
def specs : List Name :=
  [``TvmLean.Slice.takeBitsAsNat_sat, ``TvmLean.Slice.peekBitsAsNat_sat,
   ``TvmLean.Slice.takeRefInv_sat, ``TvmLean.Slice.takeRefsInv_sat]

/-- Closes a side condition of a specification by assumption, else leaves it. -/
def trySideGoal (g : MVarId) : MetaM (List MVarId) := do
  if (← g.isAssigned) then return []
  let ty ← instantiateMVars (← g.getType)
  if (satArgs? ty.getForallBody).isSome || ty.isForall && (← isProp ty) &&
      ((← forallTelescope ty fun _ b => return (satArgs? b).isSome)) then
    return [← introAll g]
  if ← g.assumptionCore then return []
  return [g]

/-- One step of the walk on the goal `Except.Sat x P`; `none` if the goal is not of that form or its
program is not one the walk knows (a leaf). -/
def step (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  let g ← normalize g
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some #[ε, α, x, P] := satArgs? tgt | return none
  match x with
  | .letE n ty v b _ => return some (← stepHave g ε α P n ty v b)
  | .mdata _ e => return some [← g.replaceTargetDefEq (mkSat ε α e P)]
  | _ =>
  let fn := x.getAppFn
  if let .fvar j := fn then
    -- a jump to a join point: its hypothesis
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ok ← forallTelescope d.type fun _ body => do
        match satArgs? body with
        | some args => return args[2]!.getAppFn == .fvar j
        | none => return false
      if ok then
        if let some gs ← observing? (applyTo g (mkFVar d.fvarId)) then return some gs
        -- the join point (a local function) is called with another postcondition
        let hjApp := mkAppN (mkFVar d.fvarId) x.getAppArgs
        let some #[_, _, _, P'] := satArgs? (← instantiateMVars (← inferType hjApp)) | return none
        let hqTy ← withLocalDeclD `a α fun a => do
          mkForallFVars #[a] (← mkArrow (mkApp P' a).headBeta (mkApp P a).headBeta)
        let hq ← mkFreshExprSyntheticOpaqueMVar hqTy
        g.assign (mkAppN (mkConst ``TvmLean.Except.Sat.mono) #[ε, α, P', P, x, hjApp, hq])
        return some [← introAll hq.mvarId!]
    return none
  let some c := fn.constName? | return none
  if c == ``ite then
    return some ((← (← applyTo g (mkConst ``TvmLean.Except.Sat.of_ite)).mapM introCond))
  if c == ``dite then
    return some ((← (← applyTo g (mkConst ``TvmLean.Except.Sat.of_dite)).mapM introCond))
  -- casts of the branches of a match on literals, once the discriminant is substituted
  if c == ``Eq.ndrec || c == ``Eq.rec || c == ``Eq.mpr || c == ``cast then
    if let some x' ← stripCast? x then
      return some [← g.replaceTargetDefEq (mkSat ε α x'.headBeta P)]
    return none
  if c == ``Bind.bind then
    return some (← applyTo g (mkConst ``TvmLean.Except.Sat.of_bind))
  if c == ``Pure.pure then
    let gs ← applyTo g (mkConst ``TvmLean.Except.Sat.of_pure)
    return some (← gs.mapM normalize)
  if c == ``MonadExcept.throw || c == ``MonadExceptOf.throw || c == ``throwThe then
    return some (← applyTo g (mkConst ``TvmLean.Except.Sat.of_throw))
  if c == ``Except.error then
    return some (← applyTo g (mkConst ``TvmLean.Except.Sat.of_error))
  if (← isMatcher c) then
    let some app ← matchMatcherApp? x | return none
    -- a match on constructors reduces; any other is split (`whnf` of a discriminant computed by
    -- the decoder could evaluate it)
    let env ← getEnv
    let isCtor (d : Expr) : Bool :=
      match d.getAppFn with
      | .const n _ => (env.find? n).any fun i => i.isCtor
      | .lit _ => true
      | _ => false
    if app.discrs.all isCtor then
      match ← reduceMatcher? x with
      | .reduced x' => return some [← g.replaceTargetDefEq (mkSat ε α x'.headBeta P)]
      | _ => return some (← Split.splitMatch g x)
    let mut onNat := true
    for d in app.discrs do
      unless (← whnfR (← inferType d)).isConstOf ``Nat do onNat := false
    unless onNat do
      return some (← Split.splitMatch g x)
    -- a match on natural number literals is a chain of `dite`s on its discriminants (made
    -- variables first, so that a branch can substitute them); its splitter is not built
    let compound := app.discrs.filter fun d => !d.isFVar
    let (_, g) ← g.generalize (compound.map fun d => { expr := d })
    let g' ← g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let some #[ε, α, x, P] := satArgs? tgt | return none
      let x' ← deltaExpand x (· == c)
      return some (← g.replaceTargetDefEq (mkSat ε α x'.headBeta P))
    return g'.map ([·])
  for s in specs do
    if let some gs ← observing? (applyTo g (mkConst s)) then
      return some (← gs.flatMapM trySideGoal)
  return none

/-- Runs `step` on the goals until none applies, at most `fuel` steps; returns the leaves. -/
def loop : Nat → List MVarId → Array MVarId → MetaM (Array MVarId)
  | 0, gs, leaves => return leaves ++ gs.toArray
  | _ + 1, [], leaves => return leaves
  | fuel + 1, g :: gs, leaves => do
    if ← g.isAssigned then loop fuel gs leaves else
    let g ← g.withContext (normalize g)
    let r ← step g
    match r with
    | some new => loop fuel (new ++ gs) leaves
    | none => loop fuel gs (leaves.push g)

/-- Walks the program of a goal `Except.Sat x P` (see the module docstring), leaving the goals of
the `return`s and the side conditions of the slice operations that are not hypotheses. -/
elab "except_sat" : tactic => do
  let g ← getMainGoal
  let leaves ← loop 10000000 [g] #[]
  replaceMainGoal leaves.toList

/-- Adds the bounds of every well-formed slice in context (`Slice.WF` is a conjunction `omega` does
not see into). -/
elab "slice_facts" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut g := g
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``TvmLean.Slice.WF 1 then
        for lem in [``TvmLean.Slice.WF.refs_le_four, ``TvmLean.Slice.WF.bits_le_max,
            ``TvmLean.Slice.WF.bitPos_le, ``TvmLean.Slice.WF.refPos_le] do
          let pf ← mkAppM lem #[mkFVar d.fvarId]
          let (_, g') ← (← g.assert `h (← inferType pf) pf).intro1P
          g := g'
    replaceMainGoal [g]

/-- Clears the hypotheses about join points (`Except.Sat`), which a `return` does not need. -/
elab "clear_sat_hyps" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut fvars := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type).find? (·.isConstOf ``TvmLean.Except.Sat) |>.isSome then
        fvars := fvars.push d.fvarId
    replaceMainGoal [← g.tryClearMany fvars]

end TvmLean.ExceptSatTactic

namespace TvmLean


/-- An instruction one of a list of decoders finds (`findSome?`) is well-formed when each of them
gives well-formed instructions. -/
theorem Instr.WF_of_findSome? {l : List (Option Instr)} (h : ∀ o ∈ l, ∀ i, o = some i → i.WF)
    {i : Instr} (hi : l.findSome? (fun x => x) = some i) : i.WF := by
  obtain ⟨o, ho, hoi⟩ := List.exists_of_findSome?_eq_some hi
  exact h o ho i hoi

/-- Closes a `return` of the decoder: substitutes the values of its `let`s, splits the claim, and
proves the bounds of the cells and slices it builds from the facts of the slice operations. -/
macro "decode_leaf" : tactic => `(tactic| (
  clear_sat_hyps
  try dsimp only
  try subst_vars
  try simp only [Instr.WF, Slice.ofCell_WF_iff, true_and, and_true, Bool.not_eq_true',
    Bool.not_eq_false, Slice.haveBits_iff, Slice.haveRefs_iff, Array.size_push,
    Array.size_empty] at *
  repeat' (first
    | assumption
    | (apply Slice.advanceBits_WF (by assumption))
    | (apply Cell.mkOrdinary_WF)
    | (exact Slice.WF.cell_wf (by assumption))
    | (exact Slice.WF.refPos_le (by assumption))
    | (intro c hc; simp at hc)
    | (exact Nat.le_trans (bitsStripTrailingMarker_size_le _) (Slice.readBits_size_le (by assumption) _))
    | (exact Slice.readBits_size_le (by assumption) _)
    | (simp; done)
    | (apply And.intro))
  all_goals (try simp only [Slice.readBits, Slice.advanceBits, Array.size_extract] at *)
  all_goals (first
    | (slice_facts; omega)
    | (apply Instr.WF_of_findSome? _ (Eq.symm (by assumption))
       simp only [List.forall_mem_cons]
       repeat' apply And.intro
       all_goals first
         | (intro o ho; cases ho)
         | (intro i hi; split at hi <;> cases hi <;> trivial)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Every instruction decoded from a well-formed code slice, and the rest of the code, are
well-formed. -/
theorem decodeCp0WithBits_sat {s : Slice} (hs : s.WF) :
    Except.Sat (decodeCp0WithBits s) (fun r => r.1.WF ∧ r.2.2.WF) := by
  delta decodeCp0WithBits
  except_sat
  all_goals try dsimp only
  all_goals first
    | exact ⟨trivial, ‹_›⟩
    | decode_leaf

theorem decodeCp0WithBits_WF {s : Slice} (hs : s.WF) {i : Instr} {n : Nat} {rest : Slice}
    (h : decodeCp0WithBits s = .ok (i, n, rest)) : i.WF ∧ rest.WF :=
  decodeCp0WithBits_sat hs _ h

end TvmLean

import TvmLean.Proofs.Exec.FramedDictOptRef
import TvmLean.Proofs.Exec.Spec.CellExt

/-!
# `GETEXTRABALANCE` on any balance, framed

`GETEXTRABALANCE` (C++ `exec_get_extra_currency_balance`, tonops.cpp:388) looks a currency up in
the dictionary of the balance (`c7[0][7][1]`); its first calls charge the cells the lookup loads
cheaply (`VM.registerCellLoadCheap`), counting the calls (`getExtraBalanceCounter`) and the gas
beyond their cap (`freeGasConsumed`). On a balance a run does not know, the instruction is framed
with the frame that lets those counters change (`Framed.ExecFramedC true`,
TvmLean/Proofs/Exec/Framed.lean): it changes the stack, the gas, the loaded cells and libraries and
the two counters only; it pushes an integer; it fails only with an exception of code 2 or more.

* `StepsX`: `Steps` (TvmLean/Proofs/Exec/FramedDict.lean) with the frame `FrameX`; `Steps.x` lifts
  a framed computation that leaves the counters; the combinators `StepsX.keep_bind`, ...;
  `AtX`: the same at one state (a program that reads the state and sets it);
* the local functions of a `do` block (its join points `__do_jp`, a helper such as the handler's
  `chargeLoads`) followed once, not once per use (tactics `stepsx_let`, `stepsx_hyp`, also for
  `Steps`), and the tactic `stepsx_auto` that follows a handler with these;
* `StepsX.registerCellLoadCheap`: a cheap load is framed;
* `DictTail.extraBalance`: the handler (TvmLean/Semantics/Exec/TonEnv/GetExtraBalance.lean) on its
  instruction, the run of `GETEXTRABALANCE` (`DictTail.extraBalanceHandler_eq`);
* `Framed.extraBalance_framed`, `Framed.runWith_extraBalance`, tactic `vm_extra_balance_any`.
-/


namespace TvmLean.Framed

open TvmLean

/-! ## Framed computations that may change the counters -/

theorem FrameX.refl (st : VmState) : FrameX st st := rfl

theorem FrameX.trans {a b c : VmState} (h1 : FrameX a b) (h2 : FrameX b c) : FrameX a c := by
  unfold FrameX at *
  conv => lhs; rw [h2, h1]

theorem FrameX.maxLibraryLoads {a b : VmState} (h : FrameX a b) : b.maxLibraryLoads = a.maxLibraryLoads := by
  rw [h]

/-- `Steps` with the frame `FrameX`: the counters of the cheap `GETEXTRABALANCE` calls may change. -/
def StepsX {α : Type} (m : VM α) (P : α → Stack → Stack → Prop) : Prop :=
  ∀ st : VmState, FrameX st (ExceptT.run m st).2 ∧
    (∀ a, (ExceptT.run m st).1 = .ok a → P a st.stack (ExceptT.run m st).2.stack) ∧
    (∀ e, (ExceptT.run m st).1 = .error e → 2 ≤ e.toInt) ∧
    (st.maxLibraryLoads = none → (ExceptT.run m st).2.librariesMissed = st.librariesMissed)

theorem Steps.x {α : Type} {m : VM α} {P : α → Stack → Stack → Prop} (h : Steps m P) : StepsX m P := by
  intro st
  obtain ⟨h1, h2, h3, h4⟩ := h st
  exact ⟨h1.x, h2, h3, h4⟩

theorem StepsX.mono {α : Type} {m : VM α} {P Q : α → Stack → Stack → Prop} (h : StepsX m P)
    (hPQ : ∀ a s s', P a s s' → Q a s s') : StepsX m Q := by
  intro st
  obtain ⟨h1, h2, h3, h4⟩ := h st
  exact ⟨h1, fun a ha => hPQ _ _ _ (h2 a ha), h3, h4⟩

theorem StepsX.bind {α β : Type} {m : VM α} {f : α → VM β} {P : α → Stack → Stack → Prop}
    {Q : α → β → Stack → Stack → Prop} (hm : StepsX m P) (hf : ∀ a, StepsX (f a) (Q a)) :
    StepsX (m >>= f) (fun b s s'' => ∃ a s', P a s s' ∧ Q a b s' s'') := by
  intro st
  obtain ⟨h1, h2, h3, h4⟩ := hm st
  rw [VM.run_bind]
  generalize hX : ExceptT.run m st = X at h1 h2 h3 h4
  obtain ⟨r, st1⟩ := X
  simp only at h1 h2 h3 h4
  cases r with
  | error e =>
    rw [VM.bindRes_error]
    refine ⟨h1, ?_, ?_, h4⟩
    · intro b h; cases h
    · intro e' h; cases h; exact h3 e rfl
  | ok a =>
    rw [VM.bindRes_ok]
    obtain ⟨g1, g2, g3, g4⟩ := hf a st1
    refine ⟨h1.trans g1, fun b hb => ⟨a, st1.stack, h2 a rfl, g2 b hb⟩, g3, fun hn => ?_⟩
    rw [g4 (by rw [h1.maxLibraryLoads]; exact hn), h4 hn]

theorem StepsX.keep_bind {α β : Type} {m : VM α} {f : α → VM β} {R : Stack → Stack → Prop}
    (hm : StepsX m (fun _ s s' => s' = s)) (hf : ∀ a, StepsX (f a) (fun _ s s' => R s s')) :
    StepsX (m >>= f) (fun _ s s' => R s s') :=
  StepsX.mono (StepsX.bind hm hf) (by
    rintro _ s s'' ⟨_, s1, h1, h2⟩
    rw [h1] at h2
    exact h2)

theorem StepsX.pop_bind {α β : Type} {m : VM α} {f : α → VM β} {R : Stack → Stack → Prop}
    (hm : StepsX m (fun _ s s' => ∃ v, s = s'.push v))
    (hf : ∀ a, StepsX (f a) (fun _ s1 s' => ∀ v, R (s1.push v) s')) :
    StepsX (m >>= f) (fun _ s s' => R s s') :=
  StepsX.mono (StepsX.bind hm hf) (by
    rintro _ s s'' ⟨_, s1, ⟨v, h1⟩, h2⟩
    rw [h1]
    exact h2 v)

theorem StepsX.push_end {v : Value} {R : Stack → Stack → Prop} (h : ∀ s, R s (s.push v)) :
    StepsX (VM.push v) (fun _ s s' => R s s') :=
  StepsX.mono (Steps.push v).x (fun _ s s' h' => by rw [h']; exact h s)

theorem StepsX.pushIntQuiet_end {x : Int} {R : Stack → Stack → Prop} (h : ∀ s, R s (s.push (.int (.num x)))) :
    StepsX (VM.pushIntQuiet (.num x) false) (fun _ s s' => R s s') :=
  StepsX.mono (Steps.pushIntQuiet_num x).x (fun _ s s' h' => by rw [h']; exact h s)

theorem StepsX.pure_end {α : Type} {a : α} {R : Stack → Stack → Prop} (h : ∀ s, R s s) :
    StepsX (Pure.pure a : VM α) (fun _ s s' => R s s') :=
  StepsX.mono (Steps.pure a).x (fun _ s s' h' => by rw [h'.2]; exact h s)

theorem StepsX.keep_end {α : Type} {m : VM α} {R : Stack → Stack → Prop}
    (hm : StepsX m (fun _ s s' => s' = s)) (h : ∀ s, R s s) : StepsX m (fun _ s s' => R s s') :=
  StepsX.mono hm (fun _ s s' h' => by rw [h']; exact h s)

theorem StepsX.throw_R {α : Type} {e : Excno} (he : 2 ≤ e.toInt) {R : Stack → Stack → Prop} :
    StepsX (MonadExcept.throw e : VM α) (fun _ s s' => R s s') :=
  (Steps.throw e he _).x

theorem StepsX.throw_bind {α β : Type} {e : Excno} (he : 2 ≤ e.toInt) {f : α → VM β}
    {R : Stack → Stack → Prop} : StepsX ((MonadExcept.throw e : VM α) >>= f) (fun _ s s' => R s s') :=
  (Steps.throw_bind he).x

theorem StepsX.ite_R {α : Type} {c : Prop} [Decidable c] {x y : VM α} {R : Stack → Stack → Prop}
    (hx : c → StepsX x (fun _ s s' => R s s')) (hy : ¬c → StepsX y (fun _ s s' => R s s')) :
    StepsX (if c then x else y) (fun _ s s' => R s s') := by
  by_cases h : c
  · rw [if_pos h]; exact hx h
  · rw [if_neg h]; exact hy h

theorem StepsX.ite_bind {α β : Type} {c : Prop} [Decidable c] {x y : VM α} {f : α → VM β}
    {R : Stack → Stack → Prop} (hx : c → StepsX (x >>= f) (fun _ s s' => R s s'))
    (hy : ¬c → StepsX (y >>= f) (fun _ s s' => R s s')) :
    StepsX ((if c then x else y) >>= f) (fun _ s s' => R s s') := by
  by_cases h : c
  · rw [if_pos h]; exact hx h
  · rw [if_neg h]; exact hy h

/-! ## The parts of the handler -/

theorem Steps.pop : Steps VM.pop (fun _ s s' => ∃ v, s = s'.push v) := by
  intro st
  rw [VM.run_pop]
  split
  · rename_i h
    refine ⟨rfl, fun _ _ => ⟨_, stack_eq_pop_push_back st.stack h⟩, ?_, fun _ => rfl⟩
    intro e he; cases he
  · steps_leaf

/-- A parameter of `c7` pushed, then popped: the stack as it was. -/
theorem Steps.c7Pop (idx : Nat) :
    Steps (VM.pushC7Param idx >>= fun _ => VM.pop) (fun _ s s' => s' = s) :=
  Steps.mono (Steps.bind (Steps.pushC7Param idx) (fun _ => Steps.pop)) (by
    rintro _ s s'' ⟨_, s1, ⟨v, h1⟩, ⟨w, h2⟩⟩
    rw [h1] at h2
    exact (Array.push_eq_push.mp h2).2.symm)

theorem StepsX.c7Pop_bind {β : Type} {idx : Nat} {f : Value → VM β} {R : Stack → Stack → Prop}
    (hf : ∀ a, StepsX (f a) (fun _ s s' => R s s')) :
    StepsX (VM.pushC7Param idx >>= fun _ => VM.pop >>= f) (fun _ s s' => R s s') := by
  have e : (VM.pushC7Param idx >>= fun _ => VM.pop >>= f) = ((VM.pushC7Param idx >>= fun _ => VM.pop) >>= f) := by
    rw [bind_assoc]
  rw [e]
  exact StepsX.keep_bind (Steps.c7Pop idx).x hf

/-- The read of an unsigned length (`Slice.takeBitsAsNatCellUnd`) in the VM: the stack as it was,
or cell_und. -/
theorem Steps.liftTakeBits (sl : Slice) (n : Nat) :
    Steps (liftM (sl.takeBitsAsNatCellUnd n) : VM (Nat × Slice)) (fun _ s s' => s' = s) := by
  intro st
  rw [Spec.run_takeBitsAsNatCellUnd]
  split
  · refine ⟨rfl, fun _ _ => rfl, ?_, fun _ => rfl⟩
    intro e he; cases he
  · steps_leaf

theorem StepsX.modifyCounter :
    StepsX (modify fun st => { st with getExtraBalanceCounter := st.getExtraBalanceCounter + 1 } : VM Unit)
      (fun _ s s' => s' = s) := by
  intro st
  rw [VM.run_modify]
  refine ⟨rfl, fun _ _ => rfl, ?_, fun _ => rfl⟩
  intro e he; cases he

/-- A loop whose every step leaves the stack (`forIn` over an array): the stack as it was. -/
theorem StepsX.forIn_keep {α β : Type} (xs : Array α) (b0 : β) (f : α → β → VM (ForInStep β))
    (hf : ∀ x b, StepsX (f x b) (fun _ s s' => s' = s)) :
    StepsX (forIn xs b0 f) (fun _ s s' => s' = s) := by
  rw [← Array.forIn_toList]
  generalize xs.toList = l
  induction l generalizing b0 with
  | nil =>
    simp only [List.forIn_nil]
    exact (Steps.mono (Steps.pure _) (fun _ _ _ h => h.2)).x
  | cons x l ih =>
    simp only [List.forIn_cons]
    refine StepsX.keep_bind (hf x b0) (fun r => ?_)
    cases r with
    | done b => exact (Steps.mono (Steps.pure _) (fun _ _ _ h => h.2)).x
    | yield b => exact ih b


theorem StepsX.registerLibraryLoad (hash : BitString) :
    StepsX (modify fun st => st.registerLibraryLoad hash : VM PUnit) (fun _ s s' => s' = s) := by
  intro st
  rw [VM.run_modify]
  refine ⟨(Frame.of_load (LoadFrame.registerLibraryLoad st _)).x, fun _ _ => (LoadFrame.registerLibraryLoad st _).stack,
    ?_, fun hn => registerLibraryLoad_none st _ hn⟩
  intro e he; cases he

theorem StepsX.modifyFreeGas (k : Int) :
    StepsX (modify fun st => { st with freeGasConsumed := st.freeGasConsumed + k } : VM Unit)
      (fun _ s s' => s' = s) := by
  intro st
  rw [VM.run_modify]
  refine ⟨rfl, fun _ _ => rfl, ?_, fun _ => rfl⟩
  intro e he; cases he

/-- `StepsX` at the one state `st0`: what a program depending on the state needs. -/
def AtX {α : Type} (st0 : VmState) (m : VM α) (P : α → Stack → Stack → Prop) : Prop :=
  FrameX st0 (ExceptT.run m st0).2 ∧
    (∀ a, (ExceptT.run m st0).1 = .ok a → P a st0.stack (ExceptT.run m st0).2.stack) ∧
    (∀ e, (ExceptT.run m st0).1 = .error e → 2 ≤ e.toInt) ∧
    (st0.maxLibraryLoads = none → (ExceptT.run m st0).2.librariesMissed = st0.librariesMissed)

/-- A read of the state, then a program framed at the state read. -/
theorem StepsX.get_bind_at {β : Type} {f : VmState → VM β} {R : β → Stack → Stack → Prop}
    (h : ∀ st, AtX st (f st) R) : StepsX (get >>= f) R := by
  intro st
  have := h st
  unfold AtX at this
  rw [VM.run_bind, VM.run_get, VM.bindRes_ok]
  exact this

theorem AtX.keep_bind {α β : Type} {st0 : VmState} {m : VM α} {f : α → VM β} {R : Stack → Stack → Prop}
    (hm : AtX st0 m (fun _ s s' => s' = s))
    (hf : ∀ a st1, ExceptT.run m st0 = (.ok a, st1) → AtX st1 (f a) (fun _ s s' => R s s')) :
    AtX st0 (m >>= f) (fun _ s s' => R s s') := by
  obtain ⟨h1, h2, h3, h4⟩ := hm
  unfold AtX
  rw [VM.run_bind]
  generalize hX : ExceptT.run m st0 = X at h1 h2 h3 h4 hf
  obtain ⟨r, st1⟩ := X
  simp only at h1 h2 h3 h4
  cases r with
  | error e =>
    rw [VM.bindRes_error]
    refine ⟨h1, ?_, ?_, h4⟩
    · intro b h; cases h
    · intro e' h; cases h; exact h3 e rfl
  | ok a =>
    rw [VM.bindRes_ok]
    obtain ⟨g1, g2, g3, g4⟩ := hf a st1 rfl
    refine ⟨h1.trans g1, fun b hb => ?_, g3, fun hn => ?_⟩
    · have := g2 b hb
      rw [h2 a rfl] at this
      exact this
    · rw [g4 (by rw [h1.maxLibraryLoads]; exact hn), h4 hn]

theorem AtX.ite {α : Type} {st0 : VmState} {c : Prop} [Decidable c] {x y : VM α} {R : α → Stack → Stack → Prop}
    (hx : c → AtX st0 x R) (hy : ¬c → AtX st0 y R) : AtX st0 (if c then x else y) R := by
  by_cases h : c
  · rw [if_pos h]; exact hx h
  · rw [if_neg h]; exact hy h

/-- A state set that changes the loaded cells only (the first load of a cell). -/
theorem AtX.setLoaded (st0 : VmState) (lc : Array (Array UInt8)) :
    AtX st0 (set { st0 with loadedCells := lc } : VM PUnit) (fun _ s s' => s' = s) := by
  unfold AtX
  rw [VM.run_set]
  refine ⟨rfl, fun _ _ => rfl, ?_, fun _ => rfl⟩
  intro e he; cases he

open Lean Meta Elab Tactic in
/-- `stepsx_let`: the program of the goal (`StepsX m P`, `Steps m P`, `AtX st m P`) is a `let`. A
value that is not a function is put in place. A function of any number of arguments (a join point
`__do_jp` of `do`, or a local helper such as the handler's `chargeLoads`) is followed once instead of
once per call: two goals, `∀ ys, StepsX (J ys) Q` for its value `J` (the arguments introduced), and
the goal with a variable `jp` in its place and the hypothesis `hjp : ∀ ys, StepsX (jp ys) Q`
(`Steps` for a goal `Steps`); `Q` is the relation of the goal for a join point (a call of it ends
the program) and the stack unchanged for a helper. The proof is the second goal applied to `J` and
to the first (`(fun jp hjp => _) J hJ`; the `let` is its `zeta`). -/
elab "stepsx_let" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let (pred, idx) ←
    if t.isAppOfArity ``StepsX 3 then pure (``StepsX, 1)
    else if t.isAppOfArity ``AtX 4 then pure (``StepsX, 2)
    else if t.isAppOfArity ``Steps 3 then pure (``Steps, 1)
    else throwError "stepsx_let: the goal is not `StepsX`, `Steps` or `AtX`"
  let args := t.getAppArgs
  let .letE n ty v b _ := args[idx]! | throwError "stepsx_let: the program is not a `let`"
  unless (← whnfR ty).isForall do
    replaceMainGoal [← g.replaceTargetDefEq (mkAppN t.getAppFn (args.set! idx (b.instantiate1 v)))]
    return
  let P := args.back!
  let stackT := mkConst ``TvmLean.Stack
  let isJp := n.eraseMacroScopes.toString.startsWith "__do_jp"
  let (hJty, hBty, k) ← forallTelescope ty fun ys body => do
    unless body.isApp do throwError "stepsx_let: not a function to a program"
    let δ := body.appArg!
    if δ.hasAnyFVar (fun f => ys.any (·.fvarId! == f)) then throwError "stepsx_let: a dependent function"
    let Q ← if isJp then
        unless ← isDefEq δ args[0]! do throwError "stepsx_let: a join point of another type"
        pure P
      else
        withLocalDeclD `x δ fun x => withLocalDeclD `s stackT fun s => withLocalDeclD `s' stackT fun s' => do
          mkLambdaFVars #[x, s, s'] (← mkEq s' s)
    let pr (m : Expr) : Expr := mkApp3 (mkConst pred) δ m Q
    let hJty ← mkForallFVars ys (pr (mkAppN v ys).headBeta)
    let hBty ← withLocalDeclD `jp ty fun jp => do
      let hjpTy ← mkForallFVars ys (pr (mkAppN jp ys))
      withLocalDeclD `hjp hjpTy fun hjp => do
        mkForallFVars #[jp, hjp] (mkAppN t.getAppFn (args.set! idx (b.instantiate1 jp)))
    return (hJty, hBty, ys.size)
  let gJ ← mkFreshExprSyntheticOpaqueMVar hJty
  let gB ← mkFreshExprSyntheticOpaqueMVar hBty
  g.assign (mkApp2 gB v gJ)
  let (_, gJ') ← gJ.mvarId!.introN k
  let (_, gB') ← gB.mvarId!.introN 2 [`jp, `hjp]
  replaceMainGoal [gJ', gB']

open Lean Meta Elab Tactic in
/-- `stepsx_hyp`: the program of the goal (`StepsX (jp as) P`, `Steps (jp as) P`) is a call of a
local function, framed by a hypothesis (`∀ ys, StepsX (jp ys) P`, of `stepsx_let`). -/
elab "stepsx_hyp" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``StepsX 3 || t.isAppOfArity ``Steps 3 do
    throwError "stepsx_hyp: the goal is not `StepsX` or `Steps`"
  let f := (t.getArg! 1).getAppFn
  unless f.isFVar do throwError "stepsx_hyp: the program is not a call of a variable"
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let fits ← forallTelescope d.type fun _ b =>
      pure ((b.isAppOfArity ``StepsX 3 || b.isAppOfArity ``Steps 3) && (b.getArg! 1).getAppFn == f)
    if fits then
      if let some gs ← observing? (g.apply d.toExpr) then
        replaceMainGoal gs
        return
  throwError "stepsx_hyp: no hypothesis frames the call"

/-! ## `GETEXTRABALANCE` -/

/-- What `GETEXTRABALANCE` leaves on the stack `s` under the currency: the balance (any integer). -/
abbrev ExtraOk (s s' : Stack) : Prop := ∃ x : Int, s' = s.push (.int (.num x))

/-- `ExtraOk` of the stack under the currency. -/
abbrev ExtraOk1 (s s' : Stack) : Prop := ∃ (s0 : Stack) (a : Value), s = s0.push a ∧ ExtraOk s0 s'

/-- An obligation of `stepsx_step` (the stack unchanged, `ExtraOk1`): the stacks named by the
combinators substituted, then the case it is. -/
macro "stepsx_close" : tactic => `(tactic| (intros; subst_vars; first
  | rfl
  | exact ⟨_, _, rfl, ⟨_, rfl⟩⟩))

/-- Follows a VM program with the combinators of `StepsX` of a fixed relation (`stepsx_step` until
none applies). -/
syntax "stepsx_auto" : tactic

open Lean Meta Elab Tactic in
/-- The tactic that proves `StepsX a (fun _ s s' => s' = s)` for a step `a` that leaves the stack (a
load, gas, a read of the state, a counter, a loop of such steps, a call of a local function), chosen
by the head of `a`; `none` for any other step. -/
def keepLeafTac? (a : Expr) : MetaM (Option (TSyntax `tactic)) := do
  if a.getAppFn.isFVar then return some (← `(tactic| stepsx_hyp))
  let some c := a.getAppFn.constName? | return none
  if c == ``modify then
    return some (← `(tactic| first
      | exact StepsX.modifyCounter | exact StepsX.modifyFreeGas _ | exact StepsX.registerLibraryLoad _))
  if c == ``ForIn.forIn then return some (← `(tactic| exact StepsX.forIn_keep _ _ _ (fun _ _ => by stepsx_auto)))
  -- proved below with this tactic: named at run time
  if c == ``VM.registerCellLoadCheap then
    return some (← `(tactic| exact $(mkIdent `TvmLean.Framed.StepsX.registerCellLoadCheap) _ _))
  if c == ``liftM then return some (← `(tactic| exact Steps.x (Steps.liftTakeBits _ _)))
  if c == ``VM.consumeGas then return some (← `(tactic| exact Steps.x (Steps.consumeGas _)))
  if c == ``MonadState.get || c == ``MonadStateOf.get || c == ``getThe then
    return some (← `(tactic| exact Steps.x Steps.get))
  if c == ``VM.registerCellLoad then return some (← `(tactic| exact Steps.x (Steps.registerCellLoad _)))
  if c == ``VM.checkUnderflow then return some (← `(tactic| exact Steps.x (Steps.checkUnderflow _)))
  return none

open Lean Meta Elab Tactic in
/-- The tactic that proves `StepsX a (fun _ s s' => ∃ v, s = s'.push v)` for a pop `a` of one value,
chosen by the head of `a`; `none` for any other step. -/
def popLeafTac? (a : Expr) : MetaM (Option (TSyntax `tactic)) := do
  let some c := a.getAppFn.constName? | return none
  if c == ``VM.pop then return some (← `(tactic| exact Steps.x Steps.pop))
  if c == ``VM.popNatUpTo then return some (← `(tactic| exact Steps.x (Steps.popNatUpTo _)))
  if c == ``VM.popInt then return some (← `(tactic| exact Steps.x Steps.popInt'))
  if c == ``VM.popSlice then return some (← `(tactic| exact Steps.x Steps.popSlice))
  if c == ``VM.popCell then return some (← `(tactic| exact Steps.x Steps.popCell))
  if c == ``VM.popBuilder then return some (← `(tactic| exact Steps.x Steps.popBuilder))
  if c == ``VM.popMaybeCell then return some (← `(tactic| exact Steps.x Steps.popMaybeCell))
  return none

open Lean Meta Elab Tactic in
/-- Whether `e` is a `throw` of the VM. -/
def isThrow (e : Expr) : Bool :=
  e.isAppOf ``MonadExcept.throw || e.isAppOf ``MonadExceptOf.throw || e.isAppOf ``throwThe

open Lean Meta Elab Tactic in
/-- `stepsx_step`: one step on the main goal `StepsX m P`, chosen by the head of the program `m`
(no unification is tried on a head that does not fit): a `let` (`stepsx_let`); a call of a local
function (`stepsx_hyp`); a bind of a step that leaves the stack, of a pop, of a parameter of `c7`
pushed and popped, of an `if`, of a `throw` (its code by `steps_err`), of a `pure` or of a bind; a
push, a `pure`, a `throw`, an `if` or a step that leaves the stack at the end; a `match` (`split`).
A goal that is not `StepsX` (an obligation on the stacks) is closed by `stepsx_close`. Fails if
nothing applies. -/
elab "stepsx_step" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``StepsX 3 do
    evalTactic (← `(tactic| stepsx_close))
    return
  let m := t.getArg! 1
  let run (tacs : Array (TSyntax `tactic)) : TacticM Unit := do
    for tac in tacs do evalTactic tac
  if m.isLet then
    run #[← `(tactic| stepsx_let)]
    return
  if m.getAppFn.isFVar then
    run #[← `(tactic| stepsx_hyp)]
    return
  if m.isAppOfArity ``Bind.bind 6 then
    let a := m.getArg! 4
    if let some leaf ← keepLeafTac? a then
      run #[← `(tactic| refine StepsX.keep_bind ?_ (fun _ => ?_)), leaf]
      return
    if let some leaf ← popLeafTac? a then
      run #[← `(tactic| refine StepsX.pop_bind ?_ (fun _ => ?_)), leaf]
      return
    if a.isAppOf ``VM.pushC7Param then
      run #[← `(tactic| refine StepsX.c7Pop_bind (fun _ => ?_))]
      return
    if a.isAppOfArity ``ite 5 then
      run #[← `(tactic| refine StepsX.ite_bind (fun _ => ?_) (fun _ => ?_))]
      return
    if isThrow a then
      run #[← `(tactic| refine StepsX.throw_bind ?_), ← `(tactic| steps_err)]
      return
    if a.isAppOf ``Pure.pure then
      run #[← `(tactic| simp (config := { zeta := false }) only [pure_bind])]
      return
    if a.isAppOfArity ``Bind.bind 6 then
      run #[← `(tactic| simp (config := { zeta := false }) only [bind_assoc])]
      return
    throwError "stepsx_step: a bind of {a.getAppFn}"
  if m.isAppOf ``VM.push then
    run #[← `(tactic| refine StepsX.push_end ?_)]
    return
  if m.isAppOf ``VM.pushIntQuiet then
    run #[← `(tactic| refine StepsX.pushIntQuiet_end ?_)]
    return
  if m.isAppOf ``Pure.pure then
    run #[← `(tactic| refine StepsX.pure_end ?_)]
    return
  if isThrow m then
    run #[← `(tactic| refine StepsX.throw_R ?_), ← `(tactic| steps_err)]
    return
  if m.isAppOfArity ``ite 5 then
    run #[← `(tactic| refine StepsX.ite_R (fun _ => ?_) (fun _ => ?_))]
    return
  if let some leaf ← keepLeafTac? m then
    run #[← `(tactic| refine StepsX.keep_end ?_ ?_), leaf]
    return
  if ← Meta.isMatcherApp m then
    run #[← `(tactic| split)]
    return
  throwError "stepsx_step: the program {m.getAppFn}"

macro_rules
  | `(tactic| stepsx_auto) => `(tactic| repeat' stepsx_step)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **A cheap load is framed** (`VM.registerCellLoadCheap`: the gas, the loaded cells and libraries,
`freeGasConsumed`). -/
theorem StepsX.registerCellLoadCheap (c : Cell) (remaining : Int) :
    StepsX (VM.registerCellLoadCheap c remaining) (fun _ s s' => s' = s) := by
  unfold VM.registerCellLoadCheap
  refine StepsX.get_bind_at (fun st => ?_)
  stepsx_let; stepsx_let; stepsx_let
  · stepsx_auto
  · refine AtX.ite (fun _ => ?_) (fun _ => ?_)
    · exact AtX.keep_bind (AtX.setLoaded _ _) (fun _ st1 _ => hjp _ st1)
    · rw [pure_bind]
      exact hjp _ st

end TvmLean.Framed

/-! ## The handler -/

namespace DictTail

open TvmLean

/-- The handler of `GETEXTRABALANCE` on its instruction (`execInstrTonEnvGetExtraBalance`). -/
def extraBalance : VM Unit := execInstrTonEnvGetExtraBalance (.tonEnvOp .getExtraBalance) (pure ())

end DictTail

namespace TvmLean

/-- `GETEXTRABALANCE` runs as `DictTail.extraBalance`. -/
theorem DictTail.extraBalanceHandler_eq (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .getExtraBalance)) st = ExceptT.run DictTail.extraBalance st := by
  simp only [DictTail.extraBalance, TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok]

end TvmLean

namespace TvmLean.Framed

open TvmLean

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`GETEXTRABALANCE` on any stack is framed** (`StepsX`): the stack under the currency `ExtraOk`. -/
theorem StepsX.extraBalance : StepsX DictTail.extraBalance (fun _ s s' => ExtraOk1 s s') := by
  unfold DictTail.extraBalance execInstrTonEnvGetExtraBalance
  simp (config := { zeta := false }) only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind]
  stepsx_auto

/-- **`GETEXTRABALANCE` on any balance is framed**, with the frame that lets the counters of its cheap
calls change: from a stack `s a`, `ExtraOk s`, or an exception of code 2 or more. -/
theorem extraBalance_framed (s : Stack) (a : Value) (st : VmState) (hs : st.stack = s.push a) :
    ExecFramedC true (.tonEnvOp .getExtraBalance) (ExtraOk s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := StepsX.extraBalance st
  rw [← DictTail.extraBalanceHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, a', e, hok⟩ := h2 () h
  rw [hs] at e
  rw [(Array.push_eq_push.mp e).2]
  exact hok

/-- **A run from `GETEXTRABALANCE` on any balance.** `st` is about to run it (decoded from `code`, the
code after it `rest`) on the stack `s a`: if `P` holds of every result that commits nothing and of
every run from the state after it with a stack `ExtraOk s`, any gas, loaded cells and libraries and
any counters of the cheap calls (`afterC`), it holds of the run. -/
theorem runWith_extraBalance {st : VmState} {code rest : Slice} {s : Stack} {a : Value}
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (.tonEnvOp .getExtraBalance, k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = s.push a)
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hok : ∀ s' g lc ll ec fg n, n < fuel → ExtraOk s s' →
      P (VmState.runWith execInstr n (afterC st rest s' g lc ll ec fg))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framedC (c := true) (Ok := ExtraOk s)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom, fun st0 h1 _ => extraBalance_framed s a st0 (h1.trans hs)⟩
    hr hm P hP fuel (fun s' g lc ll ec fg n hn hok' _ => hok s' g lc ll ec fg n hn hok')

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_extra_balance_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S` written
out) is about to run `GETEXTRABALANCE`: by `Framed.runWith_extraBalance`, two goals: `P` of a result
that commits nothing, and `P` of the runs from the state after it with a stack `Framed.ExtraOk s`, any
gas, loaded cells, libraries and counters of the cheap calls. -/
elab "vm_extra_balance_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_extra_balance_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  let iE' ← whnfR iE
  unless iE'.isAppOfArity ``Instr.tonEnvOp 1 && (← whnfR iE'.appArg!).isConstOf ``TonEnvInstr.getExtraBalance do
    throwError "vm_extra_balance_any: the instruction is {iE'}"
  let stk ← whnfR (← mkAppM ``VmState.stack #[S])
  unless stk.isAppOfArity ``Array.push 3 do throwError "vm_extra_balance_any: the stack is not written out"
  let motive ← withLocalDeclD `r (mkConst ``StepResult) fun rv => do
    mkLambdaFVars #[rv] ((← kabstract t r).instantiate1 rv)
  let refl (e : Expr) : MetaM Expr := mkEqRefl e
  let hcc ← refl (← mkAppM ``VmState.cc #[S])
  let hcp ← refl (← mkAppM ``VmState.cp #[S])
  let hchain ← Exec.decideProof (← mkAppM ``LT.lt #[← whnfCore (← whnfR (← mkAppM ``VmState.chainJumps #[S])),
    mkConst ``freeNestedContJump])
  let hc2 ← refl (← mkAppM ``Regs.c2 #[← mkAppM ``VmState.regs #[S]])
  let hcom ← refl (← mkAppM ``CommittedState.committed #[← mkAppM ``VmState.cstate #[S]])
  let hr ← refl (← mkAppM ``VmState.librariesRefused #[S])
  let hm ← refl (← mkAppM ``VmState.librariesMissed #[S])
  let hs ← refl (← mkAppM ``VmState.stack #[S])
  let f ← mkAppOptM ``Framed.runWith_extraBalance #[S, none, none, stk.getArg! 1, stk.getArg! 2, hcc, hcp,
    hbitsNe, hverLe, hdecEx, hchain, hc2, hcom, hr, hm, hs, motive]
  let (f1, goals1) ← Exec.applyRest f 1 #[fuel]
  let (pf, goals2) ← Exec.applyRest f1 1 #[]
  let goals := goals1 ++ goals2
  unless ← isDefEq (← inferType pf) t do throwError "vm_extra_balance_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

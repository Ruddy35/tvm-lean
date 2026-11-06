import TvmLean.Proofs.Exec.FramedExtraBalance

/-!
# The BLS forms with a count on the stack, framed

`BLS_AGGREGATE`, `BLS_FASTAGGREGATEVERIFY`, `BLS_AGGREGATEVERIFY`, `BLS_G1_MULTIEXP`,
`BLS_G2_MULTIEXP`, `BLS_PAIRING` (C++ crypto/vm/tonops.cpp, `exec_bls_*`) pop a count `n` and then
`n` (or `2n`) entries in a loop: on a count the run does not know, their handlers cannot be
followed. They are framed (`Framed.ExecFramed`, TvmLean/Proofs/Exec/Framed.lean): they change the
stack and the gas only; the stack after is some of the stack before with its top entries popped
(`Below`) and a slice (the aggregate, the point) or an integer (the flag) pushed; they fail only
with an exception of code 2 or more.

* `Below`, `BlsSliceOk`, `BlsIntOk`; `Steps.below_bind`, `Steps.forIn_range_below` and the tactic
  `steps_below_auto` (as `stepsx_auto`, TvmLean/Proofs/Exec/FramedExtraBalance.lean, for `Steps`
  with the pops as `Below` steps);
* `DictTail.bls op`: the handler on its instruction (`DictTail.blsHandler_eq`);
* `Framed.bls_framed`, `Framed.runWith_bls`, tactic `vm_bls_any`.
-/

namespace TvmLean.Framed

open TvmLean

/-- The stack `s'` is the stack `s` with some of its top entries popped. -/
def Below (s' s : Stack) : Prop := s'.toList <+: s.toList

theorem Below.refl (s : Stack) : Below s s := List.prefix_refl _

theorem Below.trans {a b c : Stack} (h1 : Below a b) (h2 : Below b c) : Below a c :=
  List.IsPrefix.trans h1 h2

theorem Below.push (s : Stack) (v : Value) : Below s (s.push v) := by
  unfold Below
  rw [Array.toList_push]
  exact List.prefix_append _ _

theorem Below.pop {s s' : Stack} {v : Value} (h : s = s'.push v) : Below s' s := h ▸ Below.push s' v

/-- What the BLS forms that make a point leave: some top entries of the stack popped, a slice
pushed. -/
def BlsSliceOk (s s' : Stack) : Prop := ∃ (s0 : Stack) (sl : Slice), Below s0 s ∧ s' = s0.push (.slice sl)

/-- What the BLS forms that verify leave: some top entries of the stack popped, an integer pushed. -/
def BlsIntOk (s s' : Stack) : Prop := ∃ (s0 : Stack) (x : Int), Below s0 s ∧ s' = s0.push (.int (.num x))

theorem BlsSliceOk.below {s0 s1 s' : Stack} (h : Below s1 s0) (h' : BlsSliceOk s1 s') : BlsSliceOk s0 s' := by
  obtain ⟨a, sl, ha, rfl⟩ := h'
  exact ⟨a, sl, ha.trans h, rfl⟩

theorem BlsIntOk.below {s0 s1 s' : Stack} (h : Below s1 s0) (h' : BlsIntOk s1 s') : BlsIntOk s0 s' := by
  obtain ⟨a, x, ha, rfl⟩ := h'
  exact ⟨a, x, ha.trans h, rfl⟩

/-- A step that pops some entries, then `f`: the relation of the whole from that of `f`, if it
holds of a stack whenever it holds of one with some entries popped (`hR`). -/
theorem Steps.below_bind {α β : Type} {m : VM α} {f : α → VM β} {R : Stack → Stack → Prop}
    (hR : ∀ s0 s1 s', Below s1 s0 → R s1 s' → R s0 s')
    (hm : Steps m (fun _ s s' => Below s' s)) (hf : ∀ a, Steps (f a) (fun _ s s' => R s s')) :
    Steps (m >>= f) (fun _ s s' => R s s') :=
  Steps.mono (Steps.bind hm hf) (by
    rintro _ s s'' ⟨_, s1, h1, h2⟩
    exact hR _ _ _ h1 h2)

theorem Steps.pop_below {α : Type} {m : VM α} (h : Steps m (fun _ s s' => ∃ v, s = s'.push v)) :
    Steps m (fun _ s s' => Below s' s) :=
  Steps.mono h (fun _ _ _ ⟨_, e⟩ => Below.pop e)

theorem Steps.keep_below {α : Type} {m : VM α} (h : Steps m (fun _ s s' => s' = s)) :
    Steps m (fun _ s s' => Below s' s) :=
  Steps.mono h (fun _ s _ e => e ▸ Below.refl s)

/-- A loop whose every step pops some entries pops some entries. -/
theorem Steps.forIn_list_below {α β : Type} (l : List α) (b0 : β) (f : α → β → VM (ForInStep β))
    (hf : ∀ x b, Steps (f x b) (fun _ s s' => Below s' s)) :
    Steps (forIn l b0 f) (fun _ s s' => Below s' s) := by
  induction l generalizing b0 with
  | nil =>
    simp only [List.forIn_nil]
    exact Steps.keep_below (Steps.mono (Steps.pure _) (fun _ _ _ h => h.2))
  | cons x l ih =>
    simp only [List.forIn_cons]
    refine Steps.below_bind (fun _ _ _ h1 h2 => h2.trans h1) (hf x b0) (fun r => ?_)
    cases r with
    | done b => exact Steps.keep_below (Steps.mono (Steps.pure _) (fun _ _ _ h => h.2))
    | yield b => exact ih b

/-- `Steps.forIn_list_below` over a range (the loops `for j in [0:n]` of the handlers). -/
theorem Steps.forIn_range_below {β : Type} (r : Std.Range) (b0 : β) (f : Nat → β → VM (ForInStep β))
    (hf : ∀ x b, Steps (f x b) (fun _ s s' => Below s' s)) :
    Steps (forIn r b0 f) (fun _ s s' => Below s' s) := by
  rw [Std.Range.forIn_eq_forIn_range']
  exact Steps.forIn_list_below _ _ _ hf

/-- The count of `BLS_AGGREGATE` (`popNatInRange`): a pop. -/
theorem Steps.popNatInRange (lo hi : Nat) : Steps (popNatInRange lo hi) (fun _ s s' => ∃ v, s = s'.push v) := by
  unfold TvmLean.popNatInRange
  refine Steps.mono (Steps.bind Steps.popInt (fun v => (?_ : Steps _ (fun _ s s' => s' = s)))) ?_
  · split
    · exact Steps.throw _ (by decide) _
    · simp only [pure_bind]
      repeat' (first
        | (refine Steps.ite_bind (fun _ => ?_) (fun _ => ?_))
        | (refine Steps.ite_R (fun _ => ?_) (fun _ => ?_))
        | exact Steps.throw_bind (by decide)
        | exact Steps.throw_R (by decide)
        | exact Steps.pure_end (fun _ => rfl)
        | (simp only [pure_bind, bind_assoc]))
  · rintro _ s s'' ⟨i, s1, h1, h2⟩
    exact ⟨.int i, by rw [h1, h2]⟩

/-- The read of bytes of a slice fails only with cell_und. -/
theorem prefetchBytes_real {sl : Slice} {k : Nat} {e : Excno} (h : sl.prefetchBytesCellUnd k = .error e) :
    2 ≤ e.toInt := by
  simp only [Slice.prefetchBytesCellUnd] at h
  split at h
  · cases h
  · cases h; decide

/-- The read of all the bytes of a slice (`sliceToFullBytes`) fails only with cell_und. -/
theorem sliceToFullBytes_real {sl : Slice} {e : Excno} (h : sliceToFullBytes sl = .error e) :
    2 ≤ e.toInt := by
  simp only [sliceToFullBytes] at h
  split at h
  · cases h; decide
  · exact prefetchBytes_real h

macro_rules
  | `(tactic| steps_err) => `(tactic| first
      | exact prefetchBytes_real (by assumption)
      | exact sliceToFullBytes_real (by assumption)
      | fail "not a read of bytes")

/-- An obligation of `steps_below_step`: the relation kept by pops (`BlsSliceOk.below`,
`BlsIntOk.below`, `Below.trans`), or the stack named by the combinators (`Below.refl`, the case of
`BlsSliceOk`, `BlsIntOk`). -/
macro "steps_below_close" : tactic => `(tactic| first
  | exact fun _ _ _ h1 h2 => BlsSliceOk.below h1 h2
  | exact fun _ _ _ h1 h2 => BlsIntOk.below h1 h2
  | exact fun _ _ _ h1 h2 => Below.trans h2 h1
  | exact fun s => Below.refl s
  | exact fun s => ⟨s, _, Below.refl s, rfl⟩)

/-- Follows a VM program with the combinators of `Steps` of a fixed relation, its pops as `Below`
steps (`steps_below_step` until none applies). -/
syntax "steps_below_auto" : tactic

open Lean Meta Elab Tactic in
/-- The tactic that proves `Steps a (fun _ s s' => Below s' s)` for a step `a` that pops some
entries (a pop, a loop of such steps), chosen by the head of `a`, or one that leaves the stack
(`Steps.keep_below`); `none` for any other step. -/
def belowLeafTac? (a : Expr) : MetaM (Option (TSyntax `tactic)) := do
  let some c := a.getAppFn.constName? | return none
  if c == ``VM.pop then return some (← `(tactic| exact Steps.pop_below Steps.pop))
  if c == ``VM.popNatUpTo then return some (← `(tactic| exact Steps.pop_below (Steps.popNatUpTo _)))
  if c == ``popNatInRange then return some (← `(tactic| exact Steps.pop_below (Steps.popNatInRange _ _)))
  if c == ``VM.popInt then return some (← `(tactic| exact Steps.pop_below Steps.popInt'))
  if c == ``VM.popIntFinite then return some (← `(tactic| exact Steps.pop_below Steps.popIntFinite))
  if c == ``VM.popSlice then return some (← `(tactic| exact Steps.pop_below Steps.popSlice))
  if c == ``ForIn.forIn then
    return some (← `(tactic| exact Steps.forIn_range_below _ _ _ (fun _ _ => by steps_below_auto)))
  if c == ``VM.consumeGas then return some (← `(tactic| exact Steps.keep_below (Steps.consumeGas _)))
  if c == ``MonadState.get || c == ``MonadStateOf.get || c == ``getThe then
    return some (← `(tactic| exact Steps.keep_below Steps.get))
  if c == ``VM.checkUnderflow then return some (← `(tactic| exact Steps.keep_below (Steps.checkUnderflow _)))
  return none

open Lean Meta Elab Tactic in
/-- `steps_below_step`: one step on the main goal `Steps m P`, chosen by the head of the program
`m`: a `let` (`stepsx_let`); a call of a local function (`stepsx_hyp`); a bind of a step that pops
some entries or leaves the stack (`Steps.below_bind`, its obligation `hR` by `steps_below_close`), of
an `if`, of a `throw` (its code by `steps_err`), of a `pure` or of a bind; a push, a `pure`, a
`throw`, an `if` at the end; a `match` (`split`). A goal that is not `Steps` (an obligation) is
closed by `steps_below_close`. Fails if nothing applies. -/
elab "steps_below_step" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Steps 3 do
    evalTactic (← `(tactic| steps_below_close))
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
    if let some leaf ← belowLeafTac? a then
      run #[← `(tactic| refine Steps.below_bind ?_ ?_ (fun _ => ?_)), ← `(tactic| steps_below_close), leaf]
      return
    if a.isAppOfArity ``ite 5 then
      run #[← `(tactic| refine Steps.ite_bind (fun _ => ?_) (fun _ => ?_))]
      return
    if isThrow a then
      run #[← `(tactic| refine Steps.throw_bind ?_), ← `(tactic| steps_err)]
      return
    if a.isAppOf ``Pure.pure then
      run #[← `(tactic| simp (config := { zeta := false }) only [pure_bind])]
      return
    if a.isAppOfArity ``Bind.bind 6 then
      run #[← `(tactic| simp (config := { zeta := false }) only [bind_assoc])]
      return
    throwError "steps_below_step: a bind of {a.getAppFn}"
  if m.isAppOf ``VM.push then
    run #[← `(tactic| refine Steps.push_end ?_)]
    return
  if m.isAppOf ``VM.pushSmallInt then
    run #[← `(tactic| simp only [VM.pushSmallInt])]
    return
  if m.isAppOf ``VM.pushIntQuiet then
    run #[← `(tactic| refine Steps.pushIntQuiet_end ?_)]
    return
  if m.isAppOf ``Pure.pure then
    run #[← `(tactic| refine Steps.pure_end ?_)]
    return
  if isThrow m then
    run #[← `(tactic| refine Steps.throw_R ?_), ← `(tactic| steps_err)]
    return
  if m.isAppOfArity ``ite 5 then
    run #[← `(tactic| refine Steps.ite_R (fun _ => ?_) (fun _ => ?_))]
    return
  if ← Meta.isMatcherApp m then
    run #[← `(tactic| split)]
    return
  throwError "steps_below_step: the program {m.getAppFn}"

macro_rules
  | `(tactic| steps_below_auto) => `(tactic| repeat' steps_below_step)

open Lean Meta Elab Tactic in
/-- `steps_dispatch`: the program of the goal (`Steps m P`) a dispatcher of `execInstr` applied to
an instruction (`execInstrCryptoExt i next`): the handler of the instruction in its place (the
dispatchers unfolded and their `match`es reduced, `Exec.followDispatch`, a definitional step). -/
elab "steps_dispatch" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Steps 3 do throwError "steps_dispatch: the goal is not `Steps`"
  let some m' ← withTransparency .all (Exec.followDispatch (t.getArg! 1))
    | throwError "steps_dispatch: no handler"
  replaceMainGoal [← g.replaceTargetDefEq (mkAppN t.getAppFn (t.getAppArgs.set! 1 m'))]

end TvmLean.Framed

/-! ## The handlers -/

namespace DictTail

open TvmLean

/-- The handler of the BLS forms on the instruction `op` (`execInstrCryptoExt`). -/
def bls (op : CryptoExtInstr) : VM Unit := execInstrCryptoExt (.cryptoOp (.ext op)) (pure ())

/-- The BLS forms with a count on the stack. -/
def IsBlsCount : CryptoExtInstr → Prop
  | .blsAggregate | .blsFastAggregateVerify | .blsAggregateVerify | .blsG1MultiExp | .blsG2MultiExp
  | .blsPairing => True
  | _ => False

end DictTail

namespace TvmLean

/-- A BLS form with a count runs as `DictTail.bls`. -/
theorem DictTail.blsHandler_eq (op : CryptoExtInstr) (hop : DictTail.IsBlsCount op) (st : VmState) :
    ExceptT.run (execInstr (.cryptoOp (.ext op))) st = ExceptT.run (DictTail.bls op) st := by
  cases op <;> first
    | exact hop.elim
    | simp only [DictTail.bls, TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok]

end TvmLean

namespace TvmLean.Framed

open TvmLean

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`BLS_AGGREGATE` on any stack**: some entries popped, a slice pushed. -/
theorem Steps.blsAggregate : Steps (DictTail.bls .blsAggregate) (fun _ s s' => BlsSliceOk s s') := by
  unfold DictTail.bls
  steps_dispatch
  steps_below_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`BLS_FASTAGGREGATEVERIFY` on any stack**: some entries popped, an integer pushed. -/
theorem Steps.blsFastAggregateVerify : Steps (DictTail.bls .blsFastAggregateVerify) (fun _ s s' => BlsIntOk s s') := by
  unfold DictTail.bls
  steps_dispatch
  steps_below_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`BLS_AGGREGATEVERIFY` on any stack**: some entries popped, an integer pushed. -/
theorem Steps.blsAggregateVerify : Steps (DictTail.bls .blsAggregateVerify) (fun _ s s' => BlsIntOk s s') := by
  unfold DictTail.bls
  steps_dispatch
  steps_below_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`BLS_G1_MULTIEXP` on any stack**: some entries popped, a slice pushed. -/
theorem Steps.blsG1MultiExp : Steps (DictTail.bls .blsG1MultiExp) (fun _ s s' => BlsSliceOk s s') := by
  unfold DictTail.bls
  steps_dispatch
  steps_below_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`BLS_G2_MULTIEXP` on any stack**: some entries popped, a slice pushed. -/
theorem Steps.blsG2MultiExp : Steps (DictTail.bls .blsG2MultiExp) (fun _ s s' => BlsSliceOk s s') := by
  unfold DictTail.bls
  steps_dispatch
  steps_below_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`BLS_PAIRING` on any stack**: some entries popped, an integer pushed. -/
theorem Steps.blsPairing : Steps (DictTail.bls .blsPairing) (fun _ s s' => BlsIntOk s s') := by
  unfold DictTail.bls
  steps_dispatch
  steps_below_auto

/-- A BLS form whose handler is `Steps` with `R` is framed with `R` of the stack before. -/
theorem bls_framed {op : CryptoExtInstr} {R : Stack → Stack → Prop} (hop : DictTail.IsBlsCount op)
    (h : Steps (DictTail.bls op) (fun _ s s' => R s s')) (st : VmState) :
    ExecFramed (.cryptoOp (.ext op)) (R st.stack) st := by
  obtain ⟨h1, h2, h3, h4⟩ := h st
  rw [← DictTail.blsHandler_eq op hop] at h1 h2 h3 h4
  exact ⟨h1, fun hh => h2 () hh, h3, h4⟩

/-- **A run from a BLS form on a count the run does not know** (`runWith_framed`): if `P` holds of
every result that commits nothing and of every run from the state after it with a stack `R` of the
stack before (`BlsSliceOk`, `BlsIntOk`), any gas, loaded cells and libraries, it holds of the run. -/
theorem runWith_bls {op : CryptoExtInstr} {R : Stack → Stack → Prop} (hop : DictTail.IsBlsCount op)
    (h : Steps (DictTail.bls op) (fun _ s s' => R s s')) {st : VmState} {code rest : Slice}
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (.cryptoOp (.ext op), k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hok : ∀ s' g lc ll n, n < fuel → R st.stack s' → P (VmState.runWith execInstr n (after st rest s' g lc ll))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := R st.stack)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom, fun st0 h1 _ => h1 ▸ bls_framed hop h st0⟩
    hr hm P hP fuel hok

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- The `Steps` theorem of the BLS form `op` with a count on the stack (`Framed.Steps.blsAggregate`,
...), if it is one. -/
def blsSteps? (op : Expr) : MetaM (Option Name) := do
  let some c := (← whnfR op).constName? | return none
  if c == ``CryptoExtInstr.blsAggregate then return some ``Framed.Steps.blsAggregate
  if c == ``CryptoExtInstr.blsFastAggregateVerify then return some ``Framed.Steps.blsFastAggregateVerify
  if c == ``CryptoExtInstr.blsAggregateVerify then return some ``Framed.Steps.blsAggregateVerify
  if c == ``CryptoExtInstr.blsG1MultiExp then return some ``Framed.Steps.blsG1MultiExp
  if c == ``CryptoExtInstr.blsG2MultiExp then return some ``Framed.Steps.blsG2MultiExp
  if c == ``CryptoExtInstr.blsPairing then return some ``Framed.Steps.blsPairing
  return none

open Lean Meta Elab Tactic in
/-- `vm_bls_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S` written out) is
about to run a BLS form with a count on the stack: by `Framed.runWith_bls`, two goals: `P` of a
result that commits nothing, and `P` of the runs from the state after it with a stack
`Framed.BlsSliceOk` or `Framed.BlsIntOk` of the stack before, any gas, loaded cells and libraries. -/
elab "vm_bls_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_bls_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  let iE' ← whnfR iE
  unless iE'.isAppOfArity ``Instr.cryptoOp 1 do throwError "vm_bls_any: the instruction is {iE'}"
  let ext ← whnfR iE'.appArg!
  unless ext.isAppOfArity ``CryptoInstr.ext 1 do throwError "vm_bls_any: the instruction is {iE'}"
  let some thm ← blsSteps? ext.appArg! | throwError "vm_bls_any: the instruction is {iE'}"
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
  let f ← mkAppOptM ``Framed.runWith_bls #[ext.appArg!, none, mkConst ``True.intro, mkConst thm, S, none, none,
    hcc, hcp,
    hbitsNe, hverLe, hdecEx, hchain, hc2, hcom, hr, hm, motive]
  let (f1, goals1) ← Exec.applyRest f 1 #[fuel]
  let (pf, goals2) ← Exec.applyRest f1 1 #[]
  let goals := goals1 ++ goals2
  unless ← isDefEq (← inferType pf) t do throwError "vm_bls_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

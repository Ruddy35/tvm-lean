import TvmLean.Proofs.Exec.FramedDict

/-!
# `CONFIGPARAM`/`CONFIGOPTPARAM` on any configuration, framed

`CONFIGPARAM i` reads the configuration dictionary from `c7` (its parameter 9: a cell or null) and
looks up the 32-bit key `i` in it (C++ `exec_get_config_param`, tonops.cpp). A run that does not
know `c7` (any parameters) does not know the dictionary either. The instruction is framed
(`TvmLean.Framed.ExecFramed`, TvmLean/Proofs/Exec/Framed.lean): it changes the stack, the gas, the
loaded cells and libraries only; it leaves the value found (a cell, with `-1` for `CONFIGPARAM`) or
none (`0`, or null for `CONFIGOPTPARAM`); it fails only with an exception of code 2 or more (the
stack, `c7` not a tuple of parameters, cell_und or dict_err of the lookup, out of gas of the loads).

* `Steps.popInt`, `Steps.pushC7Param`, `Steps.popMaybeCell`, `Steps.cellResolver`: the parts of the
  instruction as framed computations (`Framed.Steps`, TvmLean/Proofs/Exec/FramedDict.lean);
* `configParam_framed`: the instruction from any state with an integer on top of its stack;
* `runWith_configParam`, tactic `vm_config_param_any`: the run from a state about to run it.
-/

namespace TvmLean.Framed

open TvmLean

/-! ## The parts -/

/-- A stack with an entry on top is its pop with that entry pushed back. -/
theorem stack_eq_pop_push_back (xs : Stack) (h : 0 < xs.size) : xs = xs.pop.push (xs.back h) := by
  have e := Array.eq_push_pop_back!_of_size_ne_zero (xs := xs) (by omega)
  rw [Array.back!_eq_back?, Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega),
    Option.getD_some, ← Array.back_eq_getElem h] at e
  exact e

/-- A computation that fails at once with an exception of code 2 or more, or that changes only the
stack by pushing one value: what `Steps` asks of the leaves below. -/
macro "steps_leaf" : tactic => `(tactic| first
  | (refine ⟨Frame.refl _, ?_, ?_, fun _ => rfl⟩ <;> intro _ h <;> cases h <;> decide)
  | (refine ⟨rfl, fun _ _ => ⟨_, rfl⟩, ?_, fun _ => rfl⟩; intro _ h; cases h))

theorem Steps.popInt : Steps VM.popInt (fun i s s' => s = s'.push (.int i)) := by
  intro st
  rw [VM.run_popInt]
  split
  · rename_i h
    split
    · rename_i i hb
      refine ⟨rfl, ?_, ?_, fun _ => rfl⟩
      · intro a ha
        cases ha
        show st.stack = st.stack.pop.push (.int i)
        rw [← hb]
        exact stack_eq_pop_push_back st.stack h
      · intro e he; cases he
    · steps_leaf
  · steps_leaf

theorem Steps.popMaybeCell : Steps VM.popMaybeCell (fun _ s s' => ∃ v, s = s'.push v) := by
  intro st
  unfold VM.popMaybeCell
  rw [VM.run_bind, VM.run_pop]
  split
  · rename_i h
    rw [VM.bindRes_ok]
    have hst := stack_eq_pop_push_back st.stack h
    split
    · rw [VM.run_pure]
      refine ⟨rfl, fun _ _ => ⟨_, hst⟩, ?_, fun _ => rfl⟩
      intro e he; cases he
    · rw [VM.run_pure]
      refine ⟨rfl, fun _ _ => ⟨_, hst⟩, ?_, fun _ => rfl⟩
      intro e he; cases he
    · rw [VM.run_throw]
      refine ⟨rfl, ?_, ?_, fun _ => rfl⟩
      · intro a ha; cases ha
      · intro e he; cases he; decide
  · rw [VM.bindRes_error]
    steps_leaf

theorem Steps.pushC7Param (idx : Nat) :
    Steps (VM.pushC7Param idx) (fun _ s s' => ∃ v, s' = s.push v) := by
  intro st
  simp only [VM.pushC7Param, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_ite, VM.run_throw]
  split
  · split
    · split
      · steps_leaf
      · split
        · steps_leaf
        · steps_leaf
    · steps_leaf
  · steps_leaf

theorem Steps.cellResolver : Steps VM.cellResolver (fun r s s' => s' = s ∧ ResolverCellUnd r) := by
  intro st
  unfold VM.cellResolver
  rw [VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_pure]
  refine ⟨Frame.refl _, ?_, ?_, fun _ => rfl⟩
  · intro r h; cases h; exact ⟨rfl, resolverCellUnd_library _ _ _⟩
  · intro e h; cases h

/-! ## `CONFIGPARAM`, `CONFIGOPTPARAM` -/

/-- What `CONFIGPARAM` (`opt` false) and `CONFIGOPTPARAM` (`opt` true) leave on the stack `s` under
the key: the parameter's cell (and `-1` for `CONFIGPARAM`), or none (`0`, or null). -/
def ConfigOk : Bool → Stack → Stack → Prop
  | true, s, s' => s' = s.push .null ∨ ∃ c, s' = s.push (.cell c)
  | false, s, s' => s' = s.push (.int (.num 0)) ∨ ∃ c, s' = (s.push (.cell c)).push (.int (.num (-1)))

theorem Steps.configParam (opt : Bool) :
    Steps (execInstrTonEnvConfigParam (.tonEnvOp (.configParam opt)) (Pure.pure () : VM Unit))
      (fun _ s s'' => ∃ s0 i, s = s0.push (.int i) ∧ ConfigOk opt s0 s'') := by
  unfold execInstrTonEnvConfigParam
  dsimp only
  refine Steps.mono (Steps.bind Steps.popInt (fun i => Steps.bind (Steps.pushC7Param 9) (fun _ =>
    Steps.bind Steps.popMaybeCell (fun root => (?_ : Steps _ (fun _ s s' => ConfigOk opt s s')))))) ?_
  · cases opt
    · -- CONFIGPARAM
      simp only [Bool.false_eq_true, if_false]
      split
      · exact Steps.mono (Steps.push _) (fun _ s s' h => by simp only [ConfigOk]; exact Or.inl h)
      simp only [VM.cellResolver, bind_assoc, pure_bind]
      refine Steps.mono (Steps.bind Steps.get (fun x => (?_ : Steps _ (fun _ s s' => ConfigOk false s s')))) ?_
      rotate_left
      · rintro _ s s'' ⟨_, s1, h1, h2⟩
        rw [h1] at h2; exact h2
      split
      · rename_i e he
        have he2 : 2 ≤ e.toInt := by
          rcases dictLookupWithCells_err _ _ _ (resolverCellUnd_library _ _ _) e he with h | h <;>
            (subst h; decide)
        refine Steps.mono (Steps.bind Steps.get (fun _ => Steps.bind (Steps.forLoads _) (fun _ =>
          Steps.throw e he2 (fun _ s s' => ConfigOk false s s')))) ?_
        rintro _ s s'' ⟨_, s1, h1, _, s2, h2, h3⟩
        rw [h1] at h2; rw [h2] at h3; exact h3
      · refine Steps.mono (Steps.bind (Steps.forLoads _) (fun _ => Steps.push _)) ?_
        rintro _ s s'' ⟨_, s1, h1, h2⟩
        rw [h1] at h2; simp only [ConfigOk]; exact Or.inl h2
      · refine Steps.mono (Steps.bind (Steps.forLoads _) (fun _ =>
          (?_ : Steps _ (fun _ s s' => ConfigOk false s s')))) ?_
        · split
          · first
              | exact Steps.mono (Steps.push _) (fun _ s s' h => by simp only [ConfigOk]; exact Or.inr ⟨_, h⟩)
              | (refine Steps.mono (Steps.bind (Steps.push _) (fun _ => Steps.push (.int (.num (-1))))) ?_
                 rintro _ s s'' ⟨_, s1, h1, h2⟩
                 rw [h1] at h2; simp only [ConfigOk]; exact Or.inr ⟨_, h2⟩)
          · exact Steps.throw _ (by decide) _
        · rintro _ s s'' ⟨_, s1, h1, h2⟩
          rw [h1] at h2; exact h2
    · -- CONFIGOPTPARAM
      simp only [if_true]
      split
      · exact Steps.mono (Steps.push _) (fun _ s s' h => by simp only [ConfigOk]; exact Or.inl h)
      simp only [VM.cellResolver, bind_assoc, pure_bind]
      refine Steps.mono (Steps.bind Steps.get (fun x => (?_ : Steps _ (fun _ s s' => ConfigOk true s s')))) ?_
      rotate_left
      · rintro _ s s'' ⟨_, s1, h1, h2⟩
        rw [h1] at h2; exact h2
      split
      · rename_i e he
        have he2 : 2 ≤ e.toInt := by
          rcases dictLookupWithCells_err _ _ _ (resolverCellUnd_library _ _ _) e he with h | h <;>
            (subst h; decide)
        refine Steps.mono (Steps.bind Steps.get (fun _ => Steps.bind (Steps.forLoads _) (fun _ =>
          Steps.throw e he2 (fun _ s s' => ConfigOk true s s')))) ?_
        rintro _ s s'' ⟨_, s1, h1, _, s2, h2, h3⟩
        rw [h1] at h2; rw [h2] at h3; exact h3
      · refine Steps.mono (Steps.bind (Steps.forLoads _) (fun _ => Steps.push _)) ?_
        rintro _ s s'' ⟨_, s1, h1, h2⟩
        rw [h1] at h2; simp only [ConfigOk]; exact Or.inl h2
      · refine Steps.mono (Steps.bind (Steps.forLoads _) (fun _ =>
          (?_ : Steps _ (fun _ s s' => ConfigOk true s s')))) ?_
        · split
          · first
              | exact Steps.mono (Steps.push _) (fun _ s s' h => by simp only [ConfigOk]; exact Or.inr ⟨_, h⟩)
              | (refine Steps.mono (Steps.bind (Steps.push _) (fun _ => Steps.push (.int (.num (-1))))) ?_
                 rintro _ s s'' ⟨_, s1, h1, h2⟩
                 rw [h1] at h2; simp only [ConfigOk]; exact Or.inr ⟨_, h2⟩)
          · exact Steps.throw _ (by decide) _
        · rintro _ s s'' ⟨_, s1, h1, h2⟩
          rw [h1] at h2; exact h2
  · rintro _ s s'' ⟨i, s1, h1, _, s2, ⟨v, h2⟩, r, s3, ⟨v', h3⟩, h4⟩
    rw [h2] at h3
    obtain ⟨_, hs⟩ := Array.push_eq_push.mp h3
    subst hs
    exact ⟨_, i, h1, h4⟩

/-- `CONFIGPARAM`/`CONFIGOPTPARAM` runs as `execInstrTonEnvConfigParam` (the dispatch). -/
theorem configParam_eq (opt : Bool) (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp (.configParam opt))) st =
      ExceptT.run (execInstrTonEnvConfigParam (.tonEnvOp (.configParam opt)) (Pure.pure () : VM Unit)) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

/-- **`CONFIGPARAM`/`CONFIGOPTPARAM` on any configuration is framed**: from a stack `s` with the key
on top, the parameter's cell (with `-1` for `CONFIGPARAM`) or none (`0`, or null), or an exception
of code 2 or more. -/
theorem configParam_framed (opt : Bool) (st : VmState) (s : Stack) (idx : IntVal)
    (hs : st.stack = s.push (.int idx)) : ExecFramed (.tonEnvOp (.configParam opt)) (ConfigOk opt s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.configParam opt st
  rw [← configParam_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, i, e, hok⟩ := h2 () h
  rw [hs] at e
  obtain ⟨_, hs0⟩ := Array.push_eq_push.mp e
  rw [hs0]
  exact hok

/-- **A run from `CONFIGPARAM`/`CONFIGOPTPARAM` on any configuration.** `st` is about to run it
(decoded from `code`, the code after it `rest`) on the stack `s idx`: if `P` holds of every result
that commits nothing and of every run from the state after it with a stack `ConfigOk opt s`, any gas,
loaded cells and libraries (`after`), it holds of the run. -/
theorem runWith_configParam {st : VmState} {code rest : Slice} {s : Stack} {idx : IntVal} {opt : Bool}
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (.tonEnvOp (.configParam opt), k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = s.push (.int idx))
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r)
    (hok : ∀ s' g lc ll fuel, ConfigOk opt s s' →
      P (VmState.runWith execInstr fuel (after st rest s' g lc ll)))
    (fuel : Nat) : P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := ConfigOk opt s)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom,
      fun st0 h1 _ => configParam_framed opt st0 s idx (h1.trans hs)⟩ hr hm P hP hok fuel

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_config_param_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S` written
out) is about to run `CONFIGPARAM` or `CONFIGOPTPARAM` on a configuration it does not know: by
`Framed.runWith_configParam`, two goals: `P` of a result that commits nothing, and `P` of the runs
from the state after it with a stack `Framed.ConfigOk opt s` (the parameter found or not), any gas,
loaded cells and libraries. -/
elab "vm_config_param_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_config_param_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  let iE ← whnfR iE
  unless iE.isAppOfArity ``Instr.tonEnvOp 1 do throwError "vm_config_param_any: the instruction is {iE}"
  let op ← whnfR iE.appArg!
  unless op.isAppOfArity ``TonEnvInstr.configParam 1 do
    throwError "vm_config_param_any: not CONFIGPARAM or CONFIGOPTPARAM"
  let stk ← whnfR (← mkAppM ``VmState.stack #[S])
  unless stk.isAppOfArity ``Array.push 3 do throwError "vm_config_param_any: the stack is not written out"
  let vidx ← whnfR (stk.getArg! 2)
  unless vidx.isAppOfArity ``Value.int 1 do throwError "vm_config_param_any: no integer on top"
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
  let f ← mkAppOptM ``Framed.runWith_configParam #[S, none, none, stk.getArg! 1, vidx.appArg!,
    op.appArg!, hcc, hcp, hbitsNe, hverLe, hdecEx, hchain, hc2, hcom, hr, hm, hs, motive]
  let (pf, goals) ← Exec.applyRest f 2 #[fuel]
  unless ← isDefEq (← inferType pf) t do throwError "vm_config_param_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

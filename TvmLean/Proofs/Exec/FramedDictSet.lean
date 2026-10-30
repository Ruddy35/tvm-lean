import TvmLean.Proofs.Exec.FramedDictMinMax

/-!
# `DICT{,I,U}SET{,REF,B}`, `...ADD`, `...REPLACE`, `DICT{,I,U}REPLACEB` on any dictionary, framed

A set into a dictionary whose cells a run does not know and of which no `Dict.WF` is known (the
specifications of TvmLean/Proofs/Exec/Spec/DictSet.lean need it) is framed
(`TvmLean.Framed.ExecFramed`): the instruction changes the stack, the gas, the loaded cells and
libraries only; it pushes the new root (null or a cell) and, but for the mode `.set`, a flag; it fails
only with an exception of code 2 or more.

* `dictSetGenAuxWithCells_real`: the set of the model fails only with cell_und, dict_err or cell_ov
  (by induction on the key's length, its measure of termination), whatever the value it stores
  fails with (`ErrReal`);
* `Steps.chargeDictSetCreates`, `Steps.pop_bind`: the charge of the cells a set creates, the pops of the
  handler, as framed computations;
* `DictTail.replaceB`: the handler of `DICT{,I,U}REPLACEB` (TvmLean/Semantics/Exec/Dict/DictReplaceB.lean)
  with its tail named, the same code;
* `Framed.dictSet_framed`, `Framed.dictSetB_framed`, `Framed.replaceB_framed`, `Framed.runWith_dictSet`,
  tactic `vm_dict_set_any`.
-/

namespace TvmLean.Framed

open TvmLean

/-! ## Errors of the set -/

theorem ErrReal.ok {α : Type} (a : α) : ErrReal (.ok a : Except Excno α) := by
  intro e h; cases h

theorem ErrReal.pure {α : Type} (a : α) : ErrReal (pure a : Except Excno α) := by
  intro e h; cases h

theorem ErrReal.throw {α : Type} {e : Excno} (he : 2 ≤ e.toInt) : ErrReal (MonadExcept.throw e : Except Excno α) := by
  intro e' h; cases h; exact he

theorem ErrReal.bind {α β : Type} {x : Except Excno α} {f : α → Except Excno β} (hx : ErrReal x)
    (hf : ∀ a, ErrReal (f a)) : ErrReal (x >>= f) := by
  intro e h
  cases x with
  | error e' => cases h; exact hx _ rfl
  | ok a => exact hf a e h

theorem ErrReal.ite {α : Type} {c : Prop} [Decidable c] {x y : Except Excno α} (hx : ErrReal x)
    (hy : ErrReal y) : ErrReal (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem ErrReal.dite {α : Type} {c : Prop} [Decidable c] {x : c → Except Excno α} {y : ¬c → Except Excno α}
    (hx : ∀ h, ErrReal (x h)) (hy : ∀ h, ErrReal (y h)) : ErrReal (if h : c then x h else y h) := by
  split
  · exact hx _
  · exact hy _

theorem builderStoreRefChecked_real (b : Builder) (c : Cell) : ErrReal (builderStoreRefChecked b c) := by
  intro e h
  unfold builderStoreRefChecked at h
  split at h
  · cases h
  · cases h; decide

theorem builderAppendBuilderChecked_real (b v : Builder) : ErrReal (builderAppendBuilderChecked b v) := by
  intro e h
  unfold builderAppendBuilderChecked at h
  split at h
  · cases h
  · cases h; decide

set_option maxHeartbeats 4000000 in
/-- **The set of the model fails only with an exception of code 2 or more**, if the value it stores
does (by induction on the key's length). -/
theorem dictSetGenAuxWithCells_real (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r)
    (storeVal : Builder → Except Excno Builder) (hs : ∀ b, ErrReal (storeVal b)) (mode : DictSetMode) (k : Nat) :
    ∀ (root : Option Cell) (key : BitString), key.size = k →
      ErrReal (dictSetGenAuxWithCells root key storeVal mode r) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro root key hk
    unfold dictSetGenAuxWithCells
    repeat' (first
      | exact ErrReal.ok _ | exact ErrReal.pure _
      | exact ErrReal.throw (by decide)
      | exact hs _
      | exact ErrDict.real (parseDictLabel_err _ _ r hr)
      | exact ErrDict.real (dictValidateNodeExtLe_err _ _)
      | exact builderStoreBitsChecked_real _ _ | exact builderAppendCellChecked_real _ _
      | exact builderStoreRefChecked_real _ _
      | exact ih _ (by simp only [Array.size_extract]; omega) _ _ rfl
      | (refine ErrReal.bind ?_ (fun _ => ?_)) | (refine ErrReal.dite (fun _ => ?_) (fun _ => ?_))
      | (refine ErrReal.ite ?_ ?_) | split | (dsimp only))

theorem dictSetBuilderWithCells_real {root : Option Cell} {key : BitString} {val : Builder} {mode : DictSetMode}
    {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno}
    (h : dictSetBuilderWithCells root key val mode (fun c => (libraryResolveLoads libs gv c refused).2) = .error e) :
    2 ≤ e.toInt :=
  dictSetGenAuxWithCells_real _ (resolverCellUnd_library _ _ _) _ (fun b => builderAppendBuilderChecked_real b val)
    mode _ root key rfl e h

theorem dictSetSliceWithCells_real {root : Option Cell} {key : BitString} {val : Slice} {mode : DictSetMode}
    {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno}
    (h : dictSetSliceWithCells root key val mode (fun c => (libraryResolveLoads libs gv c refused).2) = .error e) :
    2 ≤ e.toInt :=
  dictSetGenAuxWithCells_real _ (resolverCellUnd_library _ _ _) _
    (fun b => builderAppendCellChecked_real b val.toCellRemaining) mode _ root key rfl e h

theorem dictSetRefWithCells_real {root : Option Cell} {key : BitString} {val : Cell} {mode : DictSetMode}
    {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno}
    (h : dictSetRefWithCells root key val mode (fun c => (libraryResolveLoads libs gv c refused).2) = .error e) :
    2 ≤ e.toInt :=
  dictSetGenAuxWithCells_real _ (resolverCellUnd_library _ _ _) _ (fun b => builderStoreRefChecked_real b val)
    mode _ root key rfl e h

macro_rules
  | `(tactic| steps_err) => `(tactic| first
      | exact dictSetBuilderWithCells_real (by assumption)
      | exact dictSetSliceWithCells_real (by assumption)
      | exact dictSetRefWithCells_real (by assumption))

/-! ## The parts of the handlers -/

theorem Steps.chargeDictSetCreates (newRoot? : Option Cell) (created : Nat) (path : Cell → Array Cell) :
    Steps (VM.chargeDictSetCreates newRoot? created path) (fun _ s s' => s' = s) := by
  unfold VM.chargeDictSetCreates
  simp only [bind_assoc, pure_bind]
  steps_auto

macro_rules
  | `(tactic| steps_keep) => `(tactic| exact Steps.chargeDictSetCreates _ _ _)

/-! ## The relation -/

/-- What a set (mode `mode`) leaves on the stack `s` under its arguments: the new root (null or a
cell), and but for `.set` a flag (any integer: `-1` or `0`). -/
def SetOk : DictSetMode → Stack → Stack → Prop
  | .set, s, s' => s' = s.push .null ∨ ∃ c : Cell, s' = s.push (.cell c)
  | _, s, s' => (∃ f : Int, s' = (s.push .null).push (.int (.num f))) ∨
      (∃ (c : Cell) (f : Int), s' = (s.push (.cell c)).push (.int (.num f)))

/-- `SetOk` of the stack under the four arguments of a set (the value, the key, the dictionary,
the key length). -/
abbrev SetOk4 (mode : DictSetMode) (s s' : Stack) : Prop :=
  ∃ (s0 : Stack) (a b c d : Value), s = (((s0.push a).push b).push c).push d ∧ SetOk mode s0 s'

macro_rules
  | `(tactic| steps_close) => `(tactic| (intros; subst_vars; first
      | exact ⟨_, _, _, _, _, rfl, Or.inl rfl⟩
      | exact ⟨_, _, _, _, _, rfl, Or.inr ⟨_, rfl⟩⟩
      | exact ⟨_, _, _, _, _, rfl, Or.inl ⟨_, rfl⟩⟩
      | exact ⟨_, _, _, _, _, rfl, Or.inr ⟨_, _, rfl⟩⟩))

end TvmLean.Framed

/-! ## `DICT{,I,U}REPLACEB` with its tail named -/

namespace DictTail

open TvmLean

/-- The handler of `DICT{,I,U}REPLACEB` (`execInstrDictDictReplaceB`): the same code. -/
def replaceB (intKey unsigned : Bool) : VM Unit := do
  VM.checkUnderflow 4
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let keyBits? : Option BitString ←
    if intKey then
      let idxVal ← VM.popInt
      match idxVal with
      | .nan => throw .rangeChk
      | .num idx =>
          match dictKeyBits? idx n unsigned with
          | some bs => pure (some bs)
          | none => throw .rangeChk
    else
      let keySlice ← VM.popSlice
      if keySlice.haveBits n then
        pure (some (keySlice.readBits n))
      else
        pure none
  let newVal ← VM.popBuilder
  let keyBits ←
    match keyBits? with
    | some bs => pure bs
    | none => throw .cellUnd
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()
  match dictSetBuilderWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits newVal .replace with
  | .error e =>
      let loaded := dropFirstRootLoad dictCell? (dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictCell? keyBits)
      for c in loaded do
        VM.registerCellLoad c
      throw e
  | .ok (newRoot?, ok, created, loaded) =>
      let loaded := dropFirstRootLoad dictCell? loaded
      for c in loaded do
        VM.registerCellLoad c
      VM.chargeDictSetCreates newRoot? created (dictKeyPath · keyBits)
      match newRoot? with
      | none => VM.push .null
      | some c => VM.push (.cell c)
      VM.pushSmallInt (if ok then -1 else 0)

end DictTail

namespace TvmLean

/-- `DICT{,I,U}REPLACEB` runs as `DictTail.replaceB` (the same code). -/
theorem DictTail.replaceBHandler_eq (intKey unsigned : Bool) (st : VmState) :
    ExceptT.run (execInstr (.dictReplaceB intKey unsigned)) st = ExceptT.run (DictTail.replaceB intKey unsigned) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

end TvmLean

namespace TvmLean.Framed

open TvmLean

/-! ## The handlers, framed -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `DICT{,I,U}SET{,REF}` in mode `.set`. -/
theorem Steps.dictSet_set (intKey unsigned byRef : Bool) :
    Steps (DictTail.dictSet intKey unsigned byRef .set) (fun _ s s' => SetOk4 .set s s') := by
  unfold DictTail.dictSet DictTail.setRef DictTail.setSlice
  simp only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind,
    show (DictSetMode.set == DictSetMode.set) = true from rfl, if_true]
  cases byRef <;> cases intKey <;>
    (try simp only [eq_self_iff_true, Bool.false_eq_true, if_true, if_false]) <;> steps_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `DICT{,I,U}{ADD,REPLACE}{,REF}` (modes `.add`, `.replace`). -/
theorem Steps.dictSet_flag (intKey unsigned byRef : Bool) (mode : DictSetMode) (hm : (mode == .set) = false) :
    Steps (DictTail.dictSet intKey unsigned byRef mode) (fun _ s s' => SetOk4 mode s s') := by
  unfold DictTail.dictSet DictTail.setRef DictTail.setSlice
  simp only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind, hm, Bool.false_eq_true, if_false]
  have hs : SetOk mode = fun s s' => (∃ f : Int, s' = (s.push .null).push (.int (.num f))) ∨
      (∃ (c : Cell) (f : Int), s' = (s.push (.cell c)).push (.int (.num f))) := by
    cases mode <;> first | rfl | (simp at hm)
  simp only [SetOk4, hs]
  cases byRef <;> cases intKey <;>
    (try simp only [eq_self_iff_true, Bool.false_eq_true, if_true, if_false]) <;> steps_auto

/-- **`DICT{,I,U}SET{,REF}` (any mode) on any stack is framed**: the stack under its four arguments
`SetOk mode`. -/
theorem Steps.dictSet (intKey unsigned byRef : Bool) (mode : DictSetMode) :
    Steps (DictTail.dictSet intKey unsigned byRef mode) (fun _ s s' => SetOk4 mode s s') := by
  cases mode with
  | set => exact Steps.dictSet_set intKey unsigned byRef
  | add => exact Steps.dictSet_flag intKey unsigned byRef .add rfl
  | replace => exact Steps.dictSet_flag intKey unsigned byRef .replace rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`DICT{,I,U}SETB` (any mode) on any stack is framed.** -/
theorem Steps.dictSetB (intKey unsigned : Bool) (mode : DictSetMode) :
    Steps (DictTail.dictSetB intKey unsigned mode) (fun _ s s' => SetOk4 mode s s') := by
  unfold DictTail.dictSetB DictTail.setBuilder
  simp only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind]
  cases intKey <;> cases mode <;>
    (try simp only [eq_self_iff_true, Bool.false_eq_true, if_true, if_false]) <;>
    (try simp only [show (DictSetMode.set == DictSetMode.set) = true from rfl,
      show (DictSetMode.add == DictSetMode.set) = false from rfl,
      show (DictSetMode.replace == DictSetMode.set) = false from rfl, if_true, if_false,
      Bool.false_eq_true, eq_self_iff_true]) <;>
    steps_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`DICT{,I,U}REPLACEB` on any stack is framed**, as the mode `.replace`. -/
theorem Steps.replaceB (intKey unsigned : Bool) :
    Steps (DictTail.replaceB intKey unsigned) (fun _ s s' => SetOk4 .replace s s') := by
  unfold DictTail.replaceB
  simp only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind]
  cases intKey <;>
    (try simp only [eq_self_iff_true, Bool.false_eq_true, if_true, if_false]) <;>
    steps_auto

/-- From `SetOk4` of the stack `s a b c d`, `SetOk` of `s`. -/
theorem SetOk4.under {mode : DictSetMode} {s : Stack} {a b c d : Value} {s' : Stack}
    (h : SetOk4 mode ((((s.push a).push b).push c).push d) s') : SetOk mode s s' := by
  obtain ⟨s0, a', b', c', d', e, hok⟩ := h
  obtain ⟨_, e1⟩ := Array.push_eq_push.mp e
  obtain ⟨_, e2⟩ := Array.push_eq_push.mp e1
  obtain ⟨_, e3⟩ := Array.push_eq_push.mp e2
  obtain ⟨_, e4⟩ := Array.push_eq_push.mp e3
  rw [e4]
  exact hok

/-- **A set on any dictionary is framed** (`DICT{,I,U}SET{,REF}`, `...ADD`, `...REPLACE`): from a
stack `s a b c d`, `SetOk mode s`, or an exception of code 2 or more. -/
theorem dictSet_framed (intKey unsigned byRef : Bool) (mode : DictSetMode) (s : Stack) (a b c d : Value)
    (st : VmState) (hs : st.stack = (((s.push a).push b).push c).push d) :
    ExecFramed (.dictSet intKey unsigned byRef mode) (SetOk mode s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.dictSet intKey unsigned byRef mode st
  rw [← DictTail.handler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  have hok := h2 () h
  rw [hs] at hok
  exact hok.under

/-- **A set of a builder on any dictionary is framed** (`DICT{,I,U}SETB` and its `ADD`/`REPLACE`). -/
theorem dictSetB_framed (intKey unsigned : Bool) (mode : DictSetMode) (s : Stack) (a b c d : Value)
    (st : VmState) (hs : st.stack = (((s.push a).push b).push c).push d) :
    ExecFramed (.dictSetB intKey unsigned mode) (SetOk mode s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.dictSetB intKey unsigned mode st
  rw [← DictTail.handlerB_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  have hok := h2 () h
  rw [hs] at hok
  exact hok.under

/-- **`DICT{,I,U}REPLACEB` on any dictionary is framed.** -/
theorem replaceB_framed (intKey unsigned : Bool) (s : Stack) (a b c d : Value)
    (st : VmState) (hs : st.stack = (((s.push a).push b).push c).push d) :
    ExecFramed (.dictReplaceB intKey unsigned) (SetOk .replace s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.replaceB intKey unsigned st
  rw [← DictTail.replaceBHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  have hok := h2 () h
  rw [hs] at hok
  exact hok.under

/-- **A run from a set on any dictionary.** `st` is about to run it (`i`, decoded from `code`, the
code after it `rest`, framed with `SetOk mode` from every state with the stack `s a b c d`:
`dictSet_framed`, `dictSetB_framed`, `replaceB_framed`) on the stack `s a b c d`: if `P` holds of
every result that commits nothing and of every run from the state after it with a stack
`SetOk mode s`, any gas, loaded cells and libraries (`after`), it holds of the run. -/
theorem runWith_dictSet {st : VmState} {code rest : Slice} {s : Stack} {a b c d : Value} {i : Instr}
    {mode : DictSetMode}
    (hx : ∀ st0 : VmState, st0.stack = (((s.push a).push b).push c).push d → ExecFramed i (SetOk mode s) st0)
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (i, k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = (((s.push a).push b).push c).push d)
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hok : ∀ s' g lc ll n, n < fuel → SetOk mode s s' →
      P (VmState.runWith execInstr n (after st rest s' g lc ll))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := SetOk mode s)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom, fun st0 h1 _ => hx st0 (h1.trans hs)⟩
    hr hm P hP fuel hok

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_dict_set_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S` written out)
is about to run a set (`DICT{,I,U}SET{,REF,B}` in any mode, `DICT{,I,U}REPLACEB`) on a dictionary it
does not know: by `Framed.runWith_dictSet`, two goals: `P` of a result that commits nothing, and `P`
of the runs from the state after it with a stack `Framed.SetOk mode s`, any gas, loaded cells and
libraries. -/
elab "vm_dict_set_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_dict_set_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  let iE' ← whnfR iE
  unless iE'.isAppOfArity ``Instr.dictSet 4 || iE'.isAppOfArity ``Instr.dictSetB 3 ||
      iE'.isAppOfArity ``Instr.dictReplaceB 2 do
    throwError "vm_dict_set_any: the instruction is {iE'}"
  let stk ← whnfR (← mkAppM ``VmState.stack #[S])
  let pop (e : Expr) : MetaM (Expr × Expr) := do
    let e ← whnfR e
    unless e.isAppOfArity ``Array.push 3 do throwError "vm_dict_set_any: the stack is not written out"
    return (e.getArg! 1, e.getArg! 2)
  let (s3, d) ← pop stk
  let (s2, c) ← pop s3
  let (s1, b) ← pop s2
  let (s0, a) ← pop s1
  let (hx, mode) ←
    if iE'.isAppOfArity ``Instr.dictSet 4 then
      pure (mkAppN (mkConst ``Framed.dictSet_framed) #[iE'.getArg! 0, iE'.getArg! 1, iE'.getArg! 2,
        iE'.getArg! 3, s0, a, b, c, d], iE'.getArg! 3)
    else if iE'.isAppOfArity ``Instr.dictSetB 3 then
      pure (mkAppN (mkConst ``Framed.dictSetB_framed) #[iE'.getArg! 0, iE'.getArg! 1, iE'.getArg! 2,
        s0, a, b, c, d], iE'.getArg! 2)
    else
      pure (mkAppN (mkConst ``Framed.replaceB_framed) #[iE'.getArg! 0, iE'.getArg! 1, s0, a, b, c, d],
        mkConst ``DictSetMode.replace)
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
  let f ← mkAppOptM ``Framed.runWith_dictSet #[S, none, none, s0, a, b, c, d, iE, mode, hx, hcc, hcp, hbitsNe,
    hverLe, hdecEx, hchain, hc2, hcom, hr, hm, hs, motive]
  let (f1, goals1) ← Exec.applyRest f 1 #[fuel]
  let (pf, goals2) ← Exec.applyRest f1 1 #[]
  let goals := goals1 ++ goals2
  unless ← isDefEq (← inferType pf) t do throwError "vm_dict_set_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

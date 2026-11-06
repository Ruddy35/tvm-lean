import TvmLean.Proofs.Exec.FramedDictSet
import TvmLean.Proofs.Exec.FramedDictNear

/-!
# `DICT{,I,U}GETOPTREF`, `DICT{,I,U}SETGETOPTREF` on any dictionary, framed

The lookup of an optional reference in a dictionary whose cells a run does not know, and the set
(or delete) of one, are framed (`TvmLean.Framed.ExecFramed`, `TvmLean/Proofs/Exec/Framed.lean`):
the instruction changes the stack, the gas, the loaded cells and libraries only; `GETOPTREF` pushes
the cell found or null; `SETGETOPTREF` pushes the new root (null or a cell) and the old value (a
cell or null); each fails only with an exception of code 2 or more.

* `dictLookupSetGenAuxWithCells_real`: the set of the model that also returns the old value fails
  only with cell_und, dict_err or cell_ov (by induction on the key's length);
* `DictTail.getOptRef`, `DictTail.setGetOptRef`: the handlers (TvmLean/Semantics/Exec/Dict/Ext.lean,
  whose helpers are private: `DictTail.ext*` are their copies), the same code
  (`DictTail.getOptRefHandler_eq`, `DictTail.setGetOptRefHandler_eq`);
* `Framed.getOptRef_framed`, `Framed.setGetOptRef_framed`, `Framed.runWith_framed3`,
  `Framed.runWith_framed4`, tactics `vm_dict_getoptref_any`, `vm_dict_setgetoptref_any`.
-/

namespace TvmLean.Framed

open TvmLean

/-! ## Errors of the lookup and of the set -/

/-- The lookup with the VM's resolver: its exception has code 2 or more. -/
theorem dictLookupWithCells_real {root : Option Cell} {key : BitString} {libs : Array Cell} {gv : Nat}
    {refused : Array BitString} {e : Excno}
    (h : dictLookupWithCells root key (fun c => (libraryResolveLoads libs gv c refused).2) = .error e) :
    2 ≤ e.toInt :=
  ErrDict.real (dictLookupWithCells_err root key _ (resolverCellUnd_library _ _ _)) e h

set_option maxHeartbeats 4000000 in
/-- **The set of the model that returns the old value fails only with an exception of code 2 or
more**, if the value it stores does (by induction on the key's length). -/
theorem dictLookupSetGenAuxWithCells_real (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r)
    (storeVal : Builder → Except Excno Builder) (hs : ∀ b, ErrReal (storeVal b)) (mode : DictSetMode) (k : Nat) :
    ∀ (root : Option Cell) (key : BitString), key.size = k →
      ErrReal (dictLookupSetGenAuxWithCells root key storeVal mode r) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro root key hk
    unfold dictLookupSetGenAuxWithCells
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

theorem dictLookupSetRefWithCells_real {root : Option Cell} {key : BitString} {val : Cell} {mode : DictSetMode}
    {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno}
    (h : dictLookupSetRefWithCells root key val mode (fun c => (libraryResolveLoads libs gv c refused).2) = .error e) :
    2 ≤ e.toInt :=
  dictLookupSetGenAuxWithCells_real _ (resolverCellUnd_library _ _ _) _ (fun b => builderStoreRefChecked_real b val)
    mode _ root key rfl e h

macro_rules
  | `(tactic| steps_err) => `(tactic| first
      | exact dictLookupWithCells_real (by assumption)
      | exact dictLookupSetRefWithCells_real (by assumption))

/-! ## The relations -/

/-- What `DICT{,I,U}GETOPTREF` leaves on the stack `s` under its three arguments: the cell found,
or null. -/
def OptRefOk (s s' : Stack) : Prop := s' = s.push .null ∨ ∃ c : Cell, s' = s.push (.cell c)

/-- `OptRefOk` of the stack under the three arguments (the key, the dictionary, the key length). -/
abbrev OptRefOk3 (s s' : Stack) : Prop :=
  ∃ (s0 : Stack) (a b c : Value), s = ((s0.push a).push b).push c ∧ OptRefOk s0 s'

/-- What `DICT{,I,U}SETGETOPTREF` leaves on the stack `s` under its four arguments: the new root
(null or a cell), then the old value (null or a cell). -/
def SetGetOptRefOk (s s' : Stack) : Prop :=
  s' = (s.push .null).push .null ∨ (∃ c : Cell, s' = (s.push .null).push (.cell c)) ∨
    (∃ r : Cell, s' = (s.push (.cell r)).push .null) ∨
    (∃ (r c : Cell), s' = (s.push (.cell r)).push (.cell c))

/-- `SetGetOptRefOk` of the stack under the four arguments (the new value, the key, the
dictionary, the key length). -/
abbrev SetGetOptRefOk4 (s s' : Stack) : Prop :=
  ∃ (s0 : Stack) (a b c d : Value), s = (((s0.push a).push b).push c).push d ∧ SetGetOptRefOk s0 s'

macro_rules
  | `(tactic| steps_close) => `(tactic| (intros; subst_vars; first
      | exact ⟨_, _, _, _, rfl, Or.inl rfl⟩
      | exact ⟨_, _, _, _, rfl, Or.inr ⟨_, rfl⟩⟩
      | exact ⟨_, _, _, _, _, rfl, Or.inl rfl⟩
      | exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inl ⟨_, rfl⟩)⟩
      | exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))⟩
      | exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))⟩))

end TvmLean.Framed

/-! ## The handlers with their private helpers copied -/

namespace DictTail

open TvmLean

/-- `DictExt.pushDictRoot` (private in TvmLean/Semantics/Exec/Dict/Ext.lean): the same code. -/
def extPushDictRoot (c? : Option Cell) : VM Unit := do
  match c? with
  | none => VM.push .null
  | some c => VM.push (.cell c)

/-- `DictExt.consumeCreatedGas`: the same code. -/
def extConsumeCreatedGas (created : Nat) : VM Unit :=
  VM.chargeCellCreates created

/-- `DictExt.registerLoaded`: the same code. -/
def extRegisterLoaded (loaded : Array Cell) : VM Unit := do
  for c in loaded do
    VM.registerCellLoad c

/-- `DictExt.prechargeRootLoad`: the same code. -/
def extPrechargeRootLoad (dictCell? : Option Cell) : VM Unit := do
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()

/-- `DictExt.loadedWithoutRoot`: the same code. -/
def extLoadedWithoutRoot (dictCell? : Option Cell) (loaded : Array Cell) : Array Cell :=
  match dictCell? with
  | none => loaded
  | some root => loaded.filter (fun c => c != root)

/-- `DictExt.extractRefOrThrow`: the same code. -/
def extExtractRefOrThrow (valueSlice : Slice) : VM Cell := do
  if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
    return valueSlice.cell.refs[valueSlice.refPos]!
  else
    throw .dictErr

/-- The handler of `DICT{,I,U}GETOPTREF` (`execInstrDictExt`): the same code. -/
def getOptRef (intKey unsigned : Bool) : VM Unit := do
  VM.checkUnderflow 3
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let keyBits? : Option BitString ←
    if intKey then
      let idx ← VM.popIntFinite
      pure (dictKeyBits? idx n unsigned)
    else
      let keySlice ← VM.popSlice
      if keySlice.haveBits n then
        pure (some (keySlice.readBits n))
      else
        throw .cellUnd
  match keyBits? with
  | none =>
      VM.push .null
  | some keyBits =>
      extPrechargeRootLoad dictCell?
      match dictLookupWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits with
      | .error e =>
          let loaded := extLoadedWithoutRoot dictCell? (dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictCell? keyBits)
          extRegisterLoaded loaded
          throw e
      | .ok (none, loaded) =>
          let loaded := extLoadedWithoutRoot dictCell? loaded
          extRegisterLoaded loaded
          VM.push .null
      | .ok (some valueSlice, loaded) =>
          let loaded := extLoadedWithoutRoot dictCell? loaded
          extRegisterLoaded loaded
          let c ← extExtractRefOrThrow valueSlice
          VM.push (.cell c)

/-- The handler of `DICT{,I,U}SETGETOPTREF` (`execInstrDictExt`): the same code. -/
def setGetOptRef (intKey unsigned : Bool) : VM Unit := do
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
  let newValue? ← VM.popMaybeCell
  let keyBits : BitString ←
    match keyBits? with
    | some bs => pure bs
    | none => throw .cellUnd
  match newValue? with
  | some newValue =>
      extPrechargeRootLoad dictCell?
      match dictLookupSetRefWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits newValue .set with
      | .error e =>
          let loaded := extLoadedWithoutRoot dictCell? (dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictCell? keyBits)
          extRegisterLoaded loaded
          throw e
      | .ok (oldVal?, newRoot?, _ok, created, loaded) =>
          let loaded := extLoadedWithoutRoot dictCell? loaded
          extRegisterLoaded loaded
          VM.chargeDictSetCreates newRoot? created (dictKeyPath · keyBits)
          extPushDictRoot newRoot?
          match oldVal? with
          | none => VM.push .null
          | some oldVal =>
              let c ← extExtractRefOrThrow oldVal
              VM.push (.cell c)
  | none =>
      extPrechargeRootLoad dictCell?
      match dictDeleteWithLoads (resolve := (← VM.cellResolver)) dictCell? keyBits with
      | .error (e, loaded0) =>
          extRegisterLoaded (extLoadedWithoutRoot dictCell? loaded0)
          throw e
      | .ok (oldVal?, newRoot?, created, loaded) =>
          let loaded := extLoadedWithoutRoot dictCell? loaded
          extRegisterLoaded loaded
          extConsumeCreatedGas created
          extPushDictRoot newRoot?
          match oldVal? with
          | none => VM.push .null
          | some oldVal =>
              let c ← extExtractRefOrThrow oldVal
              VM.push (.cell c)

end DictTail

namespace TvmLean

set_option maxHeartbeats 1000000 in
/-- `DICT{,I,U}GETOPTREF` runs as `DictTail.getOptRef` (the same code). -/
theorem DictTail.getOptRefHandler_eq (intKey unsigned : Bool) (st : VmState) :
    ExceptT.run (execInstr (.dictExt (.getOptRef intKey unsigned))) st =
      ExceptT.run (DictTail.getOptRef intKey unsigned) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

set_option maxHeartbeats 1000000 in
/-- `DICT{,I,U}SETGETOPTREF` runs as `DictTail.setGetOptRef` (the same code). -/
theorem DictTail.setGetOptRefHandler_eq (intKey unsigned : Bool) (st : VmState) :
    ExceptT.run (execInstr (.dictExt (.setGetOptRef intKey unsigned))) st =
      ExceptT.run (DictTail.setGetOptRef intKey unsigned) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

end TvmLean

namespace TvmLean.Framed

open TvmLean

/-! ## The helpers, framed -/

theorem Steps.extRegisterLoaded (loaded : Array Cell) :
    Steps (DictTail.extRegisterLoaded loaded) (fun _ s s' => s' = s) := by
  unfold DictTail.extRegisterLoaded
  first
    | exact Steps.forLoads loaded
    | exact Steps.keep_bind (Steps.forLoads loaded) (fun _ => Steps.mono (Steps.pure _) (fun _ _ _ h => h.2))

theorem Steps.extPrechargeRootLoad (dictCell? : Option Cell) :
    Steps (DictTail.extPrechargeRootLoad dictCell?) (fun _ s s' => s' = s) := by
  unfold DictTail.extPrechargeRootLoad
  split
  · exact Steps.registerCellLoad _
  · exact Steps.mono (Steps.pure _) (fun _ _ _ h => h.2)

theorem Steps.extConsumeCreatedGas (created : Nat) :
    Steps (DictTail.extConsumeCreatedGas created) (fun _ s s' => s' = s) := by
  unfold DictTail.extConsumeCreatedGas
  exact Steps.chargeCellCreates _

macro_rules
  | `(tactic| steps_keep) => `(tactic| first
      | exact Steps.extRegisterLoaded _ | exact Steps.extPrechargeRootLoad _
      | exact Steps.extConsumeCreatedGas _)

/-! ## The handlers, framed -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`DICT{,I,U}GETOPTREF` on any stack is framed**: the stack under its three arguments
`OptRefOk`. -/
theorem Steps.getOptRef (intKey unsigned : Bool) :
    Steps (DictTail.getOptRef intKey unsigned) (fun _ s s' => OptRefOk3 s s') := by
  unfold DictTail.getOptRef DictTail.extExtractRefOrThrow
  simp only [VM.cellResolver, bind_assoc, pure_bind]
  cases intKey <;> (try simp only [Bool.false_eq_true, if_true, if_false]) <;> steps_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`DICT{,I,U}SETGETOPTREF` on any stack is framed**: the stack under its four arguments
`SetGetOptRefOk`. -/
theorem Steps.setGetOptRef (intKey unsigned : Bool) :
    Steps (DictTail.setGetOptRef intKey unsigned) (fun _ s s' => SetGetOptRefOk4 s s') := by
  unfold DictTail.setGetOptRef DictTail.extExtractRefOrThrow DictTail.extPushDictRoot
  simp only [VM.cellResolver, bind_assoc, pure_bind]
  cases intKey <;> (try simp only [Bool.false_eq_true, if_true, if_false]) <;> steps_auto

theorem OptRefOk3.under {s : Stack} {a b c : Value} {s' : Stack}
    (h : OptRefOk3 (((s.push a).push b).push c) s') : OptRefOk s s' := by
  obtain ⟨s0, a', b', c', e, hok⟩ := h
  obtain ⟨_, e1⟩ := Array.push_eq_push.mp e
  obtain ⟨_, e2⟩ := Array.push_eq_push.mp e1
  obtain ⟨_, e3⟩ := Array.push_eq_push.mp e2
  rw [e3]
  exact hok

theorem SetGetOptRefOk4.under {s : Stack} {a b c d : Value} {s' : Stack}
    (h : SetGetOptRefOk4 ((((s.push a).push b).push c).push d) s') : SetGetOptRefOk s s' := by
  obtain ⟨s0, a', b', c', d', e, hok⟩ := h
  obtain ⟨_, e1⟩ := Array.push_eq_push.mp e
  obtain ⟨_, e2⟩ := Array.push_eq_push.mp e1
  obtain ⟨_, e3⟩ := Array.push_eq_push.mp e2
  obtain ⟨_, e4⟩ := Array.push_eq_push.mp e3
  rw [e4]
  exact hok

/-- **`DICT{,I,U}GETOPTREF` on any dictionary is framed**: from a stack `s a b c`, `OptRefOk s`, or
an exception of code 2 or more. -/
theorem getOptRef_framed (intKey unsigned : Bool) (s : Stack) (a b c : Value)
    (st : VmState) (hs : st.stack = ((s.push a).push b).push c) :
    ExecFramed (.dictExt (.getOptRef intKey unsigned)) (OptRefOk s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.getOptRef intKey unsigned st
  rw [← DictTail.getOptRefHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  have hok := h2 () h
  rw [hs] at hok
  exact hok.under

/-- **`DICT{,I,U}SETGETOPTREF` on any dictionary is framed**: from a stack `s a b c d`,
`SetGetOptRefOk s`, or an exception of code 2 or more. -/
theorem setGetOptRef_framed (intKey unsigned : Bool) (s : Stack) (a b c d : Value)
    (st : VmState) (hs : st.stack = (((s.push a).push b).push c).push d) :
    ExecFramed (.dictExt (.setGetOptRef intKey unsigned)) (SetGetOptRefOk s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.setGetOptRef intKey unsigned st
  rw [← DictTail.setGetOptRefHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  have hok := h2 () h
  rw [hs] at hok
  exact hok.under

/-- **A run from a framed instruction on a stack of three entries.** `st` is about to run `i`
(decoded from `code`, the code after it `rest`, framed with `Ok` from every state with the stack
`s a b c`) on the stack `s a b c`: if `P` holds of every result that commits nothing and of every
run from the state after it with a stack `Ok`, any gas, loaded cells and libraries (`after`), it
holds of the run. -/
theorem runWith_framed3 {st : VmState} {code rest : Slice} {s : Stack} {a b c : Value} {i : Instr}
    {Ok : Stack → Prop}
    (hx : ∀ st0 : VmState, st0.stack = ((s.push a).push b).push c → ExecFramed i Ok st0)
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (i, k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = ((s.push a).push b).push c)
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hok : ∀ s' g lc ll n, n < fuel → Ok s' →
      P (VmState.runWith execInstr n (after st rest s' g lc ll))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := Ok)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom, fun st0 h1 _ => hx st0 (h1.trans hs)⟩
    hr hm P hP fuel hok

/-- **A run from a framed instruction on a stack of four entries** (as `runWith_framed3`). -/
theorem runWith_framed4 {st : VmState} {code rest : Slice} {s : Stack} {a b c d : Value} {i : Instr}
    {Ok : Stack → Prop}
    (hx : ∀ st0 : VmState, st0.stack = (((s.push a).push b).push c).push d → ExecFramed i Ok st0)
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (i, k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = (((s.push a).push b).push c).push d)
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hok : ∀ s' g lc ll n, n < fuel → Ok s' →
      P (VmState.runWith execInstr n (after st rest s' g lc ll))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := Ok)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom, fun st0 h1 _ => hx st0 (h1.trans hs)⟩
    hr hm P hP fuel hok

end TvmLean.Framed

namespace TvmLean.Exec

open Lean Meta Elab Tactic

/-- The run in the goal (`P (VmState.runWith execInstr fuel S)`, `S` written out) about to run an
instruction `.dictExt op` (`op` built by `ctor` from `nargs` arguments, which `argsOk` accepts)
framed by `framedThm` (applied to those arguments unless `passArgs` is false, the stack `s` and its
top `k` entries) on a stack of `k` (3 or 4) entries: by `Framed.runWith_framed3` or
`Framed.runWith_framed4`, two goals: `P` of a result that commits nothing, and `P` of the runs from
the state after it with a stack `Ok`. `what` names the tactic in its errors. -/
def framedAny (what : String) (k : Nat) (ctor : Name) (nargs : Nat) (framedThm : Name)
    (argsOk : Array Expr → MetaM Bool := fun _ => pure true) (passArgs : Bool := true) :
    TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "{what}: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← framedFacts S
  let iE' ← whnfR iE
  unless iE'.isAppOfArity ``Instr.dictExt 1 do throwError "{what}: the instruction is {iE'}"
  let op ← whnfR iE'.appArg!
  unless op.isAppOfArity ctor nargs do throwError "{what}: the instruction is {iE'}"
  let args := op.getAppArgs
  unless ← argsOk args do throwError "{what}: the instruction is {iE'}"
  let pop (e : Expr) : MetaM (Expr × Expr) := do
    let e ← whnfR e
    unless e.isAppOfArity ``Array.push 3 do throwError "{what}: the stack is not written out"
    return (e.getArg! 1, e.getArg! 2)
  let mut stk ← whnfR (← mkAppM ``VmState.stack #[S])
  let mut top : Array Expr := #[]
  for _ in [0:k] do
    let (s', v) ← pop stk
    top := #[v] ++ top
    stk := s'
  let hx := mkAppN (mkConst framedThm) ((if passArgs then args else #[]) ++ #[stk] ++ top)
  let motive ← withLocalDeclD `r (mkConst ``StepResult) fun rv => do
    mkLambdaFVars #[rv] ((← kabstract t r).instantiate1 rv)
  let refl (e : Expr) : MetaM Expr := mkEqRefl e
  let hcc ← refl (← mkAppM ``VmState.cc #[S])
  let hcp ← refl (← mkAppM ``VmState.cp #[S])
  let hchain ← decideProof (← mkAppM ``LT.lt #[← whnfCore (← whnfR (← mkAppM ``VmState.chainJumps #[S])),
    mkConst ``freeNestedContJump])
  let hc2 ← refl (← mkAppM ``Regs.c2 #[← mkAppM ``VmState.regs #[S]])
  let hcom ← refl (← mkAppM ``CommittedState.committed #[← mkAppM ``VmState.cstate #[S]])
  let hr ← refl (← mkAppM ``VmState.librariesRefused #[S])
  let hm ← refl (← mkAppM ``VmState.librariesMissed #[S])
  let hs ← refl (← mkAppM ``VmState.stack #[S])
  let runThm := if k = 3 then ``Framed.runWith_framed3 else ``Framed.runWith_framed4
  let f ← mkAppOptM runThm (#[some S, none, none, some stk] ++ top.map some ++
    #[some iE, none, some hx, some hcc, some hcp, some hbitsNe, some hverLe, some hdecEx, some hchain, some hc2,
      some hcom, some hr, some hm, some hs, some motive])
  let (f1, goals1) ← applyRest f 1 #[fuel]
  let (pf, goals2) ← applyRest f1 1 #[]
  let goals := goals1 ++ goals2
  unless ← isDefEq (← inferType pf) t do throwError "{what}: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean.Exec

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_dict_getoptref_any`: the run in the goal is about to run `DICT{,I,U}GETOPTREF` on a
dictionary it does not know: by `Framed.runWith_framed3` and `Framed.getOptRef_framed`, two goals:
`P` of a result that commits nothing, and `P` of the runs from the state after it with a stack
`Framed.OptRefOk s`, any gas, loaded cells and libraries. -/
elab "vm_dict_getoptref_any" : tactic =>
  Exec.framedAny "vm_dict_getoptref_any" 3 ``DictExtInstr.getOptRef 2 ``Framed.getOptRef_framed

open Lean Meta Elab Tactic in
/-- `vm_dict_setgetoptref_any`: the run in the goal is about to run `DICT{,I,U}SETGETOPTREF` on a
dictionary it does not know: by `Framed.runWith_framed4` and `Framed.setGetOptRef_framed`, two goals:
`P` of a result that commits nothing, and `P` of the runs from the state after it with a stack
`Framed.SetGetOptRefOk s`, any gas, loaded cells and libraries. -/
elab "vm_dict_setgetoptref_any" : tactic =>
  Exec.framedAny "vm_dict_setgetoptref_any" 4 ``DictExtInstr.setGetOptRef 2 ``Framed.setGetOptRef_framed

end TvmLean

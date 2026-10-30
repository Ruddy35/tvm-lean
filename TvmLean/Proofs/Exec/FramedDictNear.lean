import TvmLean.Proofs.Exec.FramedDictMinMax

/-!
# `DICT{,I,U}GET{NEXT,PREV}{,EQ}` on any dictionary, framed

The key next to (or before) a hint in a dictionary whose cells a run does not know is framed
(`TvmLean.Framed.ExecFramed`): the instruction changes the stack, the gas, the loaded cells and
libraries only; it pushes the value (a slice), the key (an integer for the `I`/`U` forms, a slice
else) and `-1`, or `0`; it fails only with an exception of code 2 or more.

* `dictNearestWithCells_err`: the walk to the nearest key fails only with cell_und or dict_err;
* `DictTail.near`: the handler (TvmLean/Semantics/Exec/Dict/DictGetNear.lean), the same code
  (`DictTail.nearHandler_eq`);
* `Framed.near_framed`, `Framed.runWith_near`, tactic `vm_dict_near_any`.
-/

namespace TvmLean.Framed

open TvmLean

/-- The walk to the nearest key below a node fails only with cell_und or dict_err. -/
theorem dictNearestAuxWithCells_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) (n : Nat) :
    ∀ (cell : Cell) (hint : BitString) (pos : Nat) (allowEq firstBit restBit : Bool),
      ErrDict (dictNearestAuxWithCells cell hint n pos allowEq firstBit restBit r) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro cell hint pos allowEq firstBit restBit
    rw [dictNearestAuxWithCells]
    refine ErrDict.bind (parseDictLabel_err _ _ r hr) (fun lbl => ?_)
    refine ErrDict.bind (dictValidateNodeExtLe_err _ _) (fun x => ?_)
    obtain ⟨rem0, hle⟩ := x
    dsimp only
    repeat' (first
      | exact ErrDict.ok _ | exact ErrDict.pure _ | exact ErrDict.throwDictErr
      | exact dictMinMaxAuxWithCells_err r hr _ _ _ _ _
      | exact ih _ (by omega) _ _ _ _ _ _
      | (refine ErrDict.bind ?_ (fun _ => ?_)) | (refine ErrDict.dite (fun _ => ?_) (fun _ => ?_))
      | (refine ErrDict.ite ?_ ?_) | split | (dsimp only))

/-- **The walk to the nearest key fails only with cell_und or dict_err.** -/
theorem dictNearestWithCells_err (root : Option Cell) (hint : BitString) (fetchNext allowEq invertFirst : Bool)
    (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) :
    ErrDict (dictNearestWithCells root hint fetchNext allowEq invertFirst r) := by
  unfold dictNearestWithCells
  split
  · exact ErrDict.pure _
  · exact dictNearestAuxWithCells_err r hr _ _ _ _ _ _ _

theorem dictNearestWithCells_real {root : Option Cell} {hint : BitString} {fetchNext allowEq invertFirst : Bool}
    {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno}
    (h : dictNearestWithCells root hint fetchNext allowEq invertFirst
      (fun c => (libraryResolveLoads libs gv c refused).2) = .error e) : 2 ≤ e.toInt :=
  ErrDict.real (dictNearestWithCells_err _ _ _ _ _ _ (resolverCellUnd_library _ _ _)) e h

macro_rules
  | `(tactic| steps_err) => `(tactic| exact dictNearestWithCells_real (by assumption))

theorem Steps.popIntFinite : Steps VM.popIntFinite (fun _ s s' => ∃ v, s = s'.push v) := by
  unfold VM.popIntFinite
  refine Steps.mono (Steps.bind Steps.popInt (fun v => (?_ : Steps _ (fun _ s s' => s' = s)))) ?_
  · split
    · exact Steps.throw _ (by decide) _
    · exact Steps.mono (Steps.pure _) (fun _ s s' h => h.2)
  · rintro _ s s'' ⟨i, s1, h1, h2⟩
    exact ⟨.int i, by rw [h1, h2]⟩

macro_rules
  | `(tactic| steps_pop) => `(tactic| exact Steps.popIntFinite)

/-- What `DICT*GETNEXT`/`PREV` (`intKey` of its opcode) leave on the stack `s` under its three
arguments: the value, the key (an integer for the `I`/`U` forms, a slice else) and `-1`, or `0`. -/
def NearOk : Bool → Stack → Stack → Prop
  | true, s, s' =>
      (∃ (v : Slice) (k : Int), s' = ((s.push (.slice v)).push (.int (.num k))).push (.int (.num (-1)))) ∨
      s' = s.push (.int (.num 0))
  | false, s, s' =>
      (∃ (v : Slice) (k : Slice), s' = ((s.push (.slice v)).push (.slice k)).push (.int (.num (-1)))) ∨
      s' = s.push (.int (.num 0))

/-- `NearOk` of the stack under the three arguments (the key hint, the dictionary, the length). -/
abbrev NearOk3 (intKey : Bool) (s s' : Stack) : Prop :=
  ∃ (s0 : Stack) (a b c : Value), s = ((s0.push a).push b).push c ∧ NearOk intKey s0 s'

macro_rules
  | `(tactic| steps_close) => `(tactic| (intros; subst_vars; first
      | exact ⟨_, _, _, _, rfl, Or.inl ⟨_, _, rfl⟩⟩
      | exact ⟨_, _, _, _, rfl, Or.inr rfl⟩))

end TvmLean.Framed

/-! ## The handler -/

namespace DictTail

open TvmLean

/-- The handler of `DICT*GETNEXT`/`PREV` (`execInstrDictDictGetNear`): the same code. -/
def near (args4 : Nat) : VM Unit := do
  VM.checkUnderflow 3
  let allowEq : Bool := (args4 &&& 1) = 1
  let goUp : Bool := (args4 &&& 2) = 0
  let intKey : Bool := (args4 &&& 8) = 8
  let unsigned : Bool := intKey && ((args4 &&& 4) = 4)
  let sgnd : Bool := intKey && !unsigned
  let maxN : Nat := if intKey then (if unsigned then 256 else 257) else 1023
  let n ← VM.popNatUpTo maxN
  let dictCell? ← VM.popMaybeCell
  if intKey then
    let key ← VM.popIntFinite
    let (out?, loaded0) ←
      match dictKeyBits? key n unsigned with
      | some hintBits =>
          match dictCell? with
          | some c => VM.registerCellLoad c
          | none => pure ()
          match dictNearestWithCells (resolve := (← VM.cellResolver)) dictCell? hintBits goUp allowEq sgnd with
          | .error e =>
              let loaded := dropFirstRootLoad dictCell? (dictNearestVisitedCells (resolve := (← VM.cellResolver)) dictCell? hintBits goUp allowEq sgnd)
              for c in loaded do
                VM.registerCellLoad c
              throw e
          | .ok r => pure r
      | none =>
          let cond : Bool := (decide (0 ≤ key)) != goUp
          if cond then
            match dictCell? with
            | some c => VM.registerCellLoad c
            | none => pure ()
            match dictMinMaxWithCells (resolve := (← VM.cellResolver)) dictCell? n (!goUp) sgnd with
            | .error e =>
                let loaded := dropFirstRootLoad dictCell? (dictMinMaxVisitedCells (resolve := (← VM.cellResolver)) dictCell? n (!goUp) sgnd)
                for c in loaded do
                  VM.registerCellLoad c
                throw e
            | .ok r => pure r
          else
            pure (none, #[])

    for c in dropFirstRootLoad dictCell? loaded0 do
      VM.registerCellLoad c

    match out? with
    | none =>
        VM.pushSmallInt 0
    | some (val, keyBits) =>
        VM.push (.slice val)
        let keyOut : Int :=
          if sgnd then
            bitsToIntSignedTwos keyBits
          else
            Int.ofNat (bitsToNat keyBits)
        VM.pushIntQuiet (.num keyOut) false
        VM.pushSmallInt (-1)
  else
    let keyHint ← VM.popSlice
    if !keyHint.haveBits n then
      throw .cellUnd
    let hintBits : BitString := keyHint.readBits n
    match dictCell? with
    | some c => VM.registerCellLoad c
    | none => pure ()
    match dictNearestWithCells (resolve := (← VM.cellResolver)) dictCell? hintBits goUp allowEq false with
    | .error e =>
        let loaded := dropFirstRootLoad dictCell? (dictNearestVisitedCells (resolve := (← VM.cellResolver)) dictCell? hintBits goUp allowEq false)
        for c in loaded do
          VM.registerCellLoad c
        throw e
    | .ok (none, loaded) =>
        for c in dropFirstRootLoad dictCell? loaded do
          VM.registerCellLoad c
        VM.pushSmallInt 0
    | .ok (some (val, keyBits), loaded) =>
        for c in dropFirstRootLoad dictCell? loaded do
          VM.registerCellLoad c
        VM.push (.slice val)
        modify fun st => st.consumeGas cellCreateGasPrice
        let keyCell : Cell := Cell.mkOrdinary keyBits #[]
        VM.push (.slice (Slice.ofCell keyCell))
        VM.pushSmallInt (-1)

end DictTail

namespace TvmLean

/-- `DICT*GETNEXT`/`PREV` runs as `DictTail.near` (the same code). -/
theorem DictTail.nearHandler_eq (args4 : Nat) (st : VmState) :
    ExceptT.run (execInstr (.dictGetNear args4)) st = ExceptT.run (DictTail.near args4) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

end TvmLean

namespace TvmLean.Framed

open TvmLean

/-- The gas of a key cell, charged without a check (`modify`): framed, the stack kept. -/
theorem Steps.modifyConsumeGas (amount : Int) :
    Steps (modify fun st : VmState => st.consumeGas amount : VM PUnit) (fun _ s s' => s' = s) := by
  intro st
  rw [VM.run_modify]
  refine ⟨rfl, fun _ _ => rfl, ?_, fun _ => rfl⟩
  intro e h; cases h

macro_rules
  | `(tactic| steps_keep) => `(tactic| exact Steps.modifyConsumeGas _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`DICT*GETNEXT`/`PREV` on any stack is framed**, with `NearOk3` of its key form. -/
theorem Steps.near (args4 : Nat) :
    Steps (DictTail.near args4) (fun _ s s' => NearOk3 (decide ((args4 &&& 8) = 8)) s s') := by
  unfold DictTail.near
  simp only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind]
  generalize decide ((args4 &&& 8) = 8) = intKey
  cases intKey <;> (try simp only [eq_self_iff_true, Bool.false_eq_true, if_true, if_false]) <;> steps_auto

/-- From `NearOk3` of the stack `s a b c`, `NearOk` of `s`. -/
theorem NearOk3.under {intKey : Bool} {s : Stack} {a b c : Value} {s' : Stack}
    (h : NearOk3 intKey (((s.push a).push b).push c) s') : NearOk intKey s s' := by
  obtain ⟨s0, a', b', c', e, hok⟩ := h
  obtain ⟨_, e1⟩ := Array.push_eq_push.mp e
  obtain ⟨_, e2⟩ := Array.push_eq_push.mp e1
  obtain ⟨_, e3⟩ := Array.push_eq_push.mp e2
  rw [e3]
  exact hok

/-- **`DICT*GETNEXT`/`PREV` on any dictionary is framed**: from a stack `s a b c`, `NearOk intKey s`
(`intKey` the bit 8 of the opcode), or an exception of code 2 or more. -/
theorem near_framed (args4 : Nat) (intKey : Bool) (hik : decide ((args4 &&& 8) = 8) = intKey) (s : Stack)
    (a b c : Value) (st : VmState) (hs : st.stack = ((s.push a).push b).push c) :
    ExecFramed (.dictGetNear args4) (NearOk intKey s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.near args4 st
  rw [← DictTail.nearHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  have hok := h2 () h
  rw [hs, hik] at hok
  exact hok.under

/-- **A run from `DICT*GETNEXT`/`PREV` on any dictionary** (`runWith_minMax` for the nearest key). -/
theorem runWith_near {st : VmState} {code rest : Slice} {s : Stack} {a b c : Value} {args4 : Nat}
    {intKey : Bool} (hik : decide ((args4 &&& 8) = 8) = intKey)
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (.dictGetNear args4, k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = ((s.push a).push b).push c)
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hok : ∀ s' g lc ll n, n < fuel → NearOk intKey s s' →
      P (VmState.runWith execInstr n (after st rest s' g lc ll))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := NearOk intKey s)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom,
      fun st0 h1 _ => near_framed args4 intKey hik s a b c st0 (h1.trans hs)⟩
    hr hm P hP fuel hok

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_dict_near_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S` written
out) is about to run `DICT*GETNEXT`/`PREV` (any form) on a dictionary it does not know: by
`Framed.runWith_near`, two goals: `P` of a result that commits nothing, and `P` of the runs from the
state after it with a stack `Framed.NearOk intKey s`, any gas, loaded cells and libraries. -/
elab "vm_dict_near_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_dict_near_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  let iE ← whnfR iE
  unless iE.isAppOfArity ``Instr.dictGetNear 1 do throwError "vm_dict_near_any: the instruction is {iE}"
  let some args4 ← (evalNat (← instantiateMVars iE.appArg!)).run
    | throwError "vm_dict_near_any: the opcode's flags are not a numeral"
  let stk ← whnfR (← mkAppM ``VmState.stack #[S])
  let pop (e : Expr) : MetaM (Expr × Expr) := do
    let e ← whnfR e
    unless e.isAppOfArity ``Array.push 3 do throwError "vm_dict_near_any: the stack is not written out"
    return (e.getArg! 1, e.getArg! 2)
  let (s2, c) ← pop stk
  let (s1, b) ← pop s2
  let (s0, a) ← pop s1
  let intKey := if args4 &&& 8 == 8 then mkConst ``Bool.true else mkConst ``Bool.false
  let hik ← mkEqRefl intKey
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
  let f ← mkAppOptM ``Framed.runWith_near #[S, none, none, s0, a, b, c, iE.appArg!, intKey, hik, hcc, hcp,
    hbitsNe, hverLe, hdecEx, hchain, hc2, hcom, hr, hm, hs, motive]
  let (f1, goals1) ← Exec.applyRest f 1 #[fuel]
  let (pf, goals2) ← Exec.applyRest f1 1 #[]
  let goals := goals1 ++ goals2
  unless ← isDefEq (← inferType pf) t do throwError "vm_dict_near_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

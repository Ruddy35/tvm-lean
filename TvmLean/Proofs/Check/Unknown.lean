import TvmLean.Proofs.Tx.NoSetCode
import TvmLean.Proofs.Exec.Havoc
import TvmLean.Proofs.Exec.Dict.Near
import TvmLean.Proofs.Exec.Spec.DictSetGet
import TvmLean.Proofs.Exec.Spec.Ctr
import TvmLean.Proofs.Exec.Spec.FlowRef
import TvmLean.Proofs.Exec.Spec.DictLoad
import TvmLean.Proofs.Contracts.Wallet3Run.Common

/-!
# What a symbolic run knows of what it cannot see

The tactics and simp procedures `ran_case` (TvmLean/Proofs/Check/Tactic.lean) uses where the code
meets values it does not know:

* loads of cells: `havocLoads`, `havocCellLoads` name them (`Havoc.loads`, `Havoc.cellLoads`,
  TvmLean/Proofs/Exec/Havoc.lean) and `check_havoc` replaces them by their possible outcomes, the gas
  and the loaded cells after them new variables: the loads of unknown cells (of a message, of a
  dictionary), and those of the code, whose gas followed load by load is a term that grows with each
  (the kernel's check of a `CALLDICT` into a procedure took minutes); with `max_library_loads`, the
  step's reruns with libraries refused (`check_step_finish`, `stepFinish_cases`), each step run once;
* exceptions the run does not know (the error of a walk of an unknown dictionary): their number
  `Excno.toInt e` kept as it is (`excnoToIntStop`, a simp procedure run before `Excno.toInt` would
  be unfolded into a case per exception), with its range `0..15` for `omega` (`excnoBounds`), and the
  registers after the jump that ends the run (`countJump_regs`, `countJump_cstate`);
* loops: `check_loop`, the loop rule (`runWith_invLe`: the fuel bounded, so that a loop inside a
  loop keeps the outer loop's hypothesis) with the loaded libraries among the parts an iteration
  changes, the count of a `REPEAT` loop, and fewer stack entries than asked at the head of a `*BRK`
  loop;
* stacks, arrays and ranges written out: `stackChainExtract` (`Array.extract` of a stack: what calls
  and `BLKDROP2` keep), `arrayLitExtract`, `arrayLitGetElem` (literal bits of a data cell after its
  fields), `listRangeLit` (`for i in [0:k]` loops of the model);
* dictionaries: the walks of the empty dictionary (`nearestWalk_none`, `minMaxWalk_none`,
  `deleteWalk_none`: a dictionary an invariant allows to be `null`), and `check_dict_facts`, what
  the map of a dictionary says of a walk the run split on
  (TvmLean/Proofs/Exec/Dict/Near.lean), in `Dict.value` on a dictionary an invariant says is
  well-formed, and deletes with the VM's resolver as with the default one;
* calls and jumps with arguments (`callArgsUnfold`: `CALLXARGS`, `JMPXARGS`, `RETARGS`), and
  `cdata_callFrame_identity`: the return continuation of a call without arguments.
-/

namespace TvmLean.Check

open Lean Meta Elab Tactic

/-! ## Loads of unknown cells, and the steps they may repeat -/

/-- Whether `e` is a list written out (`[]`, `a :: l` with `l` written out). -/
def isListLit : Expr → Nat → Bool
  | _, 0 => false
  | e, n + 1 =>
    if e.isAppOfArity ``List.nil 1 then true
    else if e.isAppOfArity ``List.cons 3 then isListLit e.appArg! n
    else false

/-- The loads of cells (`VM.registerCellLoadList` of a list not empty, `VM.registerCellLoad`: the
nodes of a dictionary of a message, the cells of the code), named `Havoc.loads` (`Havoc.loads_eq`,
`Havoc.load_eq`), which `check_havoc` replaces by what is known of them. -/
simproc ↓ havocLoads (@ExceptT.run Excno (StateM VmState) _ _ _) := fun e => do
  let_expr ExceptT.run _ _ _ m st := e | return .continue
  if m.isAppOfArity ``VM.registerCellLoadList 1 then
    let cells ← instantiateMVars m.appArg!
    if cells.isAppOfArity ``List.nil 1 then return .continue
    let pf ← mkAppM ``Havoc.loads_eq #[cells, st]
    return .done { expr := ← mkAppM ``Havoc.loads #[cells, st], proof? := pf }
  if m.isAppOfArity ``VM.registerCellLoad 1 then
    let c ← instantiateMVars m.appArg!
    let pf ← mkAppM ``Havoc.load_eq #[c, st]
    let cells ← mkListLit (mkConst ``Cell) [c]
    return .done { expr := ← mkAppM ``Havoc.loads #[cells, st], proof? := pf }
  return .continue

/-- The rest of a run after loads of unknown cells (`VM.bindRes (Havoc.loads cells st) f`) is
left as it is until `check_havoc` gives the loads' outcomes: simplifying `f` for a state not known
yet (an exception's handler, the rest of the instruction under a binder) is work the run redoes
after the case split. -/
simproc ↓ havocStop (VM.bindRes (Havoc.loads _ _) _) := fun e => do
  return .done { expr := e }

/-- `havocLoads` for the actions themselves, wherever they are (inside a `do` block the run has
not split yet): `Havoc.loadsM`, whose run `Havoc.run_loadsM` gives as `Havoc.loads`. -/
simproc ↓ havocLoadsM (VM.registerCellLoad _) := fun e => do
  let_expr VM.registerCellLoad c := e | return .continue
  let c ← instantiateMVars c
  let cells ← mkListLit (mkConst ``Cell) [c]
  return .done { expr := ← mkAppM ``Havoc.loadsM #[cells], proof? := ← mkAppM ``Havoc.loadM_eq #[c] }

/-- `havocLoadsM` for `VM.registerCellLoadList` of a list not empty. -/
simproc ↓ havocLoadListM (VM.registerCellLoadList _) := fun e => do
  let_expr VM.registerCellLoadList cells := e | return .continue
  let cells ← instantiateMVars cells
  if cells.isAppOfArity ``List.nil 1 then return .continue
  return .done { expr := ← mkAppM ``Havoc.loadsM #[cells], proof? := ← mkAppM ``Havoc.loadsM_eq #[cells] }

/-- The loads and library calls of a load of a cell the run does not know
(`VmState.registerCellLoads`, which a symbolic run leaves when the cell may be a library), named
`Havoc.cellLoads` (`Havoc.cellLoads_eq`), which `check_havoc` replaces by what is known of them. -/
simproc ↓ havocCellLoads (VmState.registerCellLoads _ _) := fun e => do
  let_expr VmState.registerCellLoads st steps := e | return .continue
  if (← instantiateMVars steps).isAppOfArity ``List.nil 1 then return .continue
  let pf ← mkAppM ``Havoc.cellLoads_eq #[st, steps]
  return .done { expr := ← mkAppM ``Havoc.cellLoads #[st, steps], proof? := pf }

/-! ## Walks of the empty dictionary -/

/-- `DICT*GETNEXT` on the empty dictionary (`null`) finds nothing and visits no cell. -/
theorem nearestWalk_none (hint : BitString) (fetchNext allowEq invertFirst : Bool)
    (r : Cell → Except Excno Cell) :
    dictNearestWithCells none hint fetchNext allowEq invertFirst r = .ok (none, #[]) := rfl

/-- `DICT*MIN`, `DICT*MAX` and their `REM` forms on the empty dictionary find nothing. -/
theorem minMaxWalk_none (n : Nat) (fetchMax invertFirst : Bool) (r : Cell → Except Excno Cell) :
    dictMinMaxWithCells none n fetchMax invertFirst r = .ok (none, #[]) := rfl

/-- A delete from the empty dictionary removes nothing and leaves it empty. -/
theorem deleteWalk_none (key : BitString) (r : Cell → Except Excno Cell) :
    dictDeleteWithLoads none key r = .ok (none, none, 0, #[]) := rfl

/-- `Excno.toInt e` of an exception the run does not know (the error of a walk of an unknown
dictionary, of a parse of an unknown slice): kept as it is, not unfolded into a case per exception
(sixteen paths that end alike); the end of the path needs only whether its exit code commits. A
`dsimproc`: also where `simp` only reduces (the arguments it does not rewrite). -/
dsimproc ↓ excnoToIntStop (Excno.toInt _) := fun e => do
  let_expr Excno.toInt x := e | return .continue
  let x ← instantiateMVars x
  if let .const n _ := x then
    if let some (.ctorInfo _) := (← getEnv).find? n then return .continue
  return .done e

/-- The number of an exception is between `0` and `15` (`Excno.toInt`): what `omega` needs of the
number of an exception the run does not know (`excnoBounds`). -/
theorem excnoToInt_bounds (e : Excno) : 0 ≤ e.toInt ∧ e.toInt ≤ 15 := by
  cases e <;> decide

/-- The goal `g` with `excnoToInt_bounds x` as a hypothesis for each exception `x` the run does not
know (not a constructor) whose number `Excno.toInt x` occurs in `c` (the condition of an `if`
`check_split` decides by `omega`), unless the context has it already: the range check of the
default exception handler (`0 ≤ n ≤ 65535`) on such a number is then decided, not split. -/
def excnoBounds (g : MVarId) (c : Expr) : MetaM MVarId := g.withContext do
  let r ← IO.mkRef (#[] : Array Expr)
  let _ ← Meta.transform c (pre := fun s => do
    if s.isAppOfArity ``Excno.toInt 1 then
      let x := s.appArg!
      unless x.isConst || x.hasLooseBVars do
        r.modify fun a => if a.contains x then a else a.push x
    return .continue)
  let lctx ← getLCtx
  let mut g := g
  for x in ← r.get do
    if x.hasAnyFVar (fun f => !lctx.contains f) then continue
    let pf ← mkAppM ``excnoToInt_bounds #[x]
    let ty ← instantiateMVars (← inferType pf)
    if (← g.withContext getLCtx).any (fun d => !d.isImplementationDetail && d.type == ty) then continue
    let (_, g') ← (← g.assert `hexc ty pf).intro1P
    g := g'
  return g

/-- The registers and the committed state after a jump is counted (`VmState.countJump`, which may
charge gas): those before. -/
theorem countJump_regs (st : VmState) : st.countJump.regs = st.regs := by
  simp only [VmState.countJump]; split <;> rfl

theorem countJump_cstate (st : VmState) : st.countJump.cstate = st.cstate := by
  simp only [VmState.countJump]; split <;> rfl

/-- The reruns of a step with libraries refused (`VmState.stepRefusingWith`, C++ `VmState::run`
with `max_library_loads`): whatever their number, the result is the step from `st` with some set of
libraries refused, its notes of libraries reset. -/
theorem stepRefusingWith_cases (exec : Instr → VM Unit) (st : VmState) :
    ∀ (k : Nat) (refused : Array BitString), ∃ R : Array BitString,
      st.stepRefusingWith exec refused k =
        (VmState.stepOnceWith exec { st with librariesRefused := R, librariesMissed := #[] }).mapState
          fun st => { st with librariesRefused := #[], librariesMissed := #[] }
  | 0, refused => ⟨refused, rfl⟩
  | k + 1, refused => by
    simp only [VmState.stepRefusingWith]
    split
    · exact ⟨refused, rfl⟩
    · exact stepRefusingWith_cases exec st k _

/-- What `VmState.stepWith` makes of a step `r` from `st` (`VmState.stepFinish`), by cases: `r`
without `max_library_loads`; with it, `r` with its notes of libraries reset, or the step again with
some set of libraries refused (`stepRefusingWith_cases`), its notes reset. -/
theorem stepFinish_cases (exec : Instr → VM Unit) (st : VmState) (r : StepResult) :
    (st.maxLibraryLoads = none ∧ VmState.stepFinish exec st r = r) ∨
    (st.maxLibraryLoads ≠ none ∧ VmState.stepFinish exec st r =
      r.mapState fun st => { st with librariesRefused := #[], librariesMissed := #[] }) ∨
    (st.maxLibraryLoads ≠ none ∧ ∃ R : Array BitString, VmState.stepFinish exec st r =
      (VmState.stepOnceWith exec { st with librariesRefused := R, librariesMissed := #[] }).mapState
        fun st => { st with librariesRefused := #[], librariesMissed := #[] }) := by
  by_cases hm : st.maxLibraryLoads = none
  · exact Or.inl ⟨hm, by unfold VmState.stepFinish; rw [if_pos (by rw [hm]; rfl)]⟩
  · have hn : ¬ (st.maxLibraryLoads.isNone = true) := by
      cases h : st.maxLibraryLoads with
      | none => exact absurd h hm
      | some _ => simp
    by_cases he : r.state.librariesMissed.isEmpty = true
    · exact Or.inr (Or.inl ⟨hm, by unfold VmState.stepFinish; rw [if_neg hn, if_pos he]⟩)
    · obtain ⟨R, hR⟩ := stepRefusingWith_cases exec st 7 (#[] ++ r.state.librariesMissed)
      exact Or.inr (Or.inr ⟨hm, R, by unfold VmState.stepFinish; rw [if_neg hn, if_neg he]; exact hR⟩)

/-- `check_step_finish`: `VmState.stepFinish exec st r` in the goal where the step `r` notes
libraries the run does not know (`librariesMissed` not `#[]`: after `check_havoc` with
`max_library_loads`) replaced by its cases (`stepFinish_cases`): `r` with its notes reset, or the
step again with some set `R` of libraries refused, its notes reset (the case without
`max_library_loads` closed when the state has it). No step of the reruns is run twice. -/
elab "check_step_finish" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let fields := getStructureFields (← getEnv) ``VmState
  let some iM := fields.idxOf? `librariesMissed | throwError "check_step_finish: no field"
  let notes (r : Expr) : Bool := Id.run do
    let r := if r.isAppOfArity ``StepResult.continue 1 then r.appArg!
      else if r.isAppOfArity ``StepResult.halt 2 then r.appArg! else r
    unless r.isAppOfArity ``VmState.mk 20 do return false
    let m := r.getArg! iM
    return m.hasFVar
  let some e := t.find? (fun x => x.isAppOfArity ``VmState.stepFinish 3 && !x.hasLooseBVars &&
      notes (x.getArg! 2))
    | throwError "check_step_finish: no step that notes libraries the run does not know"
  let pf ← mkAppM ``stepFinish_cases #[e.getArg! 0, e.getArg! 1, e.getArg! 2]
  let (_, g') ← (← g.assert `hsf (← inferType pf) pf).intro1P
  replaceMainGoal [g']
  let hsf := mkIdent `hsf
  let hc := mkIdent `hc
  let R := mkIdent `R
  evalTactic (← `(tactic| rcases $hsf:ident with ⟨$hc:ident, $hsf:ident⟩ | ⟨$hc:ident, $hsf:ident⟩ |
    ⟨$hc:ident, $R:ident, $hsf:ident⟩))
  evalTactic (← `(tactic| all_goals first
    | (exact Option.noConfusion $hc:ident)
    | (rw [$hsf:ident]; clear $hsf:ident $hc:ident)))

/-- For a list `cells` written out of cells known to be ordinary (`Cell.special` evaluates to
`false`: the cells of the code, cells written as `Cell.mkOrdinary`), the proof of
`cells.all (fun c => !c.special) = true` (by evaluation); else `none`. -/
def ordinaryCells? (cells : Expr) : MetaM (Option Expr) := do
  let cells ← instantiateMVars cells
  unless isListLit cells 10000 do return none
  let f := mkLambda `c .default (mkConst ``Cell) (mkApp (mkConst ``not) (mkApp (mkConst ``Cell.special) (.bvar 0)))
  let allE ← mkAppM ``List.all #[cells, f]
  let ok ← tryCatchRuntimeEx
    (do
      let r ← withTransparency .default <| whnf allE
      pure (r.isConstOf ``Bool.true))
    (fun _ => pure false)
  unless ok do return none
  return some (← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) (← mkEq allE (mkConst ``Bool.true)))

/-- `check_havoc`: the loads of cells in the goal (`Havoc.loads cells st`, the first) replaced by what
is known of them: normally or out of gas (two goals), in `st` with new gas and loaded cells (`gas`,
`loaded`); for cells not known to be ordinary (`ordinaryCells?`: `Havoc.loads_cases`) also new
loaded libraries and libraries noted missed (`libs`, `missed`), which without `max_library_loads`
(a case if it is a variable) stay those of `st`. -/
elab "check_havoc" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (fun x => (x.isAppOfArity ``Havoc.loads 2 || x.isAppOfArity ``Havoc.cellLoads 2) &&
      !x.hasLooseBVars)
    | throwError "check_havoc: no loads of unknown cells"
  let isList := e.isAppOfArity ``Havoc.loads 2
  let st := if isList then e.getArg! 1 else e.getArg! 0
  let ord? ← if isList then ordinaryCells? (e.getArg! 0) else pure none
  let pf ← if let some hord := ord? then mkAppM ``Havoc.loadsOrd_cases #[e.getArg! 0, hord, st]
    else if isList then mkAppM ``Havoc.loads_cases #[e.getArg! 0, st]
    else mkAppM ``Havoc.cellLoads_cases #[st, e.getArg! 1]
  let (_, g') ← (← g.assert `hhavoc (← inferType pf) pf).intro1P
  replaceMainGoal [g']
  let mk := fun (n : String) => mkIdent (Name.mkSimple n)
  -- `rfl` patterns: without macro scopes, or `rcases` takes them for names
  let rflP := mkIdent `rfl
  if ord?.isSome then
    evalTactic (← `(tactic| obtain ⟨$(mk "r"), $(mk "gas"), $(mk "loaded"), $(mk "hhavocEq"),
      $(mk "hhavocR")⟩ := $(mk "hhavoc")))
    evalTactic (← `(tactic| rw [$(mk "hhavocEq"):ident]))
    evalTactic (← `(tactic| clear $(mk "hhavocEq")))
    evalTactic (← `(tactic| rcases $(mk "hhavocR"):ident with $rflP:ident | $rflP:ident))
    return
  if isList then
    evalTactic (← `(tactic| obtain ⟨$(mk "r"), $(mk "gas"), $(mk "loaded"), $(mk "libs"), $(mk "missed"),
      $(mk "hhavocEq"), $(mk "hhavocR"), $(mk "hhavocNone")⟩ := $(mk "hhavoc")))
  else
    evalTactic (← `(tactic| obtain ⟨$(mk "gas"), $(mk "loaded"), $(mk "libs"), $(mk "missed"),
      $(mk "outOfGas"), $(mk "hhavocEq"), $(mk "hhavocNone")⟩ := $(mk "hhavoc")))
  evalTactic (← `(tactic| rw [$(mk "hhavocEq"):ident]))
  evalTactic (← `(tactic| clear $(mk "hhavocEq")))
  -- without `max_library_loads`: the libraries stay
  let mll ← whnfR (← mkAppM ``VmState.maxLibraryLoads #[st])
  if mll.isAppOf ``Option.none then
    evalTactic (← `(tactic| obtain ⟨$rflP:ident, $rflP:ident⟩ := $(mk "hhavocNone") rfl))
  else if mll.isFVar then
    let gs ← (← getMainGoal).cases mll.fvarId!
    replaceMainGoal (gs.map (·.mvarId)).toList
    evalTactic (← `(tactic| all_goals first
      | obtain ⟨$rflP:ident, $rflP:ident⟩ := $(mk "hhavocNone") rfl
      | clear $(mk "hhavocNone")))
  else
    evalTactic (← `(tactic| clear $(mk "hhavocNone")))
  if isList then
    evalTactic (← `(tactic| all_goals rcases $(mk "hhavocR"):ident with $rflP:ident | $rflP:ident))

/-- The loop head `S` (a `VmState.mk` application) with the parts an iteration of a loop changes as
holes: the gas, the loaded cells, the loaded libraries (loads of unknown cells, `check_havoc`), the
counters of jumps and steps, `c5`, the payloads of the top `k` stack entries (as many as there are
written out, as `Exec.loopHoles`, with the loaded libraries), and of a `REPEAT` loop the count of
its iterations left (`c0`, the last hole). The values of the holes in `S`, the function that
fills them, the index of the jump counter's hole and of `c5`'s. -/
def loopHolesX (S : Expr) (k : Nat) : MetaM (Array Expr × (Array Expr → Expr) × Nat × Nat) := do
  unless S.isAppOfArity ``VmState.mk 20 do throwError "check_loop: the state is not written out"
  let fields := getStructureFields (← getEnv) ``VmState
  let idx (n : Name) : MetaM Nat := do
    let some i := fields.idxOf? n | throwError "check_loop: no field {n}"
    return i
  let args := S.getAppArgs
  let plainNames := [`gas, `loadedCells, `loadedLibraries, `chainJumps, `steps]
  let plain ← plainNames.mapM idx
  let mut vals : Array Expr := plain.toArray.map (args[·]!)
  let iRegs ← idx `regs
  let regs := args[iRegs]!
  unless regs.isAppOfArity ``Regs.mk 7 do throwError "check_loop: the registers are not written out"
  vals := vals.push (regs.getArg! 5)
  let iStack ← idx `stack
  let mut stk := args[iStack]!
  let mut entries : Array (Expr → Expr) := #[]
  for _ in [0:k] do
    -- fewer entries (the stack a `*BRK` loop moves into `c1`): fewer holes
    unless stk.isAppOfArity ``Array.push 3 do break
    let some (p, f) := Exec.stackPayload? (stk.getArg! 2)
      | throwError "check_loop: a top stack entry is not a slice, cell, builder or integer"
    vals := vals.push p
    entries := entries.push f
    stk := stk.getArg! 1
  let nPlain := plain.length
  let top := vals.extract (nPlain + 1) vals.size
  vals := (vals.extract 0 (nPlain + 1)) ++ top.reverse
  -- a `REPEAT` loop (`c0` is `Continuation.repeatBody body after n`): the count of the iterations
  -- left, which every iteration changes, a hole too (the last)
  let c0 ← whnfR (regs.getArg! 0)
  let isRepeat := c0.isAppOfArity ``Continuation.repeatBody 3
  if isRepeat then vals := vals.push (c0.getArg! 2)
  let iCount := vals.size - 1
  let es := entries.reverse
  let base := stk
  let fill (xs : Array Expr) : Expr := Id.run do
    let mut a := args
    for j in [0:nPlain] do a := a.set! plain[j]! xs[j]!
    let mut ra := regs.getAppArgs.set! 5 xs[nPlain]!
    if isRepeat then
      ra := ra.set! 0 (mkApp3 (mkConst ``Continuation.repeatBody) (c0.getArg! 0) (c0.getArg! 1) xs[iCount]!)
    a := a.set! iRegs (mkAppN regs.getAppFn ra)
    let mut s := base
    for j in [0:es.size] do
      s := mkApp3 (mkConst ``Array.push [0]) (mkConst ``Value) s (es[j]! xs[nPlain + 1 + j]!)
    a := a.set! iStack s
    return mkAppN S.getAppFn a
  return (vals, fill, 3, nPlain)

/-- **The loop rule with the fuel bounded** (`VmState.runWith_inv` for the runs of at most `F`
steps): a loop inside a loop keeps what the outer loop's hypothesis needs, that the fuel left is at
most the outer one's. -/
theorem runWith_invLe (exec : Instr → VM Unit) (Inv : VmState → Prop) (P : StepResult → Prop) (F : Nat)
    (hzero : ∀ st, Inv st → P (st.runWith exec 0))
    (hstep : ∀ n, n + 1 ≤ F → ∀ st, Inv st → (∀ m, m ≤ n → ∀ st', Inv st' → P (st'.runWith exec m)) →
      P (st.runWith exec (n + 1))) :
    ∀ n, n ≤ F → ∀ st, Inv st → P (st.runWith exec n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro hn st hst
  cases n with
  | zero => exact hzero st hst
  | succ k => exact hstep k hn st hst (fun m hm st' h' => ih m (by omega) (by omega) st' h')

/-- `check_loop`: the loop rule (`runWith_invLe`, the fuel at most that of the head) at the loop head
of the run in the goal, with
the invariant "the state is the loop head but for the gas, the loaded cells and libraries, the
counters of jumps (fewer than `freeNestedContJump`) and steps, `c5` (satisfying `SafeActs`) and the
payload of the top stack entry" (`vm_loop_c5` of `TvmLean/Proofs/Contracts/Wallet3Run/Tactic.lean`
with the loaded libraries, which loads of unknown cells change). Leaves the run out of fuel and the
run with one more step from such a state, with the hypothesis `ih`. Fails inside two loops already
(a loop the rule does not close comes back here: reported, not run again). -/
elab "check_loop" : tactic => withMainContext do
  let g ← getMainGoal
  let nih := (← getLCtx).foldl (init := 0) fun n d => if d.userName == `ih then n + 1 else n
  if nih ≥ 2 then throwError "check_loop: inside two loops already"
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "check_loop: no run in the goal"
  let exec := r.getArg! 0
  let n := r.getArg! 1
  let S := r.getArg! 2
  let Q := mkConst ``SafeActs
  let (vals, fill, iChain, iC5) ← loopHolesX S 1
  let tys ← vals.mapM fun v => (inferType v : MetaM Expr)
  let stTy := mkConst ``VmState
  let inv ← withLocalDeclD `st stTy fun st => do
    let decls := (List.range vals.size).toArray.map fun i =>
      (Name.mkSimple s!"x{i}", fun (_ : Array Expr) => pure tys[i]!)
    let body ← withLocalDeclsD decls fun xs => do
      let bound ← mkAppM ``LT.lt #[xs[iChain]!, mkConst ``freeNestedContJump]
      let mut e ← mkAppM ``And #[← mkAppM ``And #[← mkEq st (fill xs), bound], (mkApp Q xs[iC5]!).headBeta]
      for x in xs.reverse do
        e ← mkAppM ``Exists #[← mkLambdaFVars #[x] e]
      return e
    mkLambdaFVars #[st] body
  let motive ← withLocalDeclD `r (mkConst ``StepResult) fun rv => do
    mkLambdaFVars #[rv] ((← kabstract t r).instantiate1 rv)
  let hzTy ← withLocalDeclD `st stTy fun st => do
    mkForallFVars #[st] (← mkArrow (mkApp inv st).headBeta
      (mkApp motive (← mkAppM ``VmState.runWith #[exec, mkNatLit 0, st])).headBeta)
  let hz ← mkFreshExprSyntheticOpaqueMVar hzTy
  let hinv ← mkFreshExprMVar (mkApp inv S).headBeta
  Exec.solveInvC5 hinv.mvarId!
  let rule ← mkAppOptM ``runWith_invLe #[exec, inv, motive, n, hz]
  let .forallE _ hsTy _ _ ← whnf (← inferType rule) | throwError "check_loop: the loop rule"
  let hs ← mkFreshExprSyntheticOpaqueMVar hsTy
  let pf ← mkAppOptM ``runWith_invLe #[exec, inv, motive, n, hz, hs, n, ← mkAppM ``Nat.le_refl #[n], S, hinv]
  unless ← isDefEq (← inferType pf) t do throwError "check_loop: the goal is not a property of the run"
  g.assign pf
  let (_, gz) ← hz.mvarId!.intro `st
  let (h0, gz) ← gz.intro `hinv
  let gz ← Exec.destructInv gz h0
  let (_, gs) ← hs.mvarId!.intro `n
  let (_, gs) ← gs.intro `hfuel
  let (_, gs) ← gs.intro `st
  let (h1, gs) ← gs.intro `hinv
  let (_, gs) ← gs.intro `ih
  let gs ← Exec.destructInv gs h1
  replaceMainGoal [gz, gs]

/-! ## Stacks written out -/

/-- The elements of an array written out from the empty array (`((#[].push a).push b)...`), the
first first, at most `n` deep. -/
def pushChain? : Expr → Nat → MetaM (Option (Array Expr))
  | _, 0 => pure none
  | e, n + 1 => do
    if e.isAppOfArity ``Array.push 3 then
      return (← pushChain? (e.getArg! 1) n).map (·.push (e.getArg! 2))
    -- the empty array, however written (`#[]`, `Array.empty`, `Array.mkEmpty`, ...)
    let α ← inferType e
    if ← withDefault (isDefEq e (← mkAppOptM ``Array.empty #[(← whnf α).appArg!])) then return some #[]
    return none

/-- `Array.extract a i j` (and `Array.take`, an `extract` from 0) of an array written out from the
empty array (a stack: the start of a run writes it out), the bounds numerals: the array of the
elements taken, written out the same way (definitionally equal, checked). What calls and jumps with
arguments leave of the stack (`VM.call`, `VM.jump`: the arguments passed, the stack saved). -/
simproc stackChainExtract (Array.extract _ _ _) := fun e => do
  let_expr Array.extract α a i j := e | return .continue
  let some i := (← whnfR i).rawNatLit? <|> (← instantiateMVars i).nat? | return .continue
  let some j := (← whnfR j).rawNatLit? <|> (← instantiateMVars j).nat? | return .continue
  let some xs ← pushChain? (← instantiateMVars a) 10000 | return .continue
  -- `α : Type u`: the level of `Array.push.{u}` is that of `α`'s sort minus one
  let lv := (← getLevel α).dec.getD levelZero
  let mut r := mkApp2 (mkConst ``List.toArray [lv]) α (mkApp (mkConst ``List.nil [lv]) α)
  for x in xs.extract i j do
    r := mkApp3 (mkConst ``Array.push [lv]) α r x
  -- `Array.extract` unfolds only with default transparency (simprocs run with reducible)
  unless ← withDefault (isDefEq e r) do return .continue
  return .done { expr := r }

/-- A literal array (`#[a, b, …]`, `List.toArray` of a list written out) cut by numerals
(`Array.extract`): the literal array of the part, as `Array.extract` computes it (the bits of a data
cell after a field, `(d.bits ++ #[false]).extract 0 32`, end in `#[false].extract 0 0`). -/
simproc arrayLitExtract (Array.extract _ _ _) := fun e => do
  let_expr Array.extract α a i j := e | return .continue
  let some i := (← whnfR i).rawNatLit? <|> (← instantiateMVars i).nat? | return .continue
  let some j := (← whnfR j).rawNatLit? <|> (← instantiateMVars j).nat? | return .continue
  let some (_, xs) := (← instantiateMVars a).arrayLit? | return .continue
  if xs.length > 1024 then return .continue
  let lv := (← getLevel α).dec.getD levelZero
  let r := mkApp2 (mkConst ``List.toArray [lv]) α (← mkListLit α (xs.toArray.extract i j).toList)
  unless ← withDefault (isDefEq e r) do return .continue
  return .done { expr := r }

/-- An entry of a literal array at a numeral (`#[a, b, …][i]!`): the entry. -/
simproc arrayLitGetElem (@GetElem?.getElem! (Array _) Nat _ _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``GetElem?.getElem! 8 do return .continue
  let some i := (← whnfR (e.getArg! 7)).rawNatLit? <|> (← instantiateMVars (e.getArg! 7)).nat?
    | return .continue
  let some (_, xs) := (← instantiateMVars (e.getArg! 6)).arrayLit? | return .continue
  let some x := xs[i]? | return .continue
  unless ← withDefault (isDefEq e x) do return .continue
  return .done { expr := x }

/-! ## Calls and jumps with arguments -/

/-- Whether `e` is an integer numeral at least `0` (`2`, `Int.ofNat 2`). -/
def nonnegIntLit (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  if let some v ← getIntValue? e then return 0 ≤ v
  if e.isAppOfArity ``Int.ofNat 1 then return (← getNatValue? e.appArg!).isSome
  return false

/-- Whether `k` is a continuation written out (a constructor application) whose closure data, if
any, is written out too, with a nonempty stack (`OrdCdata.mk s n`, not `OrdCdata.empty`). -/
def contWithArgs (k : Expr) : MetaM Bool := do
  let k ← whnfR (← instantiateMVars k)
  unless k.isAppOfArity ``Continuation.ordinary 4 || k.isAppOfArity ``Continuation.envelope 3 do
    return false
  let cd ← whnfR k.appArg!
  return cd.isAppOfArity ``OrdCdata.mk 2 && !(← whnfR cd.appFn!.appArg!).isAppOf ``List.toArray

/-- `VM.call k p r`, `VM.jump k p` and `VM.callComputeStacks s c n p` with arguments passed (`p` a
numeral from `0`: `CALLXARGS`, `JMPXARGS`, `RETARGS`) to a continuation written out, and the jump
back to a return continuation that keeps values (`VM.jump k`, `k`'s closure data written out with a
stack): unfolded, the stacks then written out (`stackChainExtract`). The lemmas of `vm_run` cover
the calls and jumps without arguments; `unfoldModelRun` leaves calls and jumps alone. -/
dsimproc callArgsUnfold (@ExceptT.run Excno (StateM VmState) _ _ _) := fun e => do
  let args := e.getAppArgs
  unless args.size == 5 do return .continue
  let m := args[3]!
  let some f := m.getAppFn.constName? | return .continue
  let n := m.getAppNumArgs
  if f == ``VM.callComputeStacks && n == 4 then
    unless ← nonnegIntLit (m.getArg! 3) do return .continue
  else if (f == ``VM.call && n == 3) || (f == ``VM.jump && n == 2) then
    let k ← whnfR (← instantiateMVars (m.getArg! 0))
    let .const c _ := k.getAppFn | return .continue
    unless (← getEnv).isConstructor c do return .continue
    unless (← nonnegIntLit (m.getArg! 1)) || (f == ``VM.jump && (← contWithArgs k)) do
      return .continue
  else
    return .continue
  match ← withTransparency .all (unfoldDefinition? m) with
  | some m' => return .visit (mkAppN e.getAppFn (args.set! 3 m'.headBeta))
  | none => return .continue

/-- `List.range' a n s` with numerals, written out: the `for` loops of the model over ranges
(`for i in [0:k]`, `VM.execNullSwapIf`), after `Std.Range.forIn_eq_forIn_range'`, go on as loops
over a list literal (`List.forIn_cons`). -/
simproc listRangeLit (List.range' _ _ _) := fun e => do
  let_expr List.range' a n s := e | return .continue
  let num (x : Expr) : MetaM (Option Nat) := do
    let x ← instantiateMVars x
    if let some k := x.rawNatLit? <|> x.nat? then return some k
    (evalNat x).run
  let some a ← num a | return .continue
  let some n ← num n | return .continue
  let some s ← num s | return .continue
  if n > 256 then return .continue
  let r ← mkListLit (mkConst ``Nat) ((List.range' a n s).map mkNatLit)
  return .done { expr := r }

/-! ## Dictionaries as maps -/

/-- Runs `tac` on `g` within `hb` thousand heartbeats: whether it closes `g` (nothing kept of an
attempt that does not, its messages neither). -/
def closesWith (g : MVarId) (tac : TSyntax `tactic) (hb : Nat) : TacticM Bool := do
  let s ← saveState
  let n0 := (← Core.getMessageLog).toList.length
  tryCatchRuntimeEx
    (do
      let gs ← withCurrHeartbeats <| withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := hb * 1000 })
        (Term.withoutErrToSorry (Tactic.run g (evalTactic tac)))
      let msgs := (← Core.getMessageLog).toList
      if !gs.isEmpty || (msgs.drop n0).any (·.severity == .error) then
        s.restore
        return false
      return true)
    (fun _ => do s.restore; return false)

/-- A proof of `ResolvesOrdinary r` for the resolver of a walk: the default one or the VM's
(`resolvesOrdinary_library`). -/
def resolvesOrd? (r : Expr) : TacticM (Option Expr) := do
  let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``ResolvesOrdinary #[r])
  if ← closesWith g.mvarId! (← `(tactic| first
      | exact TvmLean.resolvesOrdinary_rejectSpecial
      | exact TvmLean.resolvesOrdinary_library _ _ _)) 20000 then
    return some (← instantiateMVars g)
  return none

/-- A proof of `Dict.WF root sz` from a hypothesis `Dict.WF root m` of the context and `sz = m` (by
`rfl`, `assumption` or `omega`): the dictionaries an invariant says are well-formed. -/
def findWF? (root sz : Expr) : TacticM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Dict.WF 2 do continue
    unless ← withReducible (isDefEq (ty.getArg! 0) root) do continue
    let m := ty.getArg! 1
    let gEq ← mkFreshExprSyntheticOpaqueMVar (← mkEq sz m)
    if ← closesWith gEq.mvarId! (← `(tactic| first | rfl | assumption | omega)) 20000 then
      let e ← mkCongrArg (mkApp (mkConst ``Dict.WF) root) (← instantiateMVars gEq)
      return some (← mkEqMPR e (mkFVar d.fvarId))
  return none

/-- `check_dict_facts`: what the map of a dictionary says of the walks the run has split on.

* For a walk `dictNearestWithCells … = .ok r` or `dictMinMaxWithCells … = .ok r` (`DICT*GETNEXT*`,
  `DICT*MIN*`, ...) whose result is a constructor (`r.1` reduces to one, or an equation `r.1 = some
  (v, k)`, `r.1 = none` of the context): the key found is the first of the map after the hint, ...
  (`TvmLean/Proofs/Exec/Dict/Near.lean`): in `Dict.value` if the dictionary is well-formed by a
  hypothesis (`Dict.nearest_value_ok`, `Dict.minMax_value_ok`), else as the lookups with the walk's
  resolver read it (`Dict.nearest_spec_ok`, `Dict.minMax_spec_ok`); unfolded, a hypothesis `hmap`.
* For a delete with the VM's resolver on a well-formed dictionary (`DICT*REMMIN`, ...): the same
  delete with the default resolver (`Dict.deleteWithLoads_resolve`), a hypothesis `hdel`, the form of
  `Dict.value_delete`, `Dict.WF.delete`.

Nothing if the fact is there already. -/
elab "check_dict_facts" : tactic => withMainContext do
  let mut g ← getMainGoal
  let lctx ← getLCtx
  let mut known : Array Expr := #[]
  for d in lctx do
    unless d.isImplementationDetail do known := known.push (← instantiateMVars d.type)
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isAppOfArity ``Except.ok 3 do continue
    if lhs.isAppOfArity ``dictDeleteWithLoads 3 then
      let res := lhs.getArg! 2
      if res.isConstOf ``Cell.rejectSpecial then continue
      let some hr ← resolvesOrd? res | continue
      let some hwf ← findWF? (lhs.getArg! 0) (← mkAppM ``Array.size #[lhs.getArg! 1]) | continue
      let e ← mkAppM ``Dict.deleteWithLoads_resolve #[hr, hwf]
      let pf ← mkEqTrans (← mkEqSymm e) (mkFVar d.fvarId)
      let fty ← instantiateMVars (← inferType pf)
      if known.contains fty then continue
      known := known.push fty
      let (_, g') ← (← g.assert `hdel fty pf).intro1P
      g := g'
      continue
    let isNear := lhs.isAppOfArity ``dictNearestWithCells 6
    let isMinMax := lhs.isAppOfArity ``dictMinMaxWithCells 5
    unless isNear || isMinMax do continue
    let root := lhs.getArg! 0
    let res := lhs.getArg! (if isNear then 5 else 4)
    let sz ← if isNear then mkAppM ``Array.size #[lhs.getArg! 1] else pure (lhs.getArg! 1)
    let mut pf0? : Option Expr := none
    if let some hr ← resolvesOrd? res then
      if let some hwf ← findWF? root sz then
        let refl ← mkEqRefl sz
        pf0? ← tryCatch
          (some <$> (if isNear then
              mkAppM ``Dict.nearest_value_ok #[hr, hwf, refl, mkFVar d.fvarId]
            else mkAppM ``Dict.minMax_value_ok #[hr, hwf, mkFVar d.fvarId]))
          (fun _ => pure none)
    let pf0 ← match pf0? with
      | some p => pure p
      | none => mkAppM (if isNear then ``Dict.nearest_spec_ok else ``Dict.minMax_spec_ok) #[mkFVar d.fvarId]
    let pty ← instantiateMVars (← inferType pf0)
    let o := pty.appArg!
    let isCtor (e : Expr) := e.isAppOf ``Option.some || e.isAppOf ``Option.none
    let o' ← whnfR o
    let mut res? : Option (Expr × Expr) := none
    if isCtor o' then
      res? := some (o', pf0)
    else
      for d' in lctx do
        if d'.isImplementationDetail then continue
        let t' ← instantiateMVars d'.type
        let some (_, a, b) := t'.eq? | continue
        unless isCtor b do continue
        unless ← withReducible (isDefEq a o) do continue
        let e ← mkCongrArg pty.appFn! (mkFVar d'.fvarId)
        res? := some (b, ← mkEqMP e pf0)
        break
    let some (c, pf) := res? | continue
    let fty ← withTransparency .all <| whnf (mkApp pty.appFn! c)
    let fty ← instantiateMVars fty
    if known.contains fty then continue
    known := known.push fty
    let (_, g') ← (← g.assert `hmap fty pf).intro1P
    g := g'
  replaceMainGoal [g]

/-- The data of the return continuation of a call with no arguments (`VmState.callTo`,
`CallFrame.identity`): the empty one. -/
theorem cdata_callFrame_identity :
    ({ stack := CallFrame.identity.savedStack, nargs := CallFrame.identity.retArgs } : OrdCdata) =
      OrdCdata.empty := rfl

end TvmLean.Check

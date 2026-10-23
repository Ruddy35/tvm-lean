import TvmLean.Proofs.Tx.Induction
import TvmLean.Proofs.Tx.NoSetCode
import TvmLean.Proofs.Exec.IteInst
import TvmLean.Proofs.Contracts.Wallet3Run.Common
import TvmLean.Proofs.Exec.Spec.ArithExt
import TvmLean.Proofs.Exec.Spec.StackExt
import TvmLean.Proofs.Exec.Spec.CellExt
import TvmLean.Proofs.Exec.Spec.Tuple
import TvmLean.Proofs.Exec.Spec.DictSet
import TvmLean.Proofs.Exec.Spec.DictDel
import TvmLean.Proofs.Exec.Spec.DictSetGet
import TvmLean.Proofs.Exec.Spec.MsgAddr
import TvmLean.Proofs.Exec.Spec.MsgExt
import TvmLean.Proofs.Exec.Spec.ArithShift
import TvmLean.Proofs.Exec.Spec.ArithShiftMod
import TvmLean.Proofs.Exec.Spec.ArithMulShift
import TvmLean.Proofs.Exec.Spec.ArithShlDiv
import TvmLean.Proofs.Exec.Spec.TupleVar
import TvmLean.Proofs.Exec.Spec.CellCheck
import TvmLean.Proofs.Exec.Spec.CellIntVar
import TvmLean.Proofs.Exec.Spec.CellSize
import TvmLean.Proofs.Exec.Spec.StackVar
import TvmLean.Proofs.Exec.Spec.LoopBrk
import TvmLean.Proofs.Exec.Closure
import TvmLean.Proofs.Check.Attr
import TvmLean.Proofs.Check.Closers

/-!
# Checking an invariant of a contract over all transactions: `ran_preserves`

`Reachable.code_fixed` (TvmLean/Proofs/Tx/Induction.lean) turns an invariant `P` of the data of an
account whose code is `C` into a theorem about every shard account reachable by transactions, given
its obligation about one run of the compute phase:

    ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧ ∀ c, ¬ActionIn c5 (.setCode c)

`ran_preserves [hints]` proves that obligation for a closed code literal `C` (a cell term of
`tools/boc2lean`) and a predicate `P` with no proof about the contract: it runs the code
symbolically from every state the compute phase may start it from and checks `P` at the end of every
path that commits.

* `ran_preserves_of`: the obligation from six statements `RunsKeep`, one per kind of transaction
  (`ComputeStack`: an external message, an internal message, tick-tock) and range of global versions
  (from 4: out of gas stops at once and `CHKSIGNU` is counted, C++ vm.h:203-209, 434-443; below 4),
  each about every run from `start` with data satisfying `P` and any `c7`, gas limits, libraries,
  limits and loaded cells (`lc`: with the loaded cells unknown the gas of each cell load stays a
  term, so the kernel never evaluates the hash of a cell of the code), for any number of steps: a
  run that commits leaves data satisfying `P` and an action list of `SENDRAWMSG` and `RAWRESERVE`
  actions only (`Keeps`, `SafeActs`, which has no `SETCODE`: `SafeActs.noSetCode`).
* `ran_case [hints]` proves one `RunsKeep`:
  1. the hypothesis `P data` is unfolded and taken apart (`check_destruct`: `∃` and `∧`, equations of
     variables substituted, the definitions among the hints unfolded), so that the data the run reads
     is the term of `P` (e.g. `Data.encode d` with the hint `Data.encode`);
  2. every path of the run to its end (`check_paths`, one step at a time by `check_one_step`):
     `vm_run`'s steps (TvmLean/Proofs/Exec/Tactic.lean) with every specification of `vm_spec`
     (the modules of TvmLean/Proofs/Exec/Spec/ and the calls of closures,
     TvmLean/Proofs/Exec/Closure.lean, all imported here), the lemmas of a run from the compute
     phase's start (those of `wallet_run`, TvmLean/Proofs/Contracts/Wallet3Run/Common.lean), the fresh
     instances of `if` (TvmLean/Proofs/Exec/IteInst.lean), the reading of bits written by
     `natToBits` (`extract_natToBits_all` and the like), the hints, and every loop by the loop rule
     with the action list invariant `SafeActs` (`vm_loop_c5`); the position in the code is noted at
     each step (`check_mark_pos`). Every `check.cut` steps (default 40) a path is cut (`cutGoal`):
     the rest of the run from there, its gas and its set of loaded cells made variables (no end of
     a path depends on them; the gas term otherwise grows with every load), is proved as an
     auxiliary theorem over the hypotheses it uses, which the kernel checks on its own: no proof
     term holds a whole long run, and paths that reach the same statement share its theorem;
  3. the end of every path (`finishLeaf`): a path that halts with an exception or runs out of fuel
     does not commit (`keeps_haltResult`, `keeps_halt`); a path that exits normally must leave `c4`
     satisfying `P` (unfolded, normalized by `simp` with the hints, its existential witnesses found
     by unification, `checkExists`, the rest by `rfl`, `assumption`, `omega`, `decide`, `simp only`)
     and `c5` made of `SENDRAWMSG` and `RAWRESERVE` actions (`safe_acts_close`).
  A path it cannot close fails the tactic with a report per path: the code position of the last
  step (the cell as `C.refs[i]!...`, the bit, the instruction), the exit code, the path condition
  (the hypotheses of the path but those about the gas, which are counted) and the goal left.
* `ran_preserves [hints]`: the six statements of `ran_preserves_of` by `ran_case` in one proof
  (`tools/contract-check` states them as six theorems instead, which Lean elaborates in parallel).

What it does not do: code that changes itself (`SETCODE`), that adds other actions, that runs a
loop inside a loop whose exit it cannot tell, recursion that is not a loop, and data that `P` does
not give as a term the run can read (it then splits on the unknown sizes of the cell and fails).
-/

namespace TvmLean.Check

open TvmLean.Tx

/-! ## The statements -/

/-- The state the compute phase starts `code` from (`TvmLean.Tx.VmStart` with the code loaded as
itself, `convertCodeCell_ordinary`), with the loaded cells `lc` (the compute phase starts with none). -/
def start (code data : Cell) (stack : Stack) (c7 : Value) (gl gm gc : Int) (gv : Nat)
    (libs : Array Cell) (mdd : Nat) (mll : Option Nat) (lc : Array (Array UInt8)) : VmState :=
  { computePhaseInit code data stack #[c7] gl gm gc gv with
    libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll, loadedCells := lc }

/-- A run's result keeps `P`: if it committed, the committed data satisfies `P` and the committed
action list is made of `SENDRAWMSG` and `RAWRESERVE` actions. -/
def Keeps (P : Option Cell → Prop) (r : StepResult) : Prop :=
  r.state.cstate.committed = true → P (some r.state.cstate.c4) ∧ SafeActs r.state.cstate.c5

/-- Every run of `code` from the stack `stack`, data satisfying `P`, a global version satisfying
`G`, any `c7`, gas limits, libraries, limits and loaded cells, for any number of steps, keeps `P`. -/
def RunsKeep (code : Cell) (P : Option Cell → Prop) (stack : Stack) (G : Nat → Prop) : Prop :=
  ∀ data : Option Cell, P data → ∀ (c7 : Value) (gl gm gc : Int) (gv : Nat), G gv →
    ∀ (libs : Array Cell) (mdd : Nat) (mll : Option Nat) (lc : Array (Array UInt8)) (fuel : Nat),
      Keeps P (VmState.runWith execInstr fuel
        (start code (data.getD Cell.empty) stack c7 gl gm gc gv libs mdd mll lc))

/-- The stack of a tick-tock transaction (`ComputeStack`). -/
def tickTockStack (bal addr tock : Int) : Stack :=
  #[.int (.num bal), .int (.num addr), .int (.num tock), .int (.num (-2))]

/-- **The obligation of `Reachable.code_fixed` from the runs of each kind of transaction.** -/
theorem ran_preserves_of {C : Cell} {P : Option Cell → Prop} (hC : C.special = false)
    (hext : ∀ bal val msg body, RunsKeep C P (computePhaseStack bal val msg body true) (4 ≤ ·))
    (hextOld : ∀ bal val msg body, RunsKeep C P (computePhaseStack bal val msg body true) (· < 4))
    (hint : ∀ bal val msg body, RunsKeep C P (computePhaseStack bal val msg body false) (4 ≤ ·))
    (hintOld : ∀ bal val msg body, RunsKeep C P (computePhaseStack bal val msg body false) (· < 4))
    (htt : ∀ bal addr tock, RunsKeep C P (tickTockStack bal addr tock) (4 ≤ ·))
    (httOld : ∀ bal addr tock, RunsKeep C P (tickTockStack bal addr tock) (· < 4)) :
    ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧ ∀ c, ¬ActionIn c5 (.setCode c) := by
  intro data c4 c5 hP hr
  obtain ⟨st, ⟨gv, libs, stack, c7, gl, gm, gc, mdd, mll, hstack, rfl⟩, hcomm, -, rfl, rfl⟩ := hr
  rw [convertCodeCell_ordinary C gv libs hC] at hcomm ⊢
  have hst : ({ computePhaseInit C (data.getD Cell.empty) stack #[c7] gl gm gc gv with
      libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll } : VmState) =
      start C (data.getD Cell.empty) stack c7 gl gm gc gv libs mdd mll #[] := rfl
  rw [hst, vmFinal_eq] at hcomm ⊢
  generalize hS : start C (data.getD Cell.empty) stack c7 gl gm gc gv libs mdd mll #[] = S at hcomm ⊢
  have hk : Keeps P (VmState.runWith execInstr (S.gas.stepBound + 16) S) := by
    subst hS
    rcases hstack with ⟨bal, val, msg, body, ext, rfl⟩ | ⟨bal, addr, tock, rfl⟩
    · cases ext
      · by_cases hgv : 4 ≤ gv
        · exact hint bal val msg body data hP c7 gl gm gc gv hgv libs mdd mll #[] _
        · exact hintOld bal val msg body data hP c7 gl gm gc gv (by omega) libs mdd mll #[] _
      · by_cases hgv : 4 ≤ gv
        · exact hext bal val msg body data hP c7 gl gm gc gv hgv libs mdd mll #[] _
        · exact hextOld bal val msg body data hP c7 gl gm gc gv (by omega) libs mdd mll #[] _
    · by_cases hgv : 4 ≤ gv
      · exact htt bal addr tock data hP c7 gl gm gc gv hgv libs mdd mll #[] _
      · exact httOld bal addr tock data hP c7 gl gm gc gv (by omega) libs mdd mll #[] _
  obtain ⟨h4, h5⟩ := hk hcomm
  exact ⟨h4, h5.noSetCode⟩

/-! ## The ends of the paths -/

/-- The commit at a normal exit (`VmState.tryCommit`): `c4` and `c5` committed, or nothing. -/
theorem tryCommit_cases (st : VmState) :
    st.tryCommit = (true, { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } }) ∨
      st.tryCommit = (false, st) := by
  unfold VmState.tryCommit
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A run that halts (`VmState.haltResult`) keeps `P` if the state it halts in does (its committed
state) and, on a normal exit (`-1`, `-2`), its `c4` and `c5` satisfy `P` and `SafeActs` (what the
commit takes). -/
theorem keeps_haltResult {P : Option Cell → Prop} (ec : Int) (st : VmState)
    (h1 : st.cstate.committed = true → P (some st.cstate.c4) ∧ SafeActs st.cstate.c5)
    (h2 : ec = -1 ∨ ec = -2 → P (some st.regs.c4) ∧ SafeActs st.regs.c5) :
    Keeps P (VmState.haltResult ec st) := by
  unfold Keeps VmState.haltResult
  by_cases hec : ec = -1 ∨ ec = -2
  · rw [if_pos hec]
    rcases tryCommit_cases st with h | h
    · rw [h]
      intro _
      exact h2 hec
    · rw [h]
      exact h1
  · rw [if_neg hec]
    exact h1

theorem keeps_halt {P : Option Cell → Prop} (ec : Int) (st : VmState)
    (h1 : st.cstate.committed = true → P (some st.cstate.c4) ∧ SafeActs st.cstate.c5) :
    Keeps P (StepResult.halt ec st) := h1

theorem keeps_continue {P : Option Cell → Prop} (st : VmState)
    (h1 : st.cstate.committed = true → P (some st.cstate.c4) ∧ SafeActs st.cstate.c5) :
    Keeps P (StepResult.continue st) := h1

/-! ## Reading bits that `natToBits` wrote

Data given by `P` as a term (`Data.encode d`: `Cell.mkOrdinary (natToBits a 32 ++ ...) #[]`) is
read by the run as `bitsToNat` of `extract`s of that concatenation: with these lemmas and the sizes
of `natToBits` (literals) the reads reduce to the fields (`a % 2^32`, or `a` when the context bounds
it). -/

theorem extract_natToBits_empty (n k i j : Nat) (h : j ≤ i) : (natToBits n k).extract i j = #[] :=
  Array.extract_eq_empty_of_le (by omega)

theorem extract_natToBits_past (n k i j : Nat) (h : k ≤ i) : (natToBits n k).extract i j = #[] :=
  Array.extract_eq_empty_of_le (by simp [natToBits_size]; omega)

theorem extract_natToBits_all (n k j : Nat) (h : k ≤ j) : (natToBits n k).extract 0 j = natToBits n k :=
  Array.extract_eq_self_of_le (by simp [natToBits_size]; omega)

theorem readBits_mkOrdinary (b : BitString) (r : Array Cell) (p q n : Nat) :
    Slice.readBits { cell := Cell.mkOrdinary b r, bitPos := p, refPos := q } n = b.extract p (p + n) := rfl

theorem readBits_ofCell_mkOrdinary (b : BitString) (r : Array Cell) (n : Nat) :
    Slice.readBits (Slice.ofCell (Cell.mkOrdinary b r)) n = b.extract 0 n := by
  simp [Slice.readBits, Slice.ofCell, Cell.mkOrdinary]

/-- `CTOS` of a cell written as `Cell.mkOrdinary` (ordinary by definition). -/
@[vm_spec] theorem ctos_mkOrdinary (st : VmState) (s : Stack) (b : BitString) (r : Array Cell)
    (hs : st.stack = s.push (.cell (Cell.mkOrdinary b r))) :
    ExceptT.run (execInstr .ctos) st =
      if ({ st with stack := s }.registerCellLoad (Cell.mkOrdinary b r)).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s }.registerCellLoad (Cell.mkOrdinary b r))
      else
        (.ok (), { { st with stack := s }.registerCellLoad (Cell.mkOrdinary b r) with
          stack := s.push (.slice (Slice.ofCell (Cell.mkOrdinary b r))) }) :=
  Spec.ctos st s _ hs rfl

end TvmLean.Check

namespace TvmLean

/-! ## The action list: `SENDRAWMSG` and `RAWRESERVE` actions -/

/-- `SafeActs c5`: the empty list, a hypothesis, or `SENDRAWMSG`/`RAWRESERVE` actions added to one. -/
syntax "safe_acts_close" : tactic
macro_rules
  | `(tactic| safe_acts_close) => `(tactic| first
      | exact SafeActs.empty
      | assumption
      | (refine SafeActs.send _ _ ?_; safe_acts_close)
      | (refine SafeActs.reserve _ _ ?_; safe_acts_close))

/-- `vm_c5_close` (the invariant of `c5` at a loop head of `vm_loop_c5`) for `SafeActs`. -/
macro_rules
  | `(tactic| vm_c5_close) => `(tactic| safe_acts_close)

end TvmLean

namespace TvmLean.Check

open Lean Meta Elab Tactic

register_option check.debug : Bool := {
  defValue := false
  descr := "log what `check_paths` and `check_finish` (TvmLean/Proofs/Check/Tactic.lean) make of each \
    end of a path"
}

register_option check.progress : Bool := {
  defValue := false
  descr := "print each step of `check_paths` (TvmLean/Proofs/Check/Tactic.lean) to the standard error \
    (`/dev/stderr`) as it goes: the paths open, the code position, the time"
}

/-! ## Taking the invariant apart -/

/-- The hypothesis `h` with its type's head definition unfolded if it is one of `names`. -/
def unfoldHead? (ty : Expr) (names : Array Name) : MetaM (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  let .const n _ := ty.getAppFn | return none
  unless names.contains n do return none
  let some ty' ← unfoldDefinition? ty | return none
  return some ty'.headBeta

/-- One step of taking the hypotheses apart: a hypothesis `∃`/`∧` split, an equation of a variable
substituted, `some a = some b` made `a = b`, a definition of `names` unfolded. -/
def destructStep (g : MVarId) (names : Array Name) (skip : Array FVarId) : MetaM (Option MVarId) :=
  g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail || skip.contains d.fvarId then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    if let some ty' ← unfoldHead? ty names then
      return some (← g.replaceLocalDeclDefEq d.fvarId ty')
    let ty ← whnfR ty
    if ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2 then
      -- the parts named for the report: the witness by its binder (`∃ d, ...`: `d`), facts `h`
      let names := match ty.getArg! 1 with
        | .lam n _ _ _ => if ty.isAppOfArity ``Exists 2 then [n.eraseMacroScopes, `h] else [`h, `h]
        | _ => [`h, `h]
      let gs ← g.cases d.fvarId #[{ varNames := names }]
      let some sg := gs[0]? | return none
      return some sg.mvarId
    if let some (_, a, b) := ty.eq? then
      let mut canSubst := false
      if a.isFVar then canSubst := !(← exprDependsOn b a.fvarId!)
      if !canSubst && b.isFVar then canSubst := !(← exprDependsOn a b.fvarId!)
      if canSubst then
        try return some (← subst g d.fvarId) catch _ => pure ()
      let a' ← whnfR a
      let b' ← whnfR b
      if a'.isAppOfArity ``Option.some 2 && b'.isAppOfArity ``Option.some 2 then
        let pf ← mkAppM ``Option.some.inj #[d.toExpr]
        let (_, g') ← (← g.assert d.userName (← inferType pf) pf).intro1P
        return some (← g'.clear d.fvarId)
    if ty.isConstOf ``True then
      return some (← g.clear d.fvarId)
  return none

/-! ## The position in the code -/

/-- A cell of the code written `C.refs[i]!.refs[j]!...`: the constant `C` and the path `[i, j, ...]`
(at most `depth` references deep). -/
def cellPath? (e : Expr) : (depth : Nat := 64) → MetaM (Option (Name × List Nat))
  | 0 => pure none
  | depth + 1 => do
    if let .const n _ := e then return some (n, [])
    if e.isAppOfArity ``getElem! 8 then
      let xs := e.getArg! 6
      let i ← whnfR (e.getArg! 7)
      let some k := i.rawNatLit? <|> i.nat? | return none
      if xs.isAppOfArity ``Cell.refs 1 then
        let some (n, p) ← cellPath? xs.appArg! depth | return none
        return some (n, p ++ [k])
    return none

/-- The tag of a goal that notes the code position `(root, path, bit, refs)` of the step. -/
def posTag (root : String) (path : List Nat) (bit refs : Nat) : Name :=
  Name.mkStr (Name.mkStr .anonymous "vmpos") s!"{root}|{",".intercalate (path.map toString)}|{bit}|{refs}"

/-- `check_mark_pos`: notes in the goal's tag the code position the run in the goal is about to
run (the current continuation's slice), for the report of a path that is not proved. -/
elab "check_mark_pos" : tactic => withMainContext do
  let g ← getMainGoal
  let some st := Exec.runState? (← instantiateMVars (← g.getType)) | return
  let cc ← whnfCore (← whnfR (← mkAppM ``VmState.cc #[st]))
  unless cc.isAppOfArity ``Continuation.ordinary 4 do return
  let code ← whnfR (cc.getArg! 0)
  unless code.isAppOfArity ``Slice.mk 3 do return
  let bit ← whnfR (code.getArg! 1)
  let refs ← whnfR (code.getArg! 2)
  let some b := bit.rawNatLit? <|> bit.nat? | return
  let some r := refs.rawNatLit? <|> refs.nat? | return
  match ← cellPath? (code.getArg! 0) with
  | some (root, path) => g.setTag (posTag (toString root) path b r)
  | none => g.setTag (posTag "_" [] b r)

/-- The code position noted in a tag (`posTag`), described: the cell, the bit and the instruction
there. -/
def describePos (tag : Name) : MetaM String := do
  let comps := tag.components.filterMap fun c =>
    match c with
    | .str _ s => if s.contains '|' then some s else none
    | _ => none
  let some s := comps.getLast? | return "(unknown)"
  let parts := s.splitOn "|"
  let [rootS, pathS, bitS, refsS] := parts | return s
  let path := (pathS.splitOn ",").filterMap String.toNat?
  let some bit := bitS.toNat? | return s
  let some refs := refsS.toNat? | return s
  if rootS == "_" then
    return s!"a cell of a continuation the code built (PUSHCONT), bit {bit}"
  let root := rootS.toName
  let cellDesc := rootS ++ String.join (path.map fun k => s!".refs[{k}]!")
  let mut instr := ""
  try
    let mut e := mkConst root
    for k in path do
      e ← mkAppOptM ``getElem! #[none, none, none, none, none, none, ← mkAppM ``Cell.refs #[e], mkNatLit k]
    let sl ← Exec.evalSlice (mkApp3 (mkConst ``Slice.mk) e (mkNatLit bit) (mkNatLit refs))
    if sl.bitsRemaining == 0 then
      instr := if sl.refsRemaining == 0 then "the implicit RET at the end of the cell" else "the implicit JMPREF"
    else
      match decodeCp0WithBits sl with
      | .ok (i, _, _) => instr := toString i
      | .error _ => instr := "(no instruction decodes there)"
  catch _ => pure ()
  return s!"cell {cellDesc}, bit {bit}: {instr}"

/-! ## The run -/

/-- `check_loop_close`: the run is back at the head of a loop of `vm_loop_c5`: by its hypothesis
`ih` (the latest that applies, for a loop inside a loop). -/
elab "check_loop_close" : tactic => withMainContext do
  let g ← getMainGoal
  let ihs := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.userName == `ih && !d.isImplementationDetail then acc.push d.fvarId else acc
  for ih in ihs.reverse do
    let s ← saveState
    try
      let gs ← g.apply (mkFVar ih)
      let mut rest := #[]
      for g' in gs do
        if ← g'.isAssigned then continue
        let ty ← whnfR (← instantiateMVars (← g'.getType))
        if ty.isAppOf ``LE.le then
          let r ← Tactic.run g' (evalTactic (← `(tactic| omega)))
          unless r.isEmpty do throwError "check_loop_close: the fuel"
        else if ty.isAppOf ``Exists then
          Exec.solveInvC5 g'
        else rest := rest.push g'
      replaceMainGoal rest.toList
      return
    catch _ => s.restore
  throwError "check_loop_close: no loop head to close"

/-- The simp lemmas of every step of `check_run` besides those of `vm_step`: those of `wallet_run`
(the dispatch, the bounds of slices, a step whatever `max_library_loads` is, `ACCEPT` for any gas
maximum), the fresh instances of `if`, the reading of bits written by `natToBits`, and those of the
`simp` set `check_run_simp` (TvmLean/Proofs/Check/Attr.lean). -/
syntax "check_step" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| check_step [$args,*]) => `(tactic| vm_step [Spec.dictJump, Slice.haveBits,
      Slice.advanceBits, ↓ VmState.stepWith_finish, VmState.stepFinish_continue,
      VmState.stepFinish_halt, VmState.stepFinish_ite, VmState.stepFinish_dite,
      GasLimits.changeLimit_infty_min, TvmLean.Exec.iteFreshInst, TvmLean.Exec.diteFreshInst,
      Array.extract_append, Array.size_append, natToBits_size, Array.append_empty, Array.empty_append,
      extract_natToBits_empty, extract_natToBits_past, extract_natToBits_all, readBits_mkOrdinary,
      readBits_ofCell_mkOrdinary, bitsToNat_natToBits, Nat.mod_eq_of_lt, Int.toNat_natCast_add_one,
      Option.getD_some, Option.getD_none, VmState.retCont, check_run_simp, $args,*])

/-- `vm_step_simp` with the lemmas of `check_step` (a run whose step is written out, after a split). -/
syntax "check_step_simp" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| check_step_simp [$args,*]) => `(tactic| vm_step_simp [Spec.dictJump, Slice.haveBits,
      Slice.advanceBits, ↓ VmState.stepWith_finish, VmState.stepFinish_continue,
      VmState.stepFinish_halt, VmState.stepFinish_ite, VmState.stepFinish_dite,
      GasLimits.changeLimit_infty_min, TvmLean.Exec.iteFreshInst, TvmLean.Exec.diteFreshInst,
      Array.extract_append, Array.size_append, natToBits_size, Array.append_empty, Array.empty_append,
      extract_natToBits_empty, extract_natToBits_past, extract_natToBits_all, readBits_mkOrdinary,
      readBits_ofCell_mkOrdinary, bitsToNat_natToBits, Nat.mod_eq_of_lt, Int.toNat_natCast_add_one,
      Option.getD_some, Option.getD_none, VmState.retCont, check_run_simp, $args,*])

/-- The goal `g` (target `t`) with the `if` `e` of its target (`ite c a b` or `dite c a b`) replaced
by its branch, given `h : c` (`pos`) or `h : ¬c`: the occurrences of `e` abstracted (`kabstract`),
the branch put in their place, the equation of the branch (`if_pos`, `dif_neg`, ...) carried by
`congrArg` — no `simp` over the whole goal, whose run state may be large. -/
def rewriteIte (g : MVarId) (t e : Expr) (h : Expr) (pos : Bool) : MetaM MVarId := g.withContext do
  let isDite := e.isAppOfArity ``dite 5
  let α := e.getArg! 0
  let c := e.getArg! 1
  let inst := e.getArg! 2
  let a := e.getArg! 3
  let b := e.getArg! 4
  let (lemma, branch) :=
    if isDite then
      if pos then (``dif_pos, (mkApp a h).headBeta) else (``dif_neg, (mkApp b h).headBeta)
    else if pos then (``if_pos, a) else (``if_neg, b)
  let eq ← mkAppOptM lemma #[c, inst, h, α, a, b]
  let abst ← kabstract t e
  unless abst.hasLooseBVars do throwError "check_split: the `if` is not in the goal"
  let motive := Expr.lam `x α abst .default
  let t' := abst.instantiate1 branch
  let g' ← mkFreshExprSyntheticOpaqueMVar t' (← g.getTag)
  let pf ← mkAppM ``congrArg #[motive, eq]
  g.assign (mkApp4 (mkConst ``Eq.mpr [levelZero]) t t' pf g')
  return g'.mvarId!

/-- `check_split`: `vm_split` (TvmLean/Proofs/Exec/Tactic.lean) for an `if` of the goal by `rewriteIte`
instead of `split` and `simp`, whose time grows with the whole goal: the condition decided by linear
arithmetic from the context (`assertByOmega?`, with the bounds of the load gas), or the goal split
on it (`byCasesDec` with the `if`'s own instance), each branch with its hypothesis `h`; a check of
the gas split at once, its condition not kept. A `match`, or a condition made of `True` and
`False`, by `vm_split`. -/
elab "check_split" : tactic => do
  evalTactic (← `(tactic| vm_load_bounds))
  withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e ← findSplit? t | throwError "check_split: no `if` or `match` to split"
  let isIf := e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5
  let c := if isIf then e.getArg! 1 else mkConst ``True
  let viaVmSplit := !isIf || c.isConstOf ``True || c.isConstOf ``False ||
    (!c.hasFVar && !c.hasMVar && (c.find? fun x => x.isAppOf ``True || x.isAppOf ``False).isSome)
  if viaVmSplit then
    evalTactic (← `(tactic| vm_split))
    return
  -- a check of the gas (its terms wrap around as `long long`, `int64Wrap`): split without `omega`
  -- (whose work on the wrapped terms is large), the condition not kept. No end of a path depends on
  -- the gas, and a branch out of gas ends its path at once, whether the context rules it out or not
  if (c.find? fun x => x.isAppOf ``GasLimits.gasRemaining || x.isAppOf ``cellLoadGas ||
      x.isAppOf ``int64Wrap).isSome then
    let (sPos, sNeg) ← g.byCasesDec c (e.getArg! 2) `h
    let gPos ← sPos.mvarId.withContext (rewriteIte sPos.mvarId t e (mkFVar sPos.fvarId) true)
    let gNeg ← sNeg.mvarId.withContext (rewriteIte sNeg.mvarId t e (mkFVar sNeg.fvarId) false)
    replaceMainGoal [← gPos.tryClear sPos.fvarId, ← gNeg.tryClear sNeg.fvarId]
    return
  if let some (h, g') ← Exec.assertByOmega? g (mkNot c) then
    let g'' ← g'.withContext (rewriteIte g' t e (mkFVar h) false)
    replaceMainGoal [← g''.tryClear h]
    return
  if let some (h, g') ← Exec.assertByOmega? g c then
    let g'' ← g'.withContext (rewriteIte g' t e (mkFVar h) true)
    replaceMainGoal [← g''.tryClear h]
    return
  let (sPos, sNeg) ← g.byCasesDec c (e.getArg! 2) `h
  let gPos ← sPos.mvarId.withContext (rewriteIte sPos.mvarId t e (mkFVar sPos.fvarId) true)
  let gNeg ← sNeg.mvarId.withContext (rewriteIte sNeg.mvarId t e (mkFVar sNeg.fvarId) false)
  replaceMainGoal [gPos, gNeg]

/-- `check_extra_step [hints]`: steps that modules imported after this one add (`macro_rules`, e.g.
TvmLean/Proofs/Check/Framed.lean: instructions on cells the run does not know), tried first by
`check_one_step`; none here (it fails). -/
syntax "check_extra_step" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

/-- `check_one_step [hints]`: one step of the exploration of the paths of a run: the first `if` of
the goal decided or split (`vm_split`, a branch with contradicting conditions closed), a step of the
run (`check_step`, the code position noted), a fuel that is a variable split, the loop rule at a loop
head with the invariant `SafeActs` of `c5` (`vm_loop_c5`, then a step into the loop), a path back at
a loop head closed by its hypothesis (`check_loop_close`). Fails on the end of a path. -/
syntax "check_one_step" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| check_one_step [$args,*]) => `(tactic| set_option maxRecDepth 100000 in first
      | check_extra_step [$args,*]
      | (check_split <;> try vm_prune_cheap)
      | (vm_not_at_loop_head; check_mark_pos; check_step [$args,*])
      | (vm_not_at_loop_head; vm_fuel <;> try simp only [VmState.runWith_zero, Excno.toInt])
      | (vm_has_run; check_step_simp [$args,*])
      | check_loop_close
      | (vm_has_run; check_mark_pos; vm_loop_c5 SafeActs <;>
          first
            | (simp only [VmState.runWith_zero, Excno.toInt]; done)
            | simp only [VmState.runWith_zero, Excno.toInt]
            | check_step [$args,*]))

/-- `check_run [hints]`: every path of the run in the goal, to its end (`check_one_step` as long as
it applies). -/
syntax "check_run" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| check_run [$args,*]) => `(tactic| repeat' check_one_step [$args,*])

/-! ## The ends of the paths -/

/-- The parts of `Keeps P r`. -/
def keepsParts? (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let t ← instantiateMVars t
  unless t.isAppOfArity ``Keeps 2 do return none
  return some (t.getArg! 0, t.getArg! 1)

/-- Projections of a structure written out, reduced (`st.regs.c4` as the term of the field), with
no other reduction of the field (at most `depth` projections deep). -/
def projTerm (e : Expr) : (depth : Nat := 64) → MetaM Expr
  | 0 => pure e
  | depth + 1 => do
    let e := e.headBeta
    let .const f _ := e.getAppFn | return e
    let some info ← getProjectionFnInfo? f | return e
    let args := e.getAppArgs
    unless args.size == info.numParams + 1 do return e
    let s ← whnfCore (← projTerm args[info.numParams]! depth)
    if s.isAppOf info.ctorName && s.getAppNumArgs > info.numParams + info.i then
      return ← projTerm (s.getArg! (info.numParams + info.i)) depth
    return mkAppN e.getAppFn (args.set! info.numParams s)

/-- `e` with the projections of constructor applications reduced (`(Data.mk a b).b` as `b`): the
parts of a witness that `checkExists` made, as plain unknowns. -/
def reduceCtorProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if let .proj _ i s := x then
      if let .const c _ := s.getAppFn then
        if let some (.ctorInfo cv) := (← getEnv).find? c then
          if s.getAppNumArgs > cv.numParams + i then return .done (s.getArg! (cv.numParams + i))
      return .continue
    let .const f _ := x.getAppFn | return .continue
    let some info ← getProjectionFnInfo? f | return .continue
    let args := x.getAppArgs
    unless args.size == info.numParams + 1 do return .continue
    let s := args[info.numParams]!
    if s.isAppOf info.ctorName && s.getAppNumArgs > info.numParams + info.i then
      return .done (s.getArg! (info.numParams + info.i))
    return .continue)

/-- Finds the witnesses of `∃ x, ...` by unification: a witness of a structure type is its
constructor on new unknowns, the equations among the parts (`∧`) solved by unification
(reducible) first. Returns the parts left. -/
def checkExists (g : MVarId) : (depth : Nat := 256) → MetaM (List MVarId)
  | 0 => pure [g]
  | depth + 1 => g.withContext do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    if ty.isAppOfArity ``Exists 2 then
      let α := ty.getArg! 0
      let p := ty.getArg! 1
      let w ← mkWitness α
      let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp p w).headBeta (← g.getTag)
      g.assign (← mkAppOptM ``Exists.intro #[α, p, w, g'])
      return ← checkExists g'.mvarId! depth
    if ty.isAppOfArity ``And 2 then
      let ga ← mkFreshExprSyntheticOpaqueMVar (ty.getArg! 0) (← g.getTag)
      let gb ← mkFreshExprSyntheticOpaqueMVar (ty.getArg! 1) (← g.getTag)
      g.assign (← mkAppM ``And.intro #[ga, gb])
      let ra ← checkExists ga.mvarId! depth
      let rb ← checkExists gb.mvarId! depth
      return ra ++ rb
    if let some (_, a, b) := ty.eq? then
      let s ← saveState
      -- the parts of a witness as plain unknowns (`reduceCtorProjs`), which unification assigns at
      -- once (through `(Data.mk ?x ...).f + 7` it may unfold for long)
      if ← withReducible (isDefEq (← reduceCtorProjs a) (← reduceCtorProjs b)) then
        g.assign (← mkEqRefl a)
        return []
      s.restore
    return [g]
where
  mkWitness (α : Expr) : MetaM Expr := do
    let α ← whnfR α
    let .const n us := α.getAppFn | return ← mkFreshExprMVar α
    let env ← getEnv
    unless isStructure env n do return ← mkFreshExprMVar α
    if n == ``Nat || n == ``Int then return ← mkFreshExprMVar α
    let some ci := getStructureCtor? env n | return ← mkFreshExprMVar α
    let ctor := mkAppN (mkConst ci.name us) α.getAppArgs
    let ctorTy ← inferType ctor
    let (args, _, _) ← forallMetaTelescopeReducing ctorTy
    return mkAppN ctor args
  getStructureCtor? (env : Environment) (n : Name) : Option ConstructorVal :=
    match env.find? n with
    | some (.inductInfo iv) =>
      match iv.ctors with
      | [c] => match env.find? c with
        | some (.ctorInfo cv) => some cv
        | _ => none
      | _ => none
    | _ => none

/-- The hypotheses of the path, printed. -/
def pathCondition (g : MVarId) : MetaM (Array String) := g.withContext do
  let lctx ← getLCtx
  -- the gas: a hypothesis about the gas limits (`gl`, `gm`, `gc`, the gas of a loop head), the gas
  -- of a load, the gas left, is counted, not printed
  let gasVars ← lctx.foldlM (init := #[]) fun acc d => do
    if [`gl, `gm, `gc].contains d.userName.eraseMacroScopes then return acc.push d.fvarId
    if (← instantiateMVars d.type).isConstOf ``GasLimits then return acc.push d.fvarId
    return acc
  let mut out := #[]
  let mut gas := 0
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    if d.userName == `ih then continue
    if (ty.find? fun x => x.isFVar && gasVars.contains x.fvarId! ||
        x.isAppOf ``cellLoadGas || x.isAppOf ``GasLimits.gasRemaining).isSome then
      gas := gas + 1
      continue
    -- the bound of the jump counter of a loop head, the exit code (in the report anyway)
    if (ty.find? fun x => x.isConstOf ``freeNestedContJump).isSome then continue
    if !ty.hasFVar && (ty.find? fun x => x.isConstOf ``Or).isSome then continue
    let s := toString (← ppExpr ty)
    let s := if s.length > 400 then (s.take 400) ++ " …" else s
    out := out.push (s!"{d.userName.eraseMacroScopes} : {s}".replace "\n" "\n        ")
  if gas > 0 then out := out.push s!"(and {gas} facts about the gas)"
  return out

/-- Where the run in the goal `t` stands, for a path whose run does not reach its end: the current
continuation (its code: the cell, the bit and the instruction there, when the code is closed) and the
instruction left unreduced in the goal (`execInstr i`), if any. -/
def stuckAt (t : Expr) : MetaM (Option String) := do
  let some st := Exec.runState? t | return none
  let cc ← whnfCore (← whnfR (← mkAppM ``VmState.cc #[st]))
  let mut out := ""
  if cc.isAppOfArity ``Continuation.ordinary 4 then
    let code ← whnfR (cc.getArg! 0)
    if Exec.isClosed code then
      try
        let sl ← Exec.evalSlice code
        let instr :=
          if sl.bitsRemaining == 0 then
            if sl.refsRemaining == 0 then "the implicit RET at the end of the cell" else "the implicit JMPREF"
          else match decodeCp0WithBits sl with
            | .ok (i, _, _) => toString i
            | .error _ => "(no instruction decodes there)"
        let cellS ← match ← cellPath? (code.getArg! 0) with
          | some (root, path) => pure s!"cell {root}{String.join (path.map fun k => s!".refs[{k}]!")}"
          | none => pure "a cell the code built (PUSHCONT)"
        out := s!"{cellS}, bit {sl.bitPos}: {instr}"
      catch _ => out := "an ordinary continuation"
    else out := "an ordinary continuation on code that is not known"
  else if let .const n _ := cc.getAppFn then
    out := s!"the continuation {n}"
  if let some i := t.find? (·.isAppOfArity ``execInstr 1) then
    out := out ++ s!"; the step left: {← ppExpr i}"
  return some out

/-- The report of a path that is not proved. -/
def report (g : MVarId) (what : String) (ec : Option Expr) (left : List MVarId) : MetaM MessageData := do
  let pos ← match ← g.withContext (do stuckAt (← instantiateMVars (← g.getType))) with
    | some s => pure s!"{s} (the run is there)"
    | none => describePos (← g.getTag)
  let cond ← pathCondition g
  let ecS ← match ec with
    | some e => pure (toString (← ppExpr e))
    | none => pure "-"
  let mut goals : Array String := #[]
  for g' in left do
    let s := toString (← g'.withContext (ppExpr (← instantiateMVars (← g'.getType))))
    goals := goals.push ((if s.length > 2000 then (s.take 2000) ++ " …" else s).replace "\n" "\n        ")
  let condS := "\n".intercalate (cond.toList.map ("      " ++ ·))
  let goalS := "\n".intercalate (goals.toList.map ("      ⊢ " ++ ·))
  return m!"  path: {what}\n    last step at: {pos}\n    exit code: {ecS}\n    path condition:\n{condS}\n    goal left:\n{goalS}"

/-- Runs the tactic `tac` on the goal `g`: the goals it leaves, or `none` if it fails (or uses more
than `hb` thousand heartbeats, when `hb` is not 0, or logs an error: `done` with goals left logs them
and aborts, which `Tactic.run` takes for success). On failure nothing of the attempt is kept, its
messages neither. -/
def tryTac (g : MVarId) (tac : TSyntax `tactic) (hb : Nat := 0) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  let n0 := (← Core.getMessageLog).toList.length
  -- a run out of heartbeats is a failure of `tac` too
  tryCatchRuntimeEx
    (do
      let run := Term.withoutErrToSorry (Tactic.run g (evalTactic tac))
      let gs ← if hb == 0 then run else
        withCurrHeartbeats <| withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := hb * 1000 }) run
      let msgs := (← Core.getMessageLog).toList
      if (msgs.drop n0).any (·.severity == .error) then
        s.restore
        return none
      return some gs)
    (fun _ => do
      s.restore
      return none)

/-- Closes `g` by the tactic `tac` (as `tryTac`, within `hb` thousand heartbeats) with its proof
checked by the kernel at once, as an auxiliary theorem (`mkAuxTheorem`, not in parallel): a proof the
kernel refuses (one nested too deep) is a failure of `tac`, not an error of the whole theorem later.
Whether it closed `g`. -/
def closeChecked (g : MVarId) (tac : TSyntax `tactic) (hb : Nat) : TacticM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let m ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  let s ← saveState
  match ← tryTac m.mvarId! tac hb with
  | some [] => pure ()
  | _ =>
    s.restore
    return false
  try
    let pf ← instantiateMVars m
    if pf.hasExprMVar then throwError "closeChecked: a part left"
    let c ← withOptions (Elab.async.set · false) (mkAuxTheorem ty pf (zetaDelta := true))
    g.assign c
    return true
  catch _ =>
    s.restore
    return false

/-- The goal `X → P (some c4) ∧ SafeActs c5` of a path that commits (`X` its exit or `COMMIT`): `c5`
by `safe_acts_close`; `P` unfolded, normalized by `simp only` with the hints and the lemmas of
builders and bits, its witnesses found by unification (`checkExists`), the rest by `rfl`,
`assumption`, `omega` (first with the hypotheses that share a term with the goal only,
`check_omega_rel`), `decide`, `simp only` with the hints, an implication by `intros` and `rfl`,
`assumption` or `omega`, each within a budget of heartbeats and its proof checked by the kernel at
once (`closeChecked`). The report if a part is left. -/
def commitPath (g : MVarId) (args : Array Syntax) (what : String)
    (ec : Option Expr) : TacticM (Option MessageData) := do
  let sargs : Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨args⟩
  let (_, g) ← g.intro1
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let_expr And a b := tgt | return some (← report g what ec [g])
  let .app P a1 := a | return some (← report g what ec [g])
  let x := a1.appArg!
  let x' ← projTerm x
  let_expr SafeActs y := b | return some (← report g what ec [g])
  let y' ← projTerm y
  let tag ← g.getTag
  let pa := mkApp P (← mkAppM ``Option.some #[x'])
  let pb ← mkAppM ``SafeActs #[y']
  let gA ← mkFreshExprSyntheticOpaqueMVar pa tag
  let gB ← mkFreshExprSyntheticOpaqueMVar pb tag
  g.assign (← mkAppM ``And.intro #[gA, gB])
  -- the action list
  match ← tryTac gB.mvarId! (← `(tactic| safe_acts_close)) 200000 with
  | some [] => pure ()
  | _ => return some (← report g (what ++ ": the action list is not made of SENDRAWMSG and RAWRESERVE actions")
      ec [gB.mvarId!])
  -- the data
  let mut gP := gA.mvarId!
  let pTy ← instantiateMVars (← gP.getType)
  if let .const n _ := pTy.getAppFn then
    unless n == ``Exists || n == ``And || n == ``Eq do
      if let some pTy' ← unfoldDefinition? pTy then
        gP ← gP.replaceTargetDefEq pTy'.headBeta
  let simpTac ← `(tactic| simp only [Builder.finalize, Builder.storeBits, Builder.empty,
    Array.empty_append, Array.append_empty, Array.append_assoc, Option.some.injEq,
    Int.toNat_natCast_add_one, Int.toNat_natCast, bitsToNat_natToBits, natToBits_size,
    Array.size_append, Array.extract_append, extract_natToBits_empty, extract_natToBits_past,
    extract_natToBits_all, readBits_mkOrdinary, readBits_ofCell_mkOrdinary, Nat.reducePow,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.mod_eq_of_lt, check_close, $sargs,*])
  let gs ← match ← tryTac gP simpTac 200000 with
    | some gs => pure gs
    | none => pure [gP]
  let mut left : List MVarId := []
  for g' in gs do
    for g'' in ← checkExists g' do
      let closers : Array (TSyntax `tactic) := #[← `(tactic| with_reducible rfl), ← `(tactic| assumption),
        ← `(tactic| check_omega_rel), ← `(tactic| (dsimp only; check_omega_rel)),
        ← `(tactic| omega), ← `(tactic| (dsimp only; omega)), ← `(tactic| decide),
        ← `(tactic| (simp only [check_close, $sargs,*]; done)),
        ← `(tactic| (dsimp only; simp only [check_close, $sargs,*]; omega)),
        -- an implication (`d0.active = true → d.active = true` of a field set or kept)
        ← `(tactic| (intros; first | with_reducible rfl | assumption | omega))]
      let mut closed := false
      for c in closers do
        if closed then break
        if ← closeChecked g'' c 50000 then closed := true
      unless closed do
        -- reported with the projections of the witnesses reduced
        match ← tryTac g'' (← `(tactic| dsimp only)) 50000 with
        | some gs' => left := left ++ gs'
        | none => left := left ++ [g'']
  if left.isEmpty then return none
  return some (← report g (what ++ ": the data left does not satisfy the invariant") ec left)

/-- The end of a path, `Keeps P r`: closed, or the report of what is left. -/
def closeLeaf (g : MVarId) (args : Array Syntax) :
    TacticM (Option MessageData) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if (t.find? fun x => x.isAppOfArity ``VmState.runWith 3 || x.isAppOfArity ``VmState.runCont 3).isSome then
    return some (← report g "the run does not reach its end (an instruction without a specification, \
      a recursion, a loop it cannot close, an unknown it cannot split on, a step longer than \
      `check.stepHeartbeats`, the steps of `check.maxSteps` used up)" none [g])
  let some (_, r) ← keepsParts? t | return some (← report g "not the end of a run" none [g])
  let (lemma, ec?) :=
    if r.isAppOfArity ``VmState.haltResult 2 then (``keeps_haltResult, some (r.getArg! 0))
    else if r.isAppOfArity ``StepResult.halt 2 then (``keeps_halt, some (r.getArg! 0))
    else if r.isAppOfArity ``StepResult.continue 1 then (``keeps_continue, none)
    else (Name.anonymous, none)
  if lemma.isAnonymous then return some (← report g "the end of the run is not a halt" none [g])
  let gs ← g.apply (← mkConstWithFreshMVarLevels lemma)
  let gs ← gs.filterM fun g' => return !(← g'.isAssigned)
  -- the state committed before the end (`COMMIT`), then a normal exit
  let some h1 := gs[0]? | return none
  match ← tryTac h1 (← `(tactic| (intro hcm; exact absurd hcm Bool.false_ne_true))) with
  | some [] => pure ()
  | _ => if let some m ← commitPath h1 args "a state committed by COMMIT" ec? then return some m
  let some h2 := gs[1]? | return none
  match ← tryTac h2 (← `(tactic| (intro hex; exfalso; revert hex; decide))) 20000 with
  | some [] => return none
  | _ => commitPath h2 args "a normal exit (the data and actions are committed)" ec?

/-- With the option `check.progress`: the line `s` to the process's standard error itself
(`/dev/stderr`), which the elaborator does not capture as it does `IO.getStderr` for the messages of
a command: seen as the run goes. -/
def progressLine (s : String) : CoreM Unit := do
  if check.progress.get (← getOptions) then
    let h ← IO.FS.Handle.mk "/dev/stderr" .append
    h.putStrLn s!"[check] {s}"
    h.flush

/-- The end of a path (`closeLeaf`), with what its closers left unassigned (nothing, if they did
their work) reported. -/
def finishLeaf (g : MVarId) (args : Array Syntax) : TacticM (Option MessageData) := do
  let t0 ← IO.monoMsNow
  let r ← closeLeaf g args
  progressLine s!"the end of a path at {← describePos (← g.getTag)}: \
    {if r.isSome then "not closed" else "closed"} in {(← IO.monoMsNow) - t0} ms"
  if check.debug.get (← getOptions) then
    logInfo m!"check: the end of a path at {← describePos (← g.getTag)}: \
      {if r.isSome then "not closed" else "closed"}"
  if r.isSome then return r
  let pf ← instantiateMVars (mkMVar g)
  let left ← (← getMVarsNoDelayed pf).filterM fun m => return !(← m.isAssigned)
  if left.isEmpty then return none
  return some (← report g "a part left unproved" none left.toList)

/-- The failure of `check_paths`/`check_finish` with the reports of the paths not proved. -/
def throwReports (fails : Array MessageData) : TacticM Unit := do
  let mut msg := m!"ran_preserves: {fails.size} path(s) where the invariant is not shown"
  for m in fails do msg := msg ++ m!"\n" ++ m
  throwError msg

/-- `check_finish [hints]`: closes the end of every path (`closeLeaf`); fails with the report of
every path it does not close. -/
syntax (name := checkFinish) "check_finish" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

@[tactic checkFinish] def evalCheckFinish : Tactic := fun stx => do
  match stx with
  | `(tactic| check_finish [$args,*]) =>
    let goals ← getUnsolvedGoals
    let mut fails : Array MessageData := #[]
    for g in goals do
      if ← g.isAssigned then continue
      if let some m ← finishLeaf g args.elemsAndSeps then fails := fails.push m
    if fails.isEmpty then setGoals [] else throwReports fails
  | _ => throwUnsupportedSyntax

/-! ## The paths, cut into auxiliary theorems -/

register_option check.cut : Nat := {
  defValue := 40
  descr := "the number of steps (`check_one_step`) after which `check_paths` \
    (TvmLean/Proofs/Check/Tactic.lean) cuts a path: the rest of the run from there is proved as an \
    auxiliary theorem over the hypotheses it uses (0: no cut)"
}


register_option check.stepHeartbeats : Nat := {
  defValue := 0
  descr := "the heartbeats (in thousands) one step of `check_paths` (TvmLean/Proofs/Check/Tactic.lean) \
    may take; a step that takes more ends its path, which is reported where it stands (0: no bound)"
}

register_option check.maxSteps : Nat := {
  defValue := 0
  descr := "the steps `check_paths` (TvmLean/Proofs/Check/Tactic.lean) takes at most, over all paths; \
    a path not ended then is reported where it stands (0: no bound)"
}

/-- Whether the goal is about a run that has not ended (`VmState.runWith`, `VmState.runCont`). -/
def isRunGoal (g : MVarId) : MetaM Bool := do
  let t ← instantiateMVars (← g.getType)
  return (t.find? fun x => x.isAppOfArity ``VmState.runWith 3 || x.isAppOfArity ``VmState.runCont 3).isSome

/-- The run in the goal `g` with its gas and its set of loaded cells made variables (`generalize`),
and the hypotheses about the gas cleared (those of `pathCondition`'s count): a statement that implies
the goal. The gas of a run is a term that grows with every step, its loads nested in the loaded cells
before them (`cellLoadGas (cellsLoadedAfter ...) c`); no path's end depends on it (a run commits or
not whatever its gas, and every gas check is a case anyway), so a cut makes it a variable again. -/
def generalizeGas (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some st := Exec.runState? ty | return g
  unless st.isAppOfArity ``VmState.mk 20 do return g
  let fields := getStructureFields (← getEnv) ``VmState
  let some iGas := fields.idxOf? `gas | return g
  let some iLc := fields.idxOf? `loadedCells | return g
  let mut g := g
  for (i, n) in [(iGas, `gas), (iLc, `loaded)] do
    let ty ← instantiateMVars (← g.getType)
    let some st := Exec.runState? ty | return g
    unless st.isAppOfArity ``VmState.mk 20 do return g
    let e := st.getArg! i
    if e.isFVar then continue
    let (_, g') ← g.generalize #[{ expr := e, xName? := n }]
    g := g'
  -- the hypotheses about the gas before: of the gas limits, a gas variable, a load
  g.withContext do
    let lctx ← getLCtx
    let gasVars ← lctx.foldlM (init := #[]) fun acc d => do
      if [`gl, `gm, `gc].contains d.userName.eraseMacroScopes then return acc.push d.fvarId
      if (← instantiateMVars d.type).isConstOf ``GasLimits then return acc.push d.fvarId
      return acc
    let tgt ← instantiateMVars (← g.getType)
    let mut clear := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      unless ← isProp t do continue
      if (t.find? fun x => x.isFVar && gasVars.contains x.fvarId! &&
          !(tgt.containsFVar x.fvarId!) || x.isAppOf ``cellLoadGas).isSome then
        clear := clear.push d.fvarId
    g.tryClearMany clear

/-- Cuts the path at the goal `g`: its run with the gas and the loaded cells made variables
(`generalizeGas`), over the hypotheses it uses, is proved as an auxiliary theorem (`mkAuxTheorem`,
checked by the kernel on its own) by `sub`, and closes `g`. The reports of `sub` (then `g` is left
open: the whole check fails). Two paths that reach the same statement share its theorem. -/
def cutGoal (g : MVarId) (sub : List MVarId → TacticM (Array MessageData)) :
    TacticM (Array MessageData) := do
  let tag ← g.getTag
  let g ← generalizeGas g
  g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let m ← mkFreshExprSyntheticOpaqueMVar ty tag
  let fails ← sub [m.mvarId!]
  unless fails.isEmpty do return fails
  let t0 ← IO.monoMsNow
  let pf ← instantiateMVars m
  if pf.hasExprMVar then
    let left ← (← getMVarsNoDelayed pf).filterM fun m => return !(← m.isAssigned)
    return #[← report g "a part left unproved" none left.toList]
  -- `zetaDelta`: the let-variables of the context (if any) expanded in the theorem, rather than
  -- sorted out by `Meta.check` of the whole proof (`Closure.preprocess`), which unfolds by `whnf`
  -- what the kernel compares at once and on a long path does not end
  g.assign (← mkAuxTheorem ty pf (zetaDelta := true))
  progressLine s!"a cut at {← describePos tag}: its theorem made in {(← IO.monoMsNow) - t0} ms"
  return #[]

/-- Every path from the goals `goals` (`check_one_step` as `step`), each end closed (`finishLeaf`);
a path is cut (`cutGoal`) every `cut` steps, at most `depth` cuts deep; at most `budget` steps in
all. The reports of the paths not proved. -/
def explore (step : TSyntax `tactic) (args : Array Syntax) (cut : Nat) (budget : IO.Ref Nat) :
    (depth : Nat) → List MVarId → TacticM (Array MessageData)
  | depth, goals => do
    -- the goals to explore, the last first, each with its steps since the last cut
    let mut work : Array (MVarId × Nat) := goals.toArray.reverse.map (·, 0)
    let mut fails : Array MessageData := #[]
    let progress := check.progress.get (← getOptions)
    let stepHb := check.stepHeartbeats.get (← getOptions)
    let t0 ← IO.monoMsNow
    for i in [0:100000000] do
      let some (g, n) := work.back? | break
      work := work.pop
      if ← g.isAssigned then continue
      if progress then
        progressLine s!"{(← IO.monoMsNow) - t0} ms, step {i}, depth {depth}, {work.size + 1} open: \
          {← describePos (← g.getTag)}"
      if cut != 0 && n ≥ cut then
        match depth with
        | d + 1 =>
          if ← isRunGoal g then
            fails := fails ++ (← cutGoal g (explore step args cut budget d))
            continue
        | 0 => pure ()
      -- out of steps (`check.maxSteps`): the path is reported where it stands
      let b ← budget.get
      if b == 0 then
        if let some m ← finishLeaf g args then fails := fails.push m
        continue
      budget.set (b - 1)
      match ← tryTac g step stepHb with
      | some gs => work := work ++ (gs.reverse.map (·, n + 1)).toArray
      | none =>
        if progress && (← isRunGoal g) then
          -- the goal of a path whose run stops before its end, in full
          progressLine s!"the run stops here:\n{← ppGoal g}"
        if let some m ← finishLeaf g args then fails := fails.push m
    return fails

/-- `check_paths [hints]`: every path of the run in the goal to its end and every end closed
(`explore`: `check_one_step`, `finishLeaf`), the paths cut every `check.cut` steps into auxiliary
theorems; fails with the report of every path not proved. -/
syntax (name := checkPaths) "check_paths" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

@[tactic checkPaths] def evalCheckPaths : Tactic := fun stx => do
  match stx with
  | `(tactic| check_paths [$args,*]) =>
    let step ← `(tactic| check_one_step [$args,*])
    let maxSteps := check.maxSteps.get (← getOptions)
    let budget ← IO.mkRef (if maxSteps == 0 then 1000000000 else maxSteps)
    let fails ← explore step args.elemsAndSeps (check.cut.get (← getOptions)) budget 10000
      (← getUnsolvedGoals)
    if fails.isEmpty then setGoals [] else throwReports fails
  | _ => throwUnsupportedSyntax

/-- `check_destruct h [hints]`: unfolds the hypothesis `h` (the invariant of the data) and the
definitions among the hints, takes the hypotheses apart (`destructStep`). -/
elab "check_destruct " h:ident " [" args:Lean.Parser.Tactic.simpArg,* "]" : tactic => withMainContext do
  let mut names : Array Name := #[]
  for a in args.getElems do
    if let some id := a.raw.find? (·.isIdent) then
      try
        let n ← realizeGlobalConstNoOverload id
        if let some (.defnInfo _) := (← getEnv).find? n then names := names.push n
      catch _ => pure ()
  let g ← getMainGoal
  let some d := (← getLCtx).findFromUserName? h.getId | throwError "check_destruct: no {h}"
  let mut g := g
  if let some ty' ← (do
      let ty ← instantiateMVars d.type
      let .const n _ := ty.getAppFn | pure none
      unless n == ``Exists || n == ``And || n == ``Eq do
        if let some ty' ← unfoldDefinition? ty then return some ty'.headBeta
      pure none) then
    g ← g.replaceLocalDeclDefEq d.fvarId ty'
  for _ in [0:500] do
    match ← destructStep g names #[] with
    | some g' => g := g'
    | none => break
  replaceMainGoal [g]

end TvmLean.Check

namespace TvmLean

/-- `ran_case [hints]`: one statement `RunsKeep C P stack G` (`TvmLean/Proofs/Check/Tactic.lean`):
the invariant taken apart, the start state written out, the run to the end of every path, every
end closed or reported. -/
syntax (name := ranCase) "ran_case" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

open Lean Elab Tactic in
@[tactic ranCase] def evalRanCase : Tactic := fun stx => do
  match stx with
  | `(tactic| ran_case [$args,*]) =>
    -- the binders of the statement (the message or tick-tock, the invariant's parameters) and of
    -- `RunsKeep`, by names a report can show
    let mut g ← getMainGoal
    for _ in [0:64] do
      unless (← instantiateMVars (← g.getType)).isForall do break
      let (_, g') ← g.intro1P
      g := g'
    replaceMainGoal [g]
    evalTactic (← `(tactic| unfold TvmLean.Check.RunsKeep))
    let (_, gr) ← (← getMainGoal).introN 13
      [`data, `hP, `c7, `gl, `gm, `gc, `gv, `hgv, `libs, `mdd, `mll, `lc, `fuel]
    replaceMainGoal [gr]
    let hP := mkIdent `hP
    let hgv := mkIdent `hgv
    evalTactic (← `(tactic| try dsimp only at $hgv:ident))
    evalTactic (← `(tactic| check_destruct $hP [$args,*]))
    evalTactic (← `(tactic| try simp only [Nat.reducePow] at *))
    evalTactic (← `(tactic| simp only [TvmLean.Check.start, computePhaseInit, VmState.initial,
      computePhaseStack, TvmLean.Check.tickTockStack, Regs.initial, Option.getD_some, reduceIte, $args,*]))
    evalTactic (← `(tactic| check_paths [$hgv:ident, $args,*]))
  | _ => throwUnsupportedSyntax

/-- `ran_preserves [hints]`: the obligation of `Reachable.code_fixed` for a closed code literal and
an invariant of the data (`TvmLean.Check.ran_preserves_of`), each kind of transaction by `ran_case`;
fails with the reports of all the kinds that fail. -/
syntax (name := ranPreserves) "ran_preserves" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

open Lean Elab Tactic in
@[tactic ranPreserves] def evalRanPreserves : Tactic := fun stx => do
  match stx with
  | `(tactic| ran_preserves [$args,*]) =>
    evalTactic (← `(tactic| refine TvmLean.Check.ran_preserves_of (by rfl) ?_ ?_ ?_ ?_ ?_ ?_))
    let kinds := #["an external message, global version from 4", "an external message, global version below 4",
      "an internal message, global version from 4", "an internal message, global version below 4",
      "tick-tock, global version from 4", "tick-tock, global version below 4"]
    let goals ← getGoals
    let mut fails : Array MessageData := #[]
    for (g, i) in goals.zipIdx do
      setGoals [g]
      try
        Term.withoutErrToSorry (evalTactic (← `(tactic| ran_case [$args,*])))
        unless (← getUnsolvedGoals).isEmpty do throwError "goals left"
      catch ex =>
        fails := fails.push (m!"{kinds[i]?.getD ""}:\n" ++ ex.toMessageData)
    setGoals []
    unless fails.isEmpty do
      let mut msg := m!"ran_preserves: the invariant is not shown for {fails.size} kind(s) of transaction"
      for m in fails do msg := msg ++ m!"\n" ++ m
      throwError msg
  | _ => throwUnsupportedSyntax

end TvmLean

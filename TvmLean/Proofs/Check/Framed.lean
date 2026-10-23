import TvmLean.Proofs.Check.Tactic
import TvmLean.Proofs.Check.Attr
import TvmLean.Proofs.Check.Forget
import TvmLean.Proofs.Exec.Framed
import TvmLean.Proofs.Exec.FramedDict
import TvmLean.Proofs.Exec.Spec.MsgAddr
import TvmLean.Proofs.Exec.Spec.MsgExt
import TvmLean.Proofs.Exec.Spec.ArithExt
import TvmLean.Proofs.Exec.Spec.CellExt
import TvmLean.Proofs.Exec.Spec.StackExt
import TvmLean.Proofs.Exec.Spec.Tuple

/-!
# Checking an invariant over all transactions: cells the run does not know

`ran_case` (TvmLean/Proofs/Check/Tactic.lean) runs a contract from every state the compute phase may
start it from. The message cell, the body and what the code loads from them are variables: the run
knows nothing of them. The steps here (`check_extra_step`, tried before the others of
`check_one_step`) run the instructions that look into such cells by what holds for every cell, the
framed instructions of TvmLean/Proofs/Exec/Framed.lean and FramedDict.lean:

* `CTOS` of a cell whose `special` flag the run cannot tell (`vm_ctos_any`): a slice, any, or an
  exception (cell_und of a library cell not found, out of gas); the gas and the loaded cells after it
  are any;
* `DICTIGET`/`DICTUGET` on a dictionary the run does not know (`vm_dict_get_any`): a value found, any,
  or none, or an exception;
* `CTOS` of a cell that is ordinary by definition but not written as `Cell.mkOrdinary` (`encode d` of
  the data the invariant gives, the data a run wrote): its `special` flag, `false`, as a hypothesis,
  for the specification `Spec.ctos`.

With the specifications loaded here, `LDMSGADDR` reads any slice (`Spec.ldMsgAddr_any`: the address
or cell_und) and `RAWRESERVE` with a mode below 16 runs in every global version
(`Spec.rawReserve_le15`).

The path that a framed instruction ends with an exception commits nothing: its `Keeps` holds
(`keeps_of_not_committed`).

Besides:
* an exception an instruction raises is kept as `VmState.raiseDead` (the lemma
  `VmState.instrEnd_error_dead` in the `simp` set `check_run_simp` of the steps): with the handler
  `excQuit` and nothing committed the path commits nothing and is closed at once (`check_dead`),
  else the exception is expanded (`check_undead`);
* the terms a step leaves that `check_step` does not reduce are written out (`check_unstick`: the
  call of `IF`/`IFELSE`, the gas of a tuple, a cell the code built);
* `c7` that a step wrote (`RAND`) is made a variable again (`check_forget_c7`,
  TvmLean/Proofs/Check/Forget.lean).
-/

namespace TvmLean.Check

open Lean Meta Elab Tactic

/-- A run's result that has committed nothing keeps any invariant. -/
theorem keeps_of_not_committed {P : Option Cell → Prop} (r : StepResult) (h : r.state.cstate.committed = false) :
    Keeps P r := by
  intro h'
  rw [h] at h'
  cases h'

/-- The instruction the run of the goal `t` (`Keeps P (VmState.runWith exec fuel S)`, no `if` left
around the run) is about to run, decoded from its code, which must be closed; with the state `S`. No
proof made. -/
def nextInstr? (t : Expr) : MetaM (Option (Instr × Expr)) := do
  unless t.isAppOfArity ``Keeps 2 && (t.getArg! 1).isAppOfArity ``VmState.runWith 3 do return none
  let S := (t.getArg! 1).getArg! 2
  unless S.isAppOfArity ``VmState.mk 20 do return none
  let cc ← whnfCore (← whnfR (← mkAppM ``VmState.cc #[S]))
  unless cc.isAppOfArity ``Continuation.ordinary 4 do return none
  let code := cc.getArg! 0
  unless Exec.isClosed code do return none
  let sv ← Exec.evalSlice code
  if sv.bitsRemaining == 0 then return none
  match decodeCp0WithBits sv with
  | .ok (i, _, _) => return some (i, S)
  | .error _ => return none

/-- The top `k + 1`-th entry of the stack of the state `S` (written out as `Array.push`es). -/
def stackEntry? (S : Expr) (k : Nat) : MetaM (Option Expr) := do
  let mut stk ← whnfR (← mkAppM ``VmState.stack #[S])
  for _ in [0:k] do
    unless stk.isAppOfArity ``Array.push 3 do return none
    stk ← whnfR (stk.getArg! 1)
  unless stk.isAppOfArity ``Array.push 3 do return none
  return some (← whnfR (stk.getArg! 2))

/-- The `special` flag of the cell `c` when the definitions tell it (`Cell.mkOrdinary`, a definition
that unfolds to it): `some b`; `none` for a cell the run does not know. -/
def specialOf? (c : Expr) : MetaM (Option Bool) := do
  if Exec.isClosed c then return none
  let e ← withTransparency .default <| whnf (mkApp (mkConst ``Cell.special) c)
  if e.isConstOf ``Bool.false then return some false
  if e.isConstOf ``Bool.true then return some true
  return none

/-- `CTOS`/`XCTOS` (`i`) from the state `S` of the goal `g` on a cell that is ordinary by definition
(its `special` flag reduces to `false`) but not written as `Cell.mkOrdinary`: the hypothesis
`c.special = false` added (by `rfl`), so that the specification `Spec.ctos` applies. Fails if the
hypothesis is there already, or for any other instruction or cell. -/
def knownSpecial (g : MVarId) (i : Instr) (S : Expr) : TacticM Unit := g.withContext do
  unless i matches .ctos || i matches .xctos do throwError "check_known_special: not CTOS"
  let some top ← stackEntry? S 0 | throwError "check_known_special: the stack"
  unless top.isAppOfArity ``Value.cell 1 do throwError "check_known_special: no cell"
  let c := top.appArg!
  if c.isAppOf ``Cell.mkOrdinary then throwError "check_known_special: written as mkOrdinary"
  let some false ← specialOf? c | throwError "check_known_special: not known to be ordinary"
  let ty ← mkEq (mkApp (mkConst ``Cell.special) c) (mkConst ``Bool.false)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← withReducible (isDefEq (← instantiateMVars d.type) ty) then
      throwError "check_known_special: known already"
  let pf ← mkEqRefl (mkConst ``Bool.false)
  let (_, g') ← (← g.assert `hspecial ty pf).intro1P
  replaceMainGoal [g']

/-- `CTOS` (`i`) from the state `S` on a cell whose `special` flag the run cannot tell (a cell of the
message, of the body): by `vm_ctos_any`, the run from the state after it with any slice, gas, loaded
cells and libraries (the path of an exception commits nothing). -/
def ctosAny (i : Instr) (S : Expr) : TacticM Unit := withMainContext do
  unless i matches .ctos do throwError "check_ctos_any: not CTOS"
  let some top ← stackEntry? S 0 | throwError "check_ctos_any: the stack"
  unless top.isAppOfArity ``Value.cell 1 do throwError "check_ctos_any: no cell"
  if (← specialOf? top.appArg!).isSome || Exec.isClosed top.appArg! then
    throwError "check_ctos_any: a cell the run knows"
  evalTactic (← `(tactic| vm_ctos_any))
  evalTactic (← `(tactic| (· intro r h; exact keeps_of_not_committed r h)))
  evalTactic (← `(tactic| (intro sl g lc ll fuel; simp only [Framed.after]; vm_clear_unused)))

/-- `DICTIGET`/`DICTUGET` (`i`, not `REF`) from the state `S` on a dictionary the run does not know:
by `vm_dict_get_any`, the runs with a value found (any slice) and with none. -/
def dictGetAny (i : Instr) (S : Expr) : TacticM Unit := withMainContext do
  unless i matches .dictGet true _ false do throwError "check_dict_get_any: not DICTIGET/DICTUGET"
  let some root ← stackEntry? S 1 | throwError "check_dict_get_any: the stack"
  unless root.isAppOfArity ``Value.cell 1 do throwError "check_dict_get_any: no cell"
  if Exec.isClosed root.appArg! then throwError "check_dict_get_any: a dictionary the run knows"
  evalTactic (← `(tactic| vm_dict_get_any))
  evalTactic (← `(tactic| (· intro r h; exact keeps_of_not_committed r h)))
  evalTactic (← `(tactic| all_goals (intros; simp only [Framed.after]; vm_clear_unused)))

/-- The instruction the run in the main goal is about to run (`nextInstr?`), with the state. -/
def mainNextInstr (what : String) : TacticM (MVarId × Instr × Expr) := withMainContext do
  let g ← getMainGoal
  let some (i, S) ← nextInstr? (← instantiateMVars (← g.getType)) | throwError "{what}: no instruction"
  return (g, i, S)

/-- `check_known_special`: `knownSpecial` on the instruction the run is about to run. -/
elab "check_known_special" : tactic => do
  let (g, i, S) ← mainNextInstr "check_known_special"
  knownSpecial g i S

/-- `check_ctos_any`: `ctosAny` on the instruction the run is about to run. -/
elab "check_ctos_any" : tactic => do
  let (_, i, S) ← mainNextInstr "check_ctos_any"
  ctosAny i S

/-- `check_dict_get_any`: `dictGetAny` on the instruction the run is about to run. -/
elab "check_dict_get_any" : tactic => do
  let (_, i, S) ← mainNextInstr "check_dict_get_any"
  dictGetAny i S

/-- `check_framed`: the instruction the run is about to run decoded once, then `knownSpecial`,
`ctosAny` or `dictGetAny`, whichever applies. Fails for any other instruction. -/
elab "check_framed" : tactic => do
  let (g, i, S) ← mainNextInstr "check_framed"
  match i with
  | .ctos =>
    let s ← saveState
    try knownSpecial g i S
    catch _ =>
      s.restore
      ctosAny i S
  | .xctos => knownSpecial g i S
  | .dictGet true _ false => dictGetAny i S
  | _ => throwError "check_framed: not an instruction on a cell the run does not know"

/-! ## An exception that ends the run

With `VmState.instrEnd_error_dead` among the lemmas of the steps (`check_run_simp`), an exception an
instruction raises is kept as `VmState.raiseDead` (TvmLean/Proofs/Exec/Framed.lean) instead of being
expanded (the handler's state, its gas checks, the step of `excQuit`). -/

/-- Whether `r` is the run on from an exception kept as `VmState.raiseDead`
(`VmState.runCont exec n (VmState.stepFinish exec S (st.raiseDead x))`). -/
def isDeadRun (r : Expr) : Bool :=
  r.isAppOfArity ``VmState.runCont 3 && (r.getArg! 2).isAppOfArity ``VmState.stepFinish 3 &&
    ((r.getArg! 2).getArg! 2).isAppOfArity ``VmState.raiseDead 2

/-- `check_dead`: the run in the goal goes on from an exception that the handler `excQuit` ends with
nothing committed (`Framed.dead_stepFinish_raiseDead`: `c2` is `excQuit`, nothing committed, an
exception code of at least 2, no library refused or noted): it commits nothing. Fails on any other
goal, or when one of those does not hold by `rfl`/`decide`. -/
elab "check_dead" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Keeps 2 && isDeadRun (t.getArg! 1) do throwError "check_dead: not a run from an exception"
  evalTactic (← `(tactic|
    exact keeps_of_not_committed _ (Framed.dead_stepFinish_raiseDead _ _ _ rfl rfl (by decide) rfl rfl _)))

/-- `check_undead`: an exception kept as `VmState.raiseDead` that `check_dead` does not close (a
handler other than `excQuit`, a state committed by `COMMIT`), once no `if` is left to split before
it: `VmState.raiseException`, which the next steps expand. Fails if there is none. -/
elab "check_undead" : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless (t.find? (·.isAppOfArity ``VmState.raiseDead 2)).isSome do throwError "check_undead: no exception"
  unless (t.isAppOfArity ``Keeps 2 && isDeadRun (t.getArg! 1)) || (← findSplit? t).isNone do
    throwError "check_undead: an `if` to split first"
  evalTactic (← `(tactic| simp only [VmState.raiseDead]))

/-! ## Terms a step leaves that `check_step` does not reduce -/

/-- `VmState.callTo` (the call of `IF`, `IFELSE`, `IFREFELSE`, `IFJMPREF`...) is the call `VM.call`
makes: `c0` becomes the return continuation `VmState.retCont`. -/
theorem callTo_retCont (st : VmState) (k : Continuation) :
    st.callTo k = { st with regs := { st.regs with c0 := st.retCont }, cc := k } := by
  unfold VmState.callTo VmState.callToWithFrame VmState.retCont
  cases st.cc <;> rfl

/-- The heads of the terms `check_unstick` rewrites. -/
def unstickHeads : Array Name := #[``VmState.callTo, ``VmState.consumeTupleGas, ``Builder.finalize]

/-- `check_unstick`: a goal whose run is stuck on a term that `check_step` does not reduce, or holds
a term the next steps read better written out: a call `VmState.callTo`, the gas of a tuple
`VmState.consumeTupleGas`, a cell the code built `Builder.finalize` (as `Cell.mkOrdinary` of its bits
and references: its `CTOS` by `ctos_mkOrdinary`, its references and bits read by the lemmas of
`Cell.mkOrdinary`). The term rewritten; fails if there is none (a quick search of the goal first). -/
elab "check_unstick" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless (t.find? fun x => unstickHeads.any (x.isAppOf ·)).isSome do throwError "check_unstick: nothing"
  evalTactic (← `(tactic| simp only [TvmLean.Check.callTo_retCont, VmState.retCont, VmState.consumeTupleGas,
    Builder.finalize, Builder.storeBits, Builder.empty, Array.empty_append, Array.append_empty,
    VM.getElem!_singleton, Array.push_empty]))

end TvmLean.Check

-- the action list a step leaves (`#[].push`), for the ends of the paths
attribute [check_close] Array.push_empty

-- an exception an instruction raises kept under a name (`check_dead`)
attribute [check_run_simp ↓] TvmLean.VmState.instrEnd_error_dead

namespace TvmLean

macro_rules
  | `(tactic| check_extra_step [$_args,*]) => `(tactic| first
      | check_dead
      | check_undead
      | check_unstick
      | check_forget_c7
      | check_framed)

end TvmLean

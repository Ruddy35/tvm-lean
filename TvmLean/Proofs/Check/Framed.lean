import TvmLean.Proofs.Check.Tactic
import TvmLean.Proofs.Check.Attr
import TvmLean.Proofs.Check.Forget
import TvmLean.Proofs.Exec.Framed
import TvmLean.Proofs.Exec.FramedDict
import TvmLean.Proofs.Exec.FramedConfig
import TvmLean.Proofs.Exec.FramedAddr
import TvmLean.Proofs.Exec.FramedStdAddr
import TvmLean.Proofs.Exec.FramedDictMinMax
import TvmLean.Proofs.Exec.FramedDictNear
import TvmLean.Proofs.Exec.FramedDictSet

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
* `CONFIGPARAM`/`CONFIGOPTPARAM` on a configuration the run does not know (`vm_config_param_any`,
  TvmLean/Proofs/Exec/FramedConfig.lean): the parameter's cell, any, or none, or an exception;
* `REWRITEVARADDR`/`REWRITEVARADDRQ` on a slice the run does not know (`vm_rewrite_var_addr_any`,
  TvmLean/Proofs/Exec/FramedAddr.lean): any workchain and address, or none, or an exception;
* `REWRITESTDADDR`/`REWRITESTDADDRQ` likewise (`vm_rewrite_std_addr_any`,
  TvmLean/Proofs/Exec/FramedStdAddr.lean): any workchain and address as integers, or none;
* `DICT{,I,U}{,REM}{MIN,MAX}{,REF}` on a dictionary the run does not know (`vm_dict_minmax_any`,
  TvmLean/Proofs/Exec/FramedDictMinMax.lean): a value and a key found, any (and for `REM` any new
  root), or none, or an exception;
* `DICT{,I,U}GET{NEXT,PREV}{,EQ}` on a dictionary the run does not know (`vm_dict_near_any`,
  TvmLean/Proofs/Exec/FramedDictNear.lean): a value and a key found, any, or none, or an exception;
* `DICT{,I,U}SET{,REF,B}` (any mode) and `DICT{,I,U}REPLACEB` on a dictionary the run does not know
  and of which no `Dict.WF` is known (`vm_dict_set_any`, TvmLean/Proofs/Exec/FramedDictSet.lean): a
  new root, null or any cell, and the flag (any integer) of `ADD`/`REPLACE`, or an exception;
* `CTOS` of a cell that is ordinary by definition but not written as `Cell.mkOrdinary` (`encode d` of
  the data the invariant gives, the data a run wrote): its `special` flag, `false`, as a hypothesis,
  for the specification `Spec.ctos`.

With the specifications that TvmLean/Proofs/Check/Tactic.lean loads, `LDMSGADDR` reads any slice
(`Spec.ldMsgAddr_any`: the address or cell_und) and `RAWRESERVE` with a mode below 16 runs in every
global version (`Spec.rawReserve_le15`).

The path that a framed instruction ends with an exception commits nothing: its `Keeps` holds
(`keeps_of_not_committed`), and its `KeepsActs` (`keepsActs_of_not_committed`, the runs of a
contract whose code may change).

Besides:
* an exception an instruction raises is kept as `VmState.raiseDead` (the lemma
  `VmState.instrEnd_error_dead` in the `simp` set `check_run_simp` of the steps): with the handler
  `excQuit` and nothing committed the path commits nothing and is closed at once (`check_dead`),
  else the exception is expanded (`check_undead`);
* the terms a step leaves that `check_step` does not reduce are written out (`check_unstick`: the
  gas of a tuple, a cell the code built);
* `c7` that a step wrote (`RAND`) is made a variable again (`check_forget_c7`,
  TvmLean/Proofs/Check/Forget.lean);
* a read of an unsigned integer that a handler lifts from `Except` into the VM (the storage prices
  that `GETSTORAGEFEE` reads from the unpacked configuration) is written out
  (`Spec.run_takeBitsAsNatCellUnd` in `check_run_simp`): the value and the rest, or cell_und, an
  `if` the run splits on.
-/

namespace TvmLean.Check

open Lean Meta Elab Tactic

/-- A run's result that has committed nothing keeps any invariant. -/
theorem keeps_of_not_committed {P : Option Cell → Prop} (r : StepResult) (h : r.state.cstate.committed = false) :
    Keeps P r := by
  intro h'
  rw [h] at h'
  cases h'

/-- `keeps_of_not_committed` for `KeepsActs`. -/
theorem keepsActs_of_not_committed {P : Option Cell → Prop} {A : Cell → Prop} (r : StepResult)
    (h : r.state.cstate.committed = false) : KeepsActs P A r := by
  intro h'
  rw [h] at h'
  cases h'

/-- The instruction the run of the goal `t` (`Keeps P (VmState.runWith exec fuel S)` or `KeepsActs P A
(VmState.runWith exec fuel S)`, no `if` left around the run) is about to run, decoded from its code,
which must be closed; with the state `S`. No proof made. -/
def nextInstr? (t : Expr) : MetaM (Option (Instr × Expr)) := do
  let some (_, r) ← keepsParts? t | return none
  unless r.isAppOfArity ``VmState.runWith 3 do return none
  let S := r.getArg! 2
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
  evalTactic (← `(tactic| (· intro r h; first
    | exact keeps_of_not_committed r h | exact keepsActs_of_not_committed r h)))
  evalTactic (← `(tactic| (intro sl g lc ll fuel hfuel; simp only [Framed.after]; vm_clear_unused)))

/-- `DICTIGET`/`DICTUGET` (`i`, not `REF`) from the state `S` on a dictionary the run does not know:
by `vm_dict_get_any`, the runs with a value found (any slice) and with none. -/
def dictGetAny (i : Instr) (S : Expr) : TacticM Unit := withMainContext do
  unless i matches .dictGet true _ false do throwError "check_dict_get_any: not DICTIGET/DICTUGET"
  let some root ← stackEntry? S 1 | throwError "check_dict_get_any: the stack"
  unless root.isAppOfArity ``Value.cell 1 do throwError "check_dict_get_any: no cell"
  if Exec.isClosed root.appArg! then throwError "check_dict_get_any: a dictionary the run knows"
  evalTactic (← `(tactic| vm_dict_get_any))
  evalTactic (← `(tactic| (· intro r h; first
    | exact keeps_of_not_committed r h | exact keepsActs_of_not_committed r h)))
  evalTactic (← `(tactic| all_goals (intros; simp only [Framed.after]; vm_clear_unused)))

/-- `CONFIGPARAM`/`CONFIGOPTPARAM` (`i`) on a configuration the run does not know (`c7` any): by
`vm_config_param_any`, the runs with the parameter found (any cell) and with none. -/
def configParamAny (i : Instr) : TacticM Unit := withMainContext do
  unless i matches .tonEnvOp (.configParam _) do throwError "check_framed: not CONFIGPARAM"
  evalTactic (← `(tactic| vm_config_param_any))
  evalTactic (← `(tactic| (· intro r h; first
    | exact keeps_of_not_committed r h | exact keepsActs_of_not_committed r h)))
  evalTactic (← `(tactic| intro s' g lc ll fuel hfuel h))
  evalTactic (← `(tactic| simp only [Framed.ConfigOk] at h))
  -- `rfl` of a pattern by `mkIdent`: written in the quotation it is a hygienic name, which `rcases`
  -- takes for a new hypothesis, not for the substitution
  let rflI := mkIdent `rfl
  evalTactic (← `(tactic| rcases h with $rflI:ident | ⟨c, $rflI:ident⟩))
  evalTactic (← `(tactic| all_goals (simp only [Framed.after]; vm_clear_unused)))

/-- `REWRITEVARADDR`/`REWRITEVARADDRQ` (`i`) from the state `S` on a slice the run does not know (a
part of the message): by `vm_rewrite_var_addr_any`, the runs with any workchain and address (and,
for `REWRITEVARADDRQ`, with none). -/
def rewriteVarAddrAny (i : Instr) (S : Expr) : TacticM Unit := withMainContext do
  unless i matches .tonEnvOp (.rewriteVarAddr _) do throwError "check_framed: not REWRITEVARADDR"
  let some top ← stackEntry? S 0 | throwError "check_framed: the stack"
  unless top.isAppOfArity ``Value.slice 1 do throwError "check_framed: no slice"
  if Exec.isClosed top.appArg! then throwError "check_framed: a slice the run knows"
  evalTactic (← `(tactic| vm_rewrite_var_addr_any))
  evalTactic (← `(tactic| (· intro r h; first
    | exact keeps_of_not_committed r h | exact keepsActs_of_not_committed r h)))
  evalTactic (← `(tactic| intro s' g lc ll fuel hfuel h))
  evalTactic (← `(tactic| simp only [Framed.RewriteOk] at h))
  let rflI := mkIdent `rfl
  evalTactic (← `(tactic| first | obtain ⟨wc, a, $rflI:ident⟩ := h | rcases h with ⟨wc, a, $rflI:ident⟩ | $rflI:ident))
  evalTactic (← `(tactic| all_goals (simp only [Framed.after]; vm_clear_unused)))

/-- `REWRITESTDADDR`/`REWRITESTDADDRQ` (`i`) from the state `S` on a slice the run does not know
(the sender's address): by `vm_rewrite_std_addr_any`, the runs with any workchain and address (and,
for `REWRITESTDADDRQ`, with none). -/
def rewriteStdAddrAny (i : Instr) (S : Expr) : TacticM Unit := withMainContext do
  unless i matches .tonEnvOp (.rewriteStdAddr _) do throwError "check_framed: not REWRITESTDADDR"
  let some top ← stackEntry? S 0 | throwError "check_framed: the stack"
  unless top.isAppOfArity ``Value.slice 1 do throwError "check_framed: no slice"
  if Exec.isClosed top.appArg! then throwError "check_framed: a slice the run knows"
  evalTactic (← `(tactic| vm_rewrite_std_addr_any))
  evalTactic (← `(tactic| (· intro r h; first
    | exact keeps_of_not_committed r h | exact keepsActs_of_not_committed r h)))
  evalTactic (← `(tactic| intro s' g lc ll fuel hfuel h))
  evalTactic (← `(tactic| simp only [Framed.RewriteStdOk] at h))
  -- `rfl` by `mkIdent`, as in `rewriteVarAddrAny`: a hygienic `rfl` would name a hypothesis
  let rflI := mkIdent `rfl
  evalTactic (← `(tactic| first | obtain ⟨wc, a, $rflI:ident⟩ := h | rcases h with ⟨wc, a, $rflI:ident⟩ | $rflI:ident))
  evalTactic (← `(tactic| all_goals (simp only [Framed.after]; vm_clear_unused)))

/-- `DICT*MIN`/`MAX` (`i`, any form) from the state `S` on a dictionary the run does not know: by
`vm_dict_minmax_any`, the runs with the minimum or maximum found (any value and key, and for `REM`
any new root, null or a cell) and with none. -/
def dictMinMaxAny (i : Instr) (S : Expr) : TacticM Unit := withMainContext do
  let .dictGetMinMax args5 := i | throwError "check_framed: not DICT*MIN/MAX"
  let some root ← stackEntry? S 1 | throwError "check_framed: the stack"
  unless root.isAppOfArity ``Value.cell 1 do throwError "check_framed: no cell"
  if Exec.isClosed root.appArg! then throwError "check_framed: a dictionary the run knows"
  evalTactic (← `(tactic| vm_dict_minmax_any))
  evalTactic (← `(tactic| (· intro r h; first
    | exact keeps_of_not_committed r h | exact keepsActs_of_not_committed r h)))
  evalTactic (← `(tactic| intro s' g lc ll fuel hfuel h))
  evalTactic (← `(tactic| try simp only [Framed.MinMaxOk] at h))
  let rflI := mkIdent `rfl
  if args5 &&& 16 == 16 then
    evalTactic (← `(tactic|
      rcases h with ⟨v, k, $rflI:ident⟩ | ⟨r, v, k, $rflI:ident⟩ | $rflI:ident | ⟨r, $rflI:ident⟩))
  else
    evalTactic (← `(tactic| rcases h with ⟨v, k, $rflI:ident⟩ | $rflI:ident))
  evalTactic (← `(tactic| all_goals (simp only [Framed.after]; vm_clear_unused)))

/-- `DICT*GETNEXT`/`PREV` (`i`, any form) from the state `S` on a dictionary the run does not know: by
`vm_dict_near_any`, the runs with a key found (any value and key) and with none. -/
def dictNearAny (i : Instr) (S : Expr) : TacticM Unit := withMainContext do
  unless i matches .dictGetNear _ do throwError "check_framed: not DICT*GETNEXT/PREV"
  let some root ← stackEntry? S 1 | throwError "check_framed: the stack"
  unless root.isAppOfArity ``Value.cell 1 do throwError "check_framed: no cell"
  if Exec.isClosed root.appArg! then throwError "check_framed: a dictionary the run knows"
  evalTactic (← `(tactic| vm_dict_near_any))
  evalTactic (← `(tactic| (· intro r h; first
    | exact keeps_of_not_committed r h | exact keepsActs_of_not_committed r h)))
  evalTactic (← `(tactic| intro s' g lc ll fuel hfuel h))
  evalTactic (← `(tactic| try simp only [Framed.NearOk] at h))
  let rflI := mkIdent `rfl
  evalTactic (← `(tactic| rcases h with ⟨v, k, $rflI:ident⟩ | $rflI:ident))
  evalTactic (← `(tactic| all_goals (simp only [Framed.after]; vm_clear_unused)))

/-- A set (`i`: `DICT{,I,U}SET{,REF,B}` in any mode, `DICT{,I,U}REPLACEB`) from the state `S` on a
dictionary the run does not know and of which no `Dict.WF` is known (a dictionary known well formed
is left to the specifications of TvmLean/Proofs/Exec/Spec/DictSet.lean, which say what it maps), or
`REPLACEB` on the empty dictionary (null; no specification has it): by `vm_dict_set_any`, the runs
with any new root (null or a cell) and any flag. -/
def dictSetAny (i : Instr) (S : Expr) : TacticM Unit := withMainContext do
  let some root ← stackEntry? S 1 | throwError "check_framed: the stack"
  let nullReplaceB := root.isConstOf ``Value.null && i matches .dictReplaceB _ _
  unless nullReplaceB do
    unless root.isAppOfArity ``Value.cell 1 do throwError "check_framed: no cell"
    let rc := root.appArg!
    if Exec.isClosed rc then throwError "check_framed: a dictionary the run knows"
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if (ty.find? (·.isConstOf ``Dict.WF)).isSome && (ty.find? (· == rc)).isSome then
        throwError "check_framed: a dictionary known well formed"
  evalTactic (← `(tactic| vm_dict_set_any))
  evalTactic (← `(tactic| (· intro r h; first
    | exact keeps_of_not_committed r h | exact keepsActs_of_not_committed r h)))
  evalTactic (← `(tactic| intro s' g lc ll fuel hfuel h))
  evalTactic (← `(tactic| try simp only [Framed.SetOk] at h))
  let rflI := mkIdent `rfl
  let isSet : Bool := match i with
    | .dictSet _ _ _ .set => true
    | .dictSetB _ _ .set => true
    | _ => false
  if isSet then
    evalTactic (← `(tactic| rcases h with $rflI:ident | ⟨c, $rflI:ident⟩))
  else
    evalTactic (← `(tactic| rcases h with ⟨f, $rflI:ident⟩ | ⟨c, f, $rflI:ident⟩))
  evalTactic (← `(tactic| all_goals (simp only [Framed.after]; vm_clear_unused)))

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
`ctosAny`, `dictGetAny`, `configParamAny`, `rewriteVarAddrAny`, `rewriteStdAddrAny`, `dictMinMaxAny`,
`dictNearAny` or `dictSetAny`, whichever applies. Fails for any other instruction. -/
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
  | .tonEnvOp (.configParam _) => configParamAny i
  | .tonEnvOp (.rewriteVarAddr _) => rewriteVarAddrAny i S
  | .tonEnvOp (.rewriteStdAddr _) => rewriteStdAddrAny i S
  | .dictGetMinMax _ => dictMinMaxAny i S
  | .dictGetNear _ => dictNearAny i S
  | .dictSet _ _ _ _ => dictSetAny i S
  | .dictSetB _ _ _ => dictSetAny i S
  | .dictReplaceB _ _ => dictSetAny i S
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
  let some (_, r) ← keepsParts? t | throwError "check_dead: not a run from an exception"
  unless isDeadRun r do throwError "check_dead: not a run from an exception"
  let lem := mkIdent (if t.isAppOf ``KeepsActs then ``keepsActs_of_not_committed else ``keeps_of_not_committed)
  evalTactic (← `(tactic|
    exact $lem _ (Framed.dead_stepFinish_raiseDead _ _ _ rfl rfl (by decide) rfl rfl _)))

/-- `check_undead`: an exception kept as `VmState.raiseDead` that `check_dead` does not close (a
handler other than `excQuit`, a state committed by `COMMIT`), once no `if` is left to split before
it: `VmState.raiseException`, which the next steps expand. Fails if there is none. -/
elab "check_undead" : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless (t.find? (·.isAppOfArity ``VmState.raiseDead 2)).isSome do throwError "check_undead: no exception"
  let dead := match ← keepsParts? t with
    | some (_, r) => isDeadRun r
    | none => false
  unless dead || (← findSplit? t).isNone do
    throwError "check_undead: an `if` to split first"
  evalTactic (← `(tactic| simp only [VmState.raiseDead]))

/-! ## `COMMIT`

`COMMIT` (and the commit at a normal exit) runs `VmState.tryCommit`, whose test of the depths and
levels of `c4` and `c5` the run cannot decide on data it does not know: the step leaves the pair
`st.tryCommit` (its `fst` tested, its `snd` the state the run goes on from). -/

/-- `check_commit`: the goal holds `st.tryCommit`: the two cases of `tryCommit_cases` (committed,
with `c4` and `c5` of `st`; or nothing done), each written into the goal and the hypotheses. Fails
if there is none. -/
elab "check_commit" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (·.isAppOfArity ``VmState.tryCommit 1) | throwError "check_commit: no commit"
  let pf ← mkAppM ``tryCommit_cases #[e.appArg!]
  let (h, g') ← (← g.assert `hcommit (← inferType pf) pf).intro1P
  replaceMainGoal [g']
  let hId := mkIdent (← g'.withContext h.getUserName)
  evalTactic (← `(tactic| rcases $hId:ident with $hId:ident | $hId:ident <;>
    simp only [$hId:ident, Bool.false_eq_true] at *))

/-! ## Terms a step leaves that `check_step` does not reduce -/

/-- The heads of the terms `check_unstick` rewrites. -/
def unstickHeads : Array Name := #[``VmState.consumeTupleGas, ``Builder.finalize]

/-- `check_unstick`: a goal whose run is stuck on a term that `check_step` does not reduce, or holds
a term the next steps read better written out: the gas of a tuple `VmState.consumeTupleGas`, a cell
the code built `Builder.finalize` (as `Cell.mkOrdinary` of its bits and references: its `CTOS` by
`ctos_mkOrdinary`, its references and bits read by the lemmas of `Cell.mkOrdinary`). The term
rewritten; fails if there is none (a quick search of the goal first). -/
elab "check_unstick" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless (t.find? fun x => unstickHeads.any (x.isAppOf ·)).isSome do throwError "check_unstick: nothing"
  evalTactic (← `(tactic| simp only [VmState.consumeTupleGas, Builder.finalize,
    Builder.storeBits, Builder.empty, Array.empty_append, Array.append_empty,
    VM.getElem!_singleton, Array.push_empty]))

end TvmLean.Check

-- the action list a step leaves (`#[].push`), for the ends of the paths
attribute [check_close] Array.push_empty

-- an exception an instruction raises kept under a name (`check_dead`)
attribute [check_run_simp ↓] TvmLean.VmState.instrEnd_error_dead

-- a read of an unsigned integer lifted from `Except` into the VM (`GETSTORAGEFEE`)
attribute [check_run_simp] TvmLean.Spec.run_takeBitsAsNatCellUnd

namespace TvmLean

macro_rules
  | `(tactic| check_extra_step [$_args,*]) => `(tactic| first
      | check_dead
      | check_undead
      | check_unstick
      | check_commit
      | check_forget_c7
      | check_framed)

end TvmLean

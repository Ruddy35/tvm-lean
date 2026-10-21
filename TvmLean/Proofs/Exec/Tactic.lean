import Lean
import TvmLean.Proofs.DecEq
import TvmLean.Proofs.Exec.Run
import TvmLean.Proofs.Exec.Spec.Stack
import TvmLean.Proofs.Exec.Spec.Arith
import TvmLean.Proofs.Exec.Spec.Flow
import TvmLean.Proofs.Exec.Spec.Cell
import TvmLean.Proofs.Exec.Spec.TonEnv

/-!
# Stepping concrete code on a symbolic state: `vm_step`, `vm_run`

The goal is about a run, `P (VmState.runWith execInstr fuel st)` (or `VmState.run fuel st`), where
`fuel` is a successor (`n + k`) and `st` is written out (a `VmState.mk` term, as `{ st₀ with ... }`
gives) with concrete code; its stack, registers and the like may hold unknown values. `vm_step`
rewrites one step of the run, `vm_run` the whole run:

* the run is its first step and the rest (`VmState.runWith_succ'`, `VmState.runCont`); the step is
  `VmState.stepOnceWith` between steps (`VmState.stepWith_unfold`);
* the step of an ordinary continuation without closure data on concrete code (`stepCurrent`,
  `stepCode`) is chosen by evaluating the code: the next instruction
  (`VmState.stepOnceWith_instr'`), or the implicit `RET` or `JMPREF`; the facts it rests on (the bits
  left, the opcode's global version, the decoded instruction) are computed natively and proved by
  `decide`, checked by the kernel (`kernelEq`: an auxiliary lemma, one per code position, cached),
  so the decoder is never unfolded in the goal. Other continuations (`quit`, the exception handler
  `excQuit`) are unfolded (`VmState.stepOnceWith`, its destructuring of pairs made projections,
  `pairMatchToProj`);
* the instruction runs by its specification (`runInstr`: the lemmas tagged `vm_spec`, their
  equations on the state, the stack's shape, solved by unification and their other conditions by
  the discharger), or, if none applies, by its handler (the simprocs and lemmas of `vm_simp`,
  `Proofs/Exec/Eval.lean`);
* the gas checks, the exception raised (`VmState.raiseException`) and the end of the step
  (`VmState.instrEnd`) are unfolded, literal arithmetic is computed.

Nothing about a cell's hash or a long read of bits is evaluated: those stay terms (a cell load's
gas is `VmState.registerCellLoad`, unevaluated). A condition on the unknown values (a flag, a
comparison, the length of a slice, the gas) stays an `if`: `vm_run` splits the goal on it
(`split`), each branch with the condition as a hypothesis, closes a branch whose hypotheses
contradict (`vm_prune`, `omega`), and goes on in each branch until the run halts. What is left is
`P` of each halted path (`VmState.haltResult`, which `vm_run [VmState.haltResult]` unfolds).

Both take extra simp lemmas (`vm_run [h₁, h₂]`): facts about the unknown values, and the
definitions to unfold in the conditions (e.g. `Slice.haveBits`, `Slice.advanceBits`, so that the
length of a slice is linear arithmetic for `vm_prune`).

The native evaluation (`Lean.Meta.evalExpr`, `evalSlice`) only finds the result to prove; every
equation the tactics use is a theorem checked by the kernel.
-/

namespace TvmLean.Exec

open Lean Meta Simp

/-! ## Values back to terms -/

deriving instance ToExpr for Cell
deriving instance ToExpr for Slice
deriving instance ToExpr for IntVal
deriving instance ToExpr for DictSetMode
deriving instance ToExpr for DictMutMode
deriving instance ToExpr for PfxDictGetKind
deriving instance ToExpr for DictExtInstr
deriving instance ToExpr for TupleInstr
deriving instance ToExpr for CellInstr
deriving instance ToExpr for CryptoExtInstr
deriving instance ToExpr for CryptoInstr
deriving instance ToExpr for TonEnvInstr
deriving instance ToExpr for DebugInstr
deriving instance ToExpr for ContExtInstr
deriving instance ToExpr for ArithExtInstr
deriving instance ToExpr for CellExtInstr
deriving instance ToExpr for Instr
deriving instance ToExpr for Excno

/-! ## Evaluating closed terms of the code -/

unsafe def evalSliceUnsafe (e : Expr) : MetaM Slice := evalExpr Slice (mkConst ``Slice) e

/-- The value of a closed term of type `Slice` (native evaluation: only to find a result that is
then proved). -/
@[implemented_by evalSliceUnsafe] opaque evalSlice (e : Expr) : MetaM Slice

unsafe def evalNatUnsafe (e : Expr) : MetaM Nat := evalExpr Nat (mkConst ``Nat) e

/-- The value of a closed term of type `Nat`. -/
@[implemented_by evalNatUnsafe] opaque evalNat (e : Expr) : MetaM Nat

/-- A proof of `lhs = rhs`, both closed, by `decide`, checked by the kernel alone (an auxiliary
lemma, as `decide +kernel` makes). -/
def kernelEq (lhs rhs : Expr) : MetaM Expr := do
  let ty ← mkEq lhs rhs
  let pf ← mkDecideProof ty
  let name ← mkAuxLemma [] ty pf
  return mkConst name

/-- Whether `e` is closed: no free or meta variables. -/
def isClosed (e : Expr) : Bool := !e.hasFVar && !e.hasMVar

/-- A slice term as `Slice.mk cell bitPos refPos` (unfolding `Slice.ofCell` and the like), to
keep the cell's term in the slices the decoder returns. -/
def sliceParts? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let e ← whnfD e
  if e.isAppOfArity ``Slice.mk 3 then
    return some (e.getArg! 0, e.getArg! 1, e.getArg! 2)
  return none

/-- The term of the instruction `i` decoded from the code whose cell is the term `cellE` (value
`cell`): the references of the code cell it holds (`PUSHREF`, `DICTPUSHCONST`, ...) are written as
`cellE.refs[k]!`, not copied. -/
def instrExpr (i : Instr) (cellE : Expr) (cell : Cell) : MetaM Expr := do
  let mut e := toExpr i
  for k in [0:cell.refs.size] do
    let lit := toExpr cell.refs[k]!
    let ref ← mkAppOptM ``getElem! #[none, none, none, none, none, none,
      ← mkAppM ``Cell.refs #[cellE], mkNatLit k]
    e := e.replace fun x => if x == lit then some ref else none
  return e

/-- The terms of the decoding of `code` (the term) whose value is `s` and whose cell's term is
`cellE`: the result `Except.ok (i, n, rest)` or `Except.error x`, and, for an instruction, the
terms of `i`, `n` and `rest` (`rest` keeps `cellE`). -/
def decodeExprs (cellE : Expr) (s : Slice) : MetaM (Expr × Option (Expr × Expr × Expr)) := do
  let tyE ← mkAppM ``Prod #[mkConst ``Instr, ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Slice]]
  match decodeCp0WithBits s with
  | .ok (i, n, rest) =>
    let iE ← instrExpr i cellE s.cell
    let restE := mkApp3 (mkConst ``Slice.mk) cellE (mkNatLit rest.bitPos) (mkNatLit rest.refPos)
    let pair ← mkAppM ``Prod.mk #[mkNatLit n, restE]
    let triple ← mkAppM ``Prod.mk #[iE, pair]
    return (mkApp3 (mkConst ``Except.ok [0, 0]) (mkConst ``Excno) tyE triple, some (iE, mkNatLit n, restE))
  | .error x => return (mkApp3 (mkConst ``Except.error [0, 0]) (mkConst ``Excno) tyE (toExpr x), none)

/-- `decodeCp0WithBits code` for a closed `code`: its value, proved by the kernel. -/
simproc decodeCp0 (decodeCp0WithBits _) := fun e => do
  let_expr decodeCp0WithBits code := e | return .continue
  unless isClosed code do return .continue
  let some (cellE, _, _) ← sliceParts? code | return .continue
  let s ← evalSlice code
  let (rE, _) ← decodeExprs cellE s
  let pf ← kernelEq e rE
  return .done { expr := rE, proof? := pf }

/-- A closed `Nat` term of the code (`f code`): its value, proved by the kernel. -/
def groundNat (e : Expr) : SimpM Step := do
  unless isClosed e do return .continue
  let n ← evalNat e
  let rE := mkNatLit n
  let pf ← kernelEq e rE
  return .done { expr := rE, proof? := pf }

simproc codeBitsRemaining (Slice.bitsRemaining _) := groundNat
simproc codeRefsRemaining (Slice.refsRemaining _) := groundNat
simproc codeOpcode24 (Slice.opcode24 _) := groundNat
simproc codeRequiredVersion (cp0RequiredVersion _) := groundNat

/-! ## The step of the current continuation -/

/-- A proof of the closed proposition `p` by `decide` (small: arithmetic on literals). -/
def decideProof (p : Expr) : MetaM Expr := do
  let pf ← mkDecideProof p
  let r ← withAtLeastTransparency .default <| whnf (pf.appFn!.appArg!)
  unless r.isAppOf ``Decidable.isTrue do throwError "not decided: {p}"
  return pf

/-- The step of an ordinary continuation without closure data running the concrete code `code`
(the term; `st` the state): the next instruction (`VmState.stepOnceWith_instr'`), or the implicit
`RET` or `JMPREF` (`VmState.stepOnceWith_implicitRet'`, `VmState.stepOnceWith_implicitJmpRef'`), the
facts about the code evaluated and proved by the kernel. -/
def stepCode (exec st code saved cregs hcc : Expr) : MetaM (Option (Expr × Expr)) := do
  unless isClosed code do return none
  let some (cellE, _, _) ← sliceParts? code | return none
  let s ← evalSlice code
  let b := s.bitsRemaining
  let hbits ← kernelEq (← mkAppM ``Slice.bitsRemaining #[code]) (mkNatLit b)
  let pf ← if b ≠ 0 then
      let cp ← whnfCore (← whnfR (← mkAppM ``VmState.cp #[st]))
      unless ← isDefEq cp (toExpr (0 : Int)) do return none
      let hcp ← mkEqRefl (← mkAppM ``VmState.cp #[st])
      let k := cp0RequiredVersion s.opcode24
      let hver ← kernelEq (← mkAppM ``cp0RequiredVersion #[← mkAppM ``Slice.opcode24 #[code]]) (mkNatLit k)
      let gvE ← mkAppM ``VmState.globalVersion #[st]
      let hk ← if k = 0 then mkAppM ``Nat.zero_le #[gvE] else
        decideProof (← mkAppM ``LE.le #[mkNatLit k, ← whnfCore (← whnfR gvE)])
      let (rE, parts) ← decodeExprs cellE s
      let some (iE, nE, restE) := parts | return none
      let hdec ← kernelEq (← mkAppM ``decodeCp0WithBits #[code]) rE
      let hb ← decideProof (← mkAppM ``Ne #[mkNatLit b, mkNatLit 0])
      mkAppM ``VmState.stepOnceWith_instr'
        #[exec, st, code, restE, saved, cregs, iE, nE, mkNatLit b, mkNatLit k, hcc, hcp, hbits, hb, hver, hk, hdec]
    else
      let r := s.refsRemaining
      let hrefs ← kernelEq (← mkAppM ``Slice.refsRemaining #[code]) (mkNatLit r)
      if r = 0 then
        mkAppM ``VmState.stepOnceWith_implicitRet' #[exec, st, code, saved, cregs, hcc, hbits, hrefs]
      else
        let hr ← decideProof (← mkAppM ``Ne #[mkNatLit r, mkNatLit 0])
        mkAppM ``VmState.stepOnceWith_implicitJmpRef' #[exec, st, code, saved, cregs, mkNatLit r, hcc, hbits, hrefs, hr]
  let rhs := (← inferType pf).appArg!
  return some (rhs, pf)

/-- `match e with | (a, b) => f a b` (a destructuring `let` of a pair) as `f e.1 e.2`, in all of
`t` (definitionally equal, by eta for structures): the pair is then an ordinary subterm that `simp`
can rewrite with any lemma, not a discriminant it can only `dsimp`. -/
def pairMatchToProj (t : Expr) : MetaM Expr :=
  Meta.transform t (post := fun e => do
    let some app ← matchMatcherApp? e | return .continue
    unless app.discrs.size == 1 && app.alts.size == 1 && app.altNumParams[0]! == 2 do return .continue
    let d := app.discrs[0]!
    let ty ← whnfD (← inferType d)
    unless ty.isAppOfArity ``Prod 2 do return .continue
    let r := mkAppN (mkAppN app.alts[0]! #[mkProj ``Prod 0 d, mkProj ``Prod 1 d]) app.remaining
    return .done r.headBeta)

/-- `st.stepOnceWith exec`: the step of the code when the current continuation is an ordinary one
without closure data on concrete code (`stepCode`), else `VmState.stepOnceWith` unfolded (its
`match` on the continuation then reduces). -/
simproc stepCurrent (VmState.stepOnceWith _ _) := fun e => do
  let_expr VmState.stepOnceWith exec st := e | return .continue
  let cc ← whnfCore (← whnfR (← mkAppM ``VmState.cc #[st]))
  if cc.isAppOfArity ``Continuation.ordinary 4 then
    let code := cc.getArg! 0
    let saved := cc.getArg! 1
    let cregs := cc.getArg! 2
    let cdata := cc.getArg! 3
    unless cdata.isConstOf ``OrdCdata.empty do
      unless ← withReducible (isDefEq cdata (mkConst ``OrdCdata.empty)) do return .continue
    let hcc ← mkEqRefl (← mkAppM ``VmState.cc #[st])
    match ← stepCode exec st code saved cregs hcc with
    | some (rhs, pf) => return .visit { expr := rhs, proof? := pf }
    | none =>
      let pf ← mkAppM ``VmState.stepOnceWith_ordinary' #[exec, st, code, saved, cregs, hcc]
      return .visit { expr := (← inferType pf).appArg!, proof? := pf }
  else if cc.getAppFn.isConst && (cc.getAppFn.constName!.getPrefix == ``Continuation) then
    let some e' ← withTransparency .all (unfoldDefinition? e) | return .continue
    return .visit { expr := ← pairMatchToProj e'.headBeta }
  else
    return .continue

/-! ## Instructions by their specifications -/

/-- `ExceptT.run (execInstr i) st` by a specification (`vm_spec`) whose instruction and state
unify with the term: its hypotheses on the state (`st.stack = ...`, the shape of the stack, and
the like) by unification at reducible transparency, the others by the discharger. -/
def applySpec (e : Expr) : SimpM (Option Simp.Result) := do
  let some ext ← getSimpExtension? `vm_spec | return none
  let thms ← ext.getTheorems
  let cands ← thms.post.getMatch e
  for thm in cands do
    let saved ← Meta.saveState
    let ok ← try
        let val ← thm.getValue
        let ty ← inferType val
        let (mvars, _, concl) ← forallMetaTelescopeReducing ty
        let some (_, lhs, _) := concl.eq? | failure
        unless ← withReducible (isDefEq lhs e) do failure
        -- the equations first (the shape of the stack, by unification), then the other conditions
        for m in mvars do
          if ← m.mvarId!.isAssigned then continue
          let mty ← instantiateMVars (← inferType m)
          unless ← isProp mty do continue
          if let some (_, a, b) := mty.eq? then
            if ← withReducible (isDefEq a b) then
              m.mvarId!.assign (← mkEqRefl a)
        for m in mvars do
          if ← m.mvarId!.isAssigned then continue
          let mty ← instantiateMVars (← inferType m)
          unless ← isProp mty do continue
          if mty.hasMVar then failure
          let some p ← (← getMethods).discharge? mty | failure
          m.mvarId!.assign p
        let pf ← instantiateMVars (mkAppN val mvars)
        if pf.hasMVar then failure
        let some (_, _, rhs) := (← instantiateMVars concl).eq? | failure
        pure (some { expr := rhs, proof? := some pf : Simp.Result })
      catch _ => pure none
    match ok with
    | some r => return some r
    | none => saved.restore
  return none

/-- `ExceptT.run (execInstr i) st`, once `st` is simplified (a state written out): by a
specification (`applySpec`), else by the handler of `i` (the chain of dispatchers followed, then
the run computed by the lemmas of `vm_run`). -/
simproc runInstr (@ExceptT.run Excno (StateM VmState) _ (execInstr _) _) := fun e => do
  if let some r ← applySpec e then return .visit r
  match ← dispatchRun false e with
  | .visit e' => return .visit { expr := e' }
  | _ => return .continue

end TvmLean.Exec

namespace TvmLean

/-- The simp lemmas of a step (`Proofs/Exec/Tactic.lean`), with those of `vm_simp`. -/
syntax (name := vmStepSimp) "vm_step_simp" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| vm_step_simp $[[$args,*]]?) => do
    let args := args.getD ⟨#[]⟩
    `(tactic| set_option maxRecDepth 100000 in simp (config := { maxSteps := 2000000 }) (disch := vm_disch) only [
      TvmLean.Exec.runInstr, TvmLean.Exec.reduceInnerDispatchRun, TvmLean.Exec.unfoldModelRun,
      TvmLean.Exec.decodeCp0, TvmLean.Exec.codeBitsRemaining, TvmLean.Exec.codeRefsRemaining,
      TvmLean.Exec.codeOpcode24, TvmLean.Exec.codeRequiredVersion, TvmLean.Exec.stepCurrent,
      vm_run, VmState.run_eq, VmState.runCont_continue, VmState.runCont_halt, VmState.runCont_ite,
      VmState.runCont_dite, VmState.stepWith_unfold, StepResult.state_continue, StepResult.state_halt,
      StepResult.state_ite, StepResult.mapState_continue, StepResult.mapState_halt,
      StepResult.mapState_ite, VmState.instrStep_eq, VmState.instrEnd_ok, VmState.instrEnd_error,
      VmState.instrEnd_ite, VmState.instrEnd_ite_id, VmState.instrEnd_dite, VmState.retStep_eq,
      VmState.retEnd_ok, VmState.retEnd_error, VmState.jmpRefStep,
      VmState.enter_empty, VmState.applyCregsCdata_empty, VmState.countJump_of_lt, VmState.consumeGas,
      GasLimits.consume, instrGas, gasPerInstr, implicitRetGasPrice, implicitJmpRefGasPrice,
      exceptionGasPrice, VmState.gasExhaustedNow, VmState.outOfGasHalt, VmState.raiseException,
      VmState.excHandlerNeedsMoreArgs, Option.isNone_none, Array.isEmpty_empty,
      Array.size_push, Array.pop_push, Array.size_pop, if_true,
      if_false, dite_true, dite_false, Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false,
      ne_eq, Nat.add_sub_cancel, Nat.sub_self, Nat.add_one_sub_one, Nat.sub_zero, and_true, true_and,
      decide_eq_true_eq, decide_eq_false_iff_not, decide_not, Bool.not_not, Bool.not_true,
      Bool.not_false, Decidable.not_not, Bool.not_eq_true', Bool.not_eq_false', beq_iff_eq,
      Int.ofNat_eq_coe, Int.toNat_natCast, Bool.and_eq_true, Bool.or_eq_true, Bool.eq_false_iff, ite_not,
      Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, ge_iff_le, gt_iff_lt, reduceIte, reduceDIte,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceLT, Nat.reduceGT,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, Nat.reduceBEq, Nat.reduceBNe, Int.reduceAdd, Int.reduceSub, Int.reduceMul, Int.reduceNeg,
      Int.reducePow, Int.reduceLT, Int.reduceLE, Int.reduceGT, Int.reduceGE, Int.reduceEq, Int.reduceNe,
      Int.reduceNatCast, Int.reduceNatCast', Int.reduceOfNat, Int.reduceToNat, GasLimits.ofLimits,
      GasLimits.ofLimit, reduceCtorEq, Excno.toInt, Array.size_empty, Nat.zero_lt_succ, Nat.succ_ne_zero,
      Nat.add_one_ne_zero, Nat.zero_add, Int.toNat_natCast, or_false, false_or, or_self, and_self,
      not_false_eq_true, not_true_eq_false, $args,*])

/-- One step of a run (`Proofs/Exec/Tactic.lean`): the goal mentions
`VmState.runWith execInstr (fuel + 1) st` (or `VmState.run`); it becomes the run after the step,
with the cases the step cannot decide as `if`s. Extra simp lemmas: `vm_step [h]`. -/
syntax (name := vmStep) "vm_step" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| vm_step $[[$args,*]]?) => do
    let args := args.getD ⟨#[]⟩
    `(tactic| ((try simp only [VmState.run_eq]); rw [VmState.runWith_succ']; vm_step_simp [$args,*]))

/-- A path whose conditions contradict each other is closed (`omega` on the hypotheses). -/
macro "vm_prune" : tactic => `(tactic| (exfalso; omega))

/-- The whole run (`Proofs/Exec/Tactic.lean`): one step at a time (`vm_step`); a case the step
cannot decide splits the goal (`split`), each branch with its condition as a hypothesis, and a
branch whose conditions contradict the hypotheses is closed (`vm_prune`). Goes on until every
run halts (or its fuel is not a successor): what is left is the goal of each halted path. Extra
simp lemmas: `vm_run [h]`. -/
syntax (name := vmRun) "vm_run" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| vm_run $[[$args,*]]?) => do
    let args := args.getD ⟨#[]⟩
    `(tactic| repeat' (first
        | (split <;> try vm_prune)
        | vm_step [$args,*]))

end TvmLean

import Lean
import TvmLean.Proofs.Fast.Twin
import TvmLean.Proofs.DecEq
import TvmLean.Proofs.Exec.Run
import TvmLean.Proofs.Exec.Spec.Stack
import TvmLean.Proofs.Exec.Spec.Arith
import TvmLean.Proofs.Exec.Spec.Flow
import TvmLean.Proofs.Exec.Spec.Cell
import TvmLean.Proofs.Exec.Spec.TonEnv
import TvmLean.Proofs.Exec.Spec.Dispatch
import TvmLean.Proofs.Exec.Spec.Dict
import TvmLean.Proofs.Exec.Spec.Crypto
import TvmLean.Proofs.Exec.Spec.Msg
import TvmLean.Proofs.Exec.Spec.Loop

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
  `decide`, checked by the kernel (`kernelEq`: an auxiliary lemma, one per code position, cached;
  with the option `vm.fastFacts`, by kernel evaluation over the fast twins of
  `TvmLean/Proofs/Fast/`, which takes a fraction of the time), so the decoder is never unfolded in
  the goal. Other continuations (`quit`, the exception handler
  `excQuit`) are unfolded (`VmState.stepOnceWith`, its destructuring of pairs made projections,
  `pairMatchToProj`);
* the instruction runs by its specification (`runInstr`: the lemmas tagged `vm_spec`, their
  equations on the state, the stack's shape, solved by unification and their other conditions by
  the discharger), or, if none applies, by its handler (the simprocs and lemmas of `vm_simp`,
  `Proofs/Exec/Eval.lean`);
* the gas checks, the exception raised (`VmState.raiseException`) and the end of the step
  (`VmState.instrEnd`) are unfolded, literal arithmetic is computed.

Nothing about a cell's hash or a long read of bits is evaluated: those stay terms (a cell load's
gas is the symbolic `cellLoadGas loaded c`, between 25 and 100, `Proofs/Exec/Load.lean`). The facts
of the code that are closed (the bits of a method id as a dictionary key, `dictKeyBits?`; the lookup
of a key in a dictionary of the code, `dictLookupLoads`) are evaluated natively and proved by the
kernel (`closedDictFacts`, `evalClosed?`), as conditions of a specification and in the goal; the
cells a lookup returns keep their terms in the code (`cellTermIn`).

A condition on the unknown values (a flag, a comparison, the length of a slice, the gas) stays an
`if`: `vm_split` reduces it to its branch if linear arithmetic decides it from the context (with
the bounds of the load gas, `vm_load_bounds`, and of numbers read from bits,
`VM.bitsToNat_readBits_lt`), else splits the goal (`split`), each branch with the condition as a
hypothesis; a `match` on a flag the step popped (`(.ok b, st)`) is split on the cases of the flag.
`vm_run` closes a branch whose hypotheses contradict (`vm_prune_cheap`) and goes on in each branch
until the run halts. What is left is `P` of each halted path (`VmState.haltResult`, which
`vm_run [VmState.haltResult]` unfolds).

A run whose fuel is a variable is split at each step into the run out of fuel and the run with one
more step (`vm_fuel`). At a loop head (`VmState.atLoopHead`) `vm_run` stops; `vm_loop` applies the
loop rule there (`VmState.runWith_inv`, with the trivial invariant: the loop head with any gas,
loaded cells, step counters, `c5` and top stack payloads), after which `vm_run` runs one iteration
and closes the paths that come back to the loop head by the induction hypothesis
(`vm_loop_close`).

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

register_option vm.fastFacts : Bool := {
  defValue := false
  descr := "prove the closed facts of the code (`kernelEq`: the decoded instructions, dictionary \
    lookups) by kernel evaluation over the fast twins (`TvmLean.Fast.fastRflProof`, \
    TvmLean/Proofs/Fast/Twin.lean) instead of `decide`; the speed-up needs the replacements of \
    TvmLean/Proofs/Fast/ imported (e.g. `TvmLean.Proofs.Fast.Run`)"
}

/-- A proof of `lhs = rhs`, both closed, by `decide`, checked by the kernel alone (an auxiliary
lemma, as `decide +kernel` makes); with the option `vm.fastFacts`, by kernel evaluation over the
fast twins (`TvmLean.Fast.fastRflProof`, also an auxiliary lemma checked by the kernel). -/
def kernelEq (lhs rhs : Expr) : MetaM Expr := do
  let ty ← mkEq lhs rhs
  if vm.fastFacts.get (← getOptions) then
    return ← Fast.fastRflProof ty
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

/-! ## Closed facts of the code: dictionary lookups -/

unsafe def evalCellUnsafe (e : Expr) : MetaM Cell := evalExpr Cell (mkConst ``Cell) e

/-- The value of a closed term of type `Cell`. -/
@[implemented_by evalCellUnsafe] opaque evalCell (e : Expr) : MetaM Cell

unsafe def evalKeyBitsUnsafe (e : Expr) : MetaM (Option BitString) :=
  evalExpr (Option BitString) (mkApp (mkConst ``Option [0]) (mkConst ``BitString)) e

/-- The value of a closed term of type `Option BitString`. -/
@[implemented_by evalKeyBitsUnsafe] opaque evalKeyBits (e : Expr) : MetaM (Option BitString)

unsafe def evalBitsUnsafe (e : Expr) : MetaM BitString := evalExpr BitString (mkConst ``BitString) e

/-- The value of a closed term of type `BitString`. -/
@[implemented_by evalBitsUnsafe] opaque evalBits (e : Expr) : MetaM BitString

/-- The term of the cell `c` as a cell of the tree of `root` (its term `rootE`):
`rootE.refs[i]!.refs[j]!...` for the first such cell found (breadth first, at most `depth` deep),
so that the cells a closed fact returns keep the terms of the code. -/
def cellTermIn (rootE : Expr) (root : Cell) (c : Cell) (depth : Nat := 8) : MetaM (Option Expr) := do
  let mut frontier : Array (Expr × Cell) := #[(rootE, root)]
  for _ in [0:depth + 1] do
    let mut next : Array (Expr × Cell) := #[]
    for (e, x) in frontier do
      if x == c then return some e
      for k in [0:x.refs.size] do
        let ref ← mkAppOptM ``getElem! #[none, none, none, none, none, none, ← mkAppM ``Cell.refs #[e], mkNatLit k]
        next := next.push (ref, x.refs[k]!)
    frontier := next
  return none

/-- The term of a cell of the tree of `root`, else the literal. -/
def cellTerm (rootE : Expr) (root : Cell) (c : Cell) : MetaM Expr := do
  return (← cellTermIn rootE root c).getD (toExpr c)

/-- `dictKeyBits? idx n unsigned` for closed arguments: its value. -/
def evalDictKeyBits? (e : Expr) : MetaM (Option Expr) := do
  let_expr dictKeyBits? _ _ _ := e | return none
  let v ← evalKeyBits e
  return some (toExpr v)

/-- `dictLookupLoads root key` for closed arguments: its value, with the cells found written as
cells of `root`'s tree (`cellTermIn`). -/
def evalDictLookupLoads? (e : Expr) : MetaM (Option Expr) := do
  let_expr dictLookupLoads rootE keyE := e | return none
  let root ← evalCell rootE
  let key ← evalBits keyE
  let sliceTy := mkConst ``Slice
  let resTy ← mkAppM ``Prod #[mkApp (mkConst ``Option [0]) sliceTy, mkApp (mkConst ``List [0]) (mkConst ``Cell)]
  match dictLookupLoads root key with
  | .error x => return some (mkApp3 (mkConst ``Except.error [0, 0]) (mkConst ``Excno) resTy (toExpr x))
  | .ok (r, cells) =>
    let rE ← match r with
      | none => pure (mkApp (mkConst ``Option.none [0]) sliceTy)
      | some s =>
        pure (mkApp2 (mkConst ``Option.some [0]) sliceTy
          (mkApp3 (mkConst ``Slice.mk) (← cellTerm rootE root s.cell) (mkNatLit s.bitPos) (mkNatLit s.refPos)))
    let mut cellsE := mkApp (mkConst ``List.nil [0]) (mkConst ``Cell)
    for c in cells.reverse do
      cellsE := mkApp3 (mkConst ``List.cons [0]) (mkConst ``Cell) (← cellTerm rootE root c) cellsE
    let pair ← mkAppM ``Prod.mk #[rE, cellsE]
    return some (mkApp3 (mkConst ``Except.ok [0, 0]) (mkConst ``Excno) resTy pair)

/-- The value of a closed term `e` of one of the functions symbolic execution evaluates on the
code (`dictKeyBits?`, `dictLookupLoads`), computed natively: only to find the result, which is
then proved (`closedEqProof`). -/
def evalClosed? (e : Expr) : MetaM (Option Expr) := do
  unless isClosed e do return none
  if let some v ← evalDictKeyBits? e then return some v
  if let some v ← evalDictLookupLoads? e then return some v
  return none

/-- A proof of `e = v` for the value `v` that `evalClosed?` found, by the kernel. -/
def closedEqProof (e v : Expr) : MetaM Expr := kernelEq e v

/-- `dictKeyBits?` and `dictLookupLoads` on closed arguments: their value, proved by the kernel. -/
simproc closedDictFacts (dictLookupLoads _ _) := fun e => do
  let some v ← evalClosed? e | return .continue
  return .done { expr := v, proof? := ← closedEqProof e v }

simproc closedDictKeyBits (dictKeyBits? _ _ _) := fun e => do
  let some v ← evalClosed? e | return .continue
  return .done { expr := v, proof? := ← closedEqProof e v }

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

/-- `st.stepWith exec` when `st` sets no `max_library_loads` (`maxLibraryLoads` reduces to
`none`): the step `st.stepOnceWith exec` (`VmState.stepWith_of_none`), before `simp` looks into
the cases of `VmState.stepWith` with the limit. -/
simproc ↓ stepWithNone (VmState.stepWith _ _) := fun e => do
  let_expr VmState.stepWith exec st := e | return .continue
  let m ← whnfCore (← whnfR (← mkAppM ``VmState.maxLibraryLoads #[st]))
  unless m.isAppOf ``Option.none do return .continue
  let h ← mkEqRefl (← mkAppM ``VmState.maxLibraryLoads #[st])
  let pf ← mkAppM ``VmState.stepWith_of_none #[exec, st, h]
  return .visit { expr := ← mkAppM ``VmState.stepOnceWith #[exec, st], proof? := pf }

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
        unless ← withReducible (isDefEq lhs e) do throwError "lhs" 
        -- the equations first (the shape of the stack, by unification), then the other conditions
        for m in mvars do
          if ← m.mvarId!.isAssigned then continue
          let mty ← instantiateMVars (← inferType m)
          unless ← isProp mty do continue
          if let some (_, a, b) := mty.eq? then
            if ← withReducible (isDefEq a b) then
              m.mvarId!.assign (← mkEqRefl a)
            -- a fact of the code (`dictLookupLoads root key = .ok (some ?val, ?loads)`): its
            -- closed side evaluated, unified with the other, proved by the kernel
            else if let some v ← evalClosed? a then
              if ← withReducible (isDefEq b v) then
                m.mvarId!.assign (← closedEqProof a v)
            -- a fact of the goal's context (`c7[0]! = .tuple ?params`): a hypothesis that unifies
            else if mty.hasMVar then
              for d in ← getLCtx do
                if d.isImplementationDetail then continue
                let s ← Meta.saveState
                if ← withReducible (isDefEq mty d.type) then
                  m.mvarId!.assign d.toExpr
                  break
                else s.restore
        for m in mvars do
          if ← m.mvarId!.isAssigned then continue
          let mty ← instantiateMVars (← inferType m)
          unless ← isProp mty do continue
          if mty.hasMVar then throwError "mvar in {mty}"
          let some p ← (← getMethods).discharge? mty | throwError "disch {mty}" 
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

/-- An array literal of values `#[x₁, ..., xₙ]` as `((#[].push x₁)...).push xₙ` (definitionally
equal), the form the specifications state stacks in (the initial stack of the compute phase is a
literal, `computePhaseStack`). -/
dsimproc arrayLitPush (List.toArray _) := fun e => do
  let_expr List.toArray α l := e | return .continue
  unless α.isConstOf ``Value do return .continue
  let some (_, elems) := l.listLit? | return .continue
  if elems.isEmpty then return .continue
  let u := e.getAppFn.constLevels!
  let mut acc := mkApp2 (mkConst ``List.toArray u) α (mkApp (mkConst ``List.nil u) α)
  for x in elems do
    acc := mkApp3 (mkConst ``Array.push u) α acc x
  return .done acc

/-- Whether `e` is an integer literal (`OfNat.ofNat n`, `-OfNat.ofNat n`, `Int.ofNat n`). -/
def intLit? (e : Expr) : Option Int :=
  match e.int? with
  | some i => some i
  | none => none

theorem int_sub_sub_lit (x a b : Int) : x - a - b = x - (a + b) := by omega
theorem int_sub_right_comm (x t n : Int) : x - t - n = x - n - t := by omega

/-- The gas left after many charges, `((g - t₁) - 26) - 18 - ...`, with its literal charges summed
and moved first: `(x - t) - n` with `n` a literal is `(x - n) - t`, and `(x - m) - n` with both
literals is `x - (m + n)` (then computed). Keeps the terms of a run linear in size. -/
simproc foldIntSub (@HSub.hSub Int Int Int _ (@HSub.hSub Int Int Int _ _ _) _) := fun e => do
  let_expr HSub.hSub _ _ _ _ xt n := e | return .continue
  let some _ := intLit? n | return .continue
  let_expr HSub.hSub _ _ _ _ x t := xt | return .continue
  if (intLit? t).isSome then
    let r ← mkAppM ``HSub.hSub #[x, ← mkAppM ``HAdd.hAdd #[t, n]]
    return .visit { expr := r, proof? := ← mkAppM ``int_sub_sub_lit #[x, t, n] }
  else
    let r ← mkAppM ``HSub.hSub #[← mkAppM ``HSub.hSub #[x, n], t]
    return .visit { expr := r, proof? := ← mkAppM ``int_sub_right_comm #[x, t, n] }

/-! ## Facts for pruning, fuel -/

/-- All subterms `cellLoadGas l c` of `e`, added to `acc`. -/
def collectCellLoadGas (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let r ← IO.mkRef acc
  e.forEach fun x => do
    if x.isAppOfArity ``cellLoadGas 2 then
      r.modify fun a => if a.contains x then a else a.push x
  r.get

/-- `vm_load_bounds`: the bounds of every symbolic load gas (`cellLoadGas l c`, between 25 and 100,
`cellLoadGas_bounds`) in the goal and the hypotheses, as hypotheses (for `omega`). -/
elab "vm_load_bounds" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let mut terms ← collectCellLoadGas (← instantiateMVars (← g.getType)) #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      terms ← collectCellLoadGas (← instantiateMVars d.type) terms
  let mut g := g
  let mut known : Array Expr := #[]
  for d in ← getLCtx do
    known := known.push (← instantiateMVars d.type)
  for t in terms do
    let pf ← mkAppM ``cellLoadGas_bounds #[t.getArg! 0, t.getArg! 1]
    let ty ← inferType pf
    if known.contains ty then continue
    let (_, g') ← (← g.assert `hload ty pf).intro1P
    g := g'
  Lean.Elab.Tactic.replaceMainGoal [g]

/-- The bounds `bitsToNat (s.readBits n) < 2 ^ n` (`VM.bitsToNat_readBits_lt`, `n` a literal) of the
numbers read from bits in `e`: proofs and their statements (with `2 ^ n` computed). -/
def readBitsBounds (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let r ← IO.mkRef (#[] : Array Expr)
  e.forEach fun x => do
    if x.isAppOfArity ``bitsToNat 1 && x.appArg!.isAppOfArity ``Slice.readBits 2 then
      r.modify fun a => if a.contains x then a else a.push x
  let mut out := #[]
  for t in ← r.get do
    let s := t.appArg!.getArg! 0
    let nE := t.appArg!.getArg! 1
    let some n := nE.rawNatLit? <|> nE.nat? | continue
    let ty ← mkAppM ``LT.lt #[t, mkNatLit (2 ^ n)]
    out := out.push (← mkExpectedTypeHint (← mkAppM ``VM.bitsToNat_readBits_lt #[s, nE]) ty, ty)
  return out

/-- Whether `p` follows by linear arithmetic (`omega` at reducible transparency) from the context
and the bounds of the numbers read from bits in `p` (`readBitsBounds`, given to `omega` only): if
so, the goal `g` gets it as a hypothesis (`hvm_cond`), returned with the new goal. -/
def assertByOmega? (g : MVarId) (p : Expr) : Lean.Elab.Tactic.TacticM (Option (FVarId × MVarId)) := do
  let saved ← Lean.Elab.Tactic.saveState
  try
    let facts ← readBitsBounds p
    let mut target := p
    for (_, ty) in facts.reverse do
      target ← mkArrow ty target
    let pf ← mkFreshExprSyntheticOpaqueMVar target
    let gs ← Lean.Elab.Tactic.run pf.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic| intros; with_reducible omega))
    unless gs.isEmpty do
      saved.restore; return none
    let g' ← g.assert `hvm_cond p (mkAppN pf (facts.map (·.1)))
    let (h, g'') ← g'.intro1P
    return some (h, g'')
  catch _ =>
    saved.restore; return none

/-- A Boolean that is not a literal inside constructor applications (`(.ok b, st)`), at most
`depth` constructors deep. -/
def boolInCtors? (e : Expr) : Nat → MetaM (Option Expr)
  | 0 => pure none
  | depth + 1 => do
    let e ← whnfR (← instantiateMVars e)
    let .const f _ := e.getAppFn | return none
    unless (← getEnv).isConstructor f do return none
    for a in e.getAppArgs do
      if a.isConstOf ``Bool.true || a.isConstOf ``Bool.false then continue
      if (← whnfR (← inferType a)).isConstOf ``Bool then
        if !a.hasLooseBVars then return some a
      if let some b ← boolInCtors? a depth then return some b
    return none

/-- The fuel of the run in the goal (`VmState.runWith exec fuel st`) when it is a variable. -/
def runFuelVar? (e : Expr) : Option FVarId :=
  (e.find? fun x => x.isAppOfArity ``VmState.runWith 3 && (x.getArg! 1).isFVar).map
    fun x => (x.getArg! 1).fvarId!

/-- The state of the run in the goal (`VmState.runWith exec fuel st`). -/
def runState? (e : Expr) : Option Expr :=
  (e.find? fun x => x.isAppOfArity ``VmState.runWith 3).map (·.getArg! 2)

/-- `vm_not_at_loop_head`: fails if the run in the goal is at a loop head (`VmState.atLoopHead`:
the current continuation is the condition or body that `c0` loops on), so that `vm_run` stops
there for the loop rule (`VmState.runWith_loop`). -/
elab "vm_not_at_loop_head" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let some st := runState? (← instantiateMVars (← g.getType)) | return
  let cc ← whnfCore (← whnfR (← mkAppM ``VmState.cc #[st]))
  let c0 ← whnfCore (← whnfR (← mkAppM ``Regs.c0 #[← mkAppM ``VmState.regs #[st]]))
  let looped? : Option Expr :=
    if c0.isAppOfArity ``Continuation.whileCond 3 then some (c0.getArg! 0)
    else if c0.isAppOfArity ``Continuation.untilBody 2 then some (c0.getArg! 0)
    else if c0.isAppOfArity ``Continuation.repeatBody 3 then some (c0.getArg! 0)
    else if c0.isAppOfArity ``Continuation.againBody 1 then some (c0.getArg! 0)
    else none
  if let some k := looped? then
    if ← withReducible (isDefEq k cc) then throwError "vm_not_at_loop_head: at a loop head"

/-- `vm_fuel`: a run whose fuel is a variable is split into the run out of fuel (`0`: it halts
with `fatal`, `VmState.runWith_zero`) and the run with one more step (`fuel + 1`). -/
elab "vm_fuel" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let some f := runFuelVar? (← instantiateMVars (← g.getType)) | throwError "vm_fuel: no run with a variable fuel"
  let subgoals ← g.cases f
  Lean.Elab.Tactic.replaceMainGoal (subgoals.map (·.mvarId)).toList

/-- `vm_has_run`: fails unless the goal mentions a run (`VmState.runWith`, `VmState.runCont`). -/
elab "vm_has_run" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  if (t.find? fun x => x.isAppOfArity ``VmState.runWith 3 || x.isAppOfArity ``VmState.runCont 3).isNone then
    throwError "vm_has_run: no run"

/-! ## Loops: the loop rule on the loop head of a run -/

/-- The payload of a stack entry that a loop changes: the slice, cell, builder or integer inside
the value (the entry keeps its shape, so that the specifications still apply). -/
def stackPayload? (v : Expr) : Option (Expr × (Expr → Expr)) :=
  if v.isAppOfArity ``Value.slice 1 || v.isAppOfArity ``Value.cell 1 || v.isAppOfArity ``Value.builder 1 then
    some (v.appArg!, fun x => mkApp v.appFn! x)
  else if v.isAppOfArity ``Value.int 1 && v.appArg!.isAppOfArity ``IntVal.num 1 then
    some (v.appArg!.appArg!, fun x => mkApp v.appFn! (mkApp v.appArg!.appFn! x))
  else none

/-- The loop head `S` (a `VmState.mk` application) with the parts that an iteration of a loop
changes as holes: the gas, the loaded cells, the counters of jumps and steps, `c5`, and the payloads
of the top `k` stack entries. Returns the values of the holes in `S`, the function that fills them,
and the index of the hole of the jump counter. -/
def loopHoles (S : Expr) (k : Nat) : MetaM (Array Expr × (Array Expr → Expr) × Nat) := do
  unless S.isAppOfArity ``VmState.mk 20 do throwError "vm_loop: the state is not written out"
  let fields := getStructureFields (← getEnv) ``VmState
  let idx (n : Name) : MetaM Nat := do
    let some i := fields.idxOf? n | throwError "vm_loop: no field {n}"
    return i
  let args := S.getAppArgs
  let plainNames := [`gas, `loadedCells, `chainJumps, `steps]
  let plain ← plainNames.mapM idx
  let mut vals : Array Expr := plain.toArray.map (args[·]!)
  let iRegs ← idx `regs
  let regs := args[iRegs]!
  unless regs.isAppOfArity ``Regs.mk 7 do throwError "vm_loop: the registers are not written out"
  vals := vals.push (regs.getArg! 5)
  let iStack ← idx `stack
  let mut stk := args[iStack]!
  let mut entries : Array (Expr → Expr) := #[]
  for _ in [0:k] do
    unless stk.isAppOfArity ``Array.push 3 do throwError "vm_loop: fewer than {k} stack entries written out"
    let some (p, f) := stackPayload? (stk.getArg! 2) | throwError "vm_loop: a top stack entry is not a slice, cell, builder or integer"
    vals := vals.push p
    entries := entries.push f
    stk := stk.getArg! 1
  -- the payloads were pushed top first
  let nPlain := plain.length
  let top := vals.extract (nPlain + 1) vals.size
  vals := (vals.extract 0 (nPlain + 1)) ++ top.reverse
  let es := entries.reverse
  let base := stk
  let fill (xs : Array Expr) : Expr := Id.run do
    let mut a := args
    for j in [0:nPlain] do a := a.set! plain[j]! xs[j]!
    a := a.set! iRegs (mkAppN regs.getAppFn (regs.getAppArgs.set! 5 xs[nPlain]!))
    let mut s := base
    for j in [0:es.size] do
      s := mkApp3 (mkConst ``Array.push [0]) (mkConst ``Value) s (es[j]! xs[nPlain + 1 + j]!)
    a := a.set! iStack s
    return mkAppN S.getAppFn a
  return (vals, fill, 2)

/-- Destructs `h : ∃ x₁ ... xₙ, st = S[x] ∧ c` and substitutes `st`. -/
def destructInv (g : MVarId) (h : FVarId) : MetaM MVarId := do
  let mut g := g
  let mut h := h
  for _ in [0:64] do
    let ty ← g.withContext do whnfR (← instantiateMVars (← h.getType))
    if ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2 then
      let #[sg] ← g.cases h | throwError "vm_loop: cases"
      g := sg.mvarId
      h := sg.fields[0]!.fvarId!
      if ty.isAppOfArity ``Exists 2 then h := sg.fields[1]!.fvarId!
    else break
  subst g h

/-- Proves `∃ x₁ ... xₙ, S' = S[x] ∧ c` by unification (reducible) and `decide` or `omega`. -/
def solveInvExists (g : MVarId) : Lean.Elab.Tactic.TacticM Unit := do
  let mut g := g
  for _ in [0:64] do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    if ty.isAppOfArity ``Exists 2 then
      let α := ty.getArg! 0
      let p := ty.getArg! 1
      let w ← mkFreshExprMVar α
      let g' ← mkFreshExprMVar (mkApp p w).headBeta
      g.assign (← mkAppOptM ``Exists.intro #[α, p, w, g'])
      g := g'.mvarId!
    else
      let some (eq, c) := (if ty.isAppOfArity ``And 2 then some (ty.getArg! 0, ty.getArg! 1) else none)
        | throwError "vm_loop_close: not the invariant"
      let some (_, a, b) := eq.eq? | throwError "vm_loop_close: not an equation"
      unless ← withReducible (isDefEq a b) do throwError "vm_loop_close: the state is not the loop head"
      let hc ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars c)
      let r ← Lean.Elab.Tactic.run hc.mvarId! do
        Lean.Elab.Tactic.evalTactic (← `(tactic| first | decide | (simp only [freeNestedContJump]; omega)))
      unless r.isEmpty do throwError "vm_loop_close: the bound of the jump counter"
      g.assign (← mkAppM ``And.intro #[← mkEqRefl a, hc])
      return
  throwError "vm_loop_close: too many parts"

end TvmLean.Exec

namespace TvmLean

open Lean Meta in
/-- `vm_loop k`: at a loop head `S` (`VmState.atLoopHead`, where `vm_run` stops), the goal
`P (S.runWith exec n)` by the loop rule (`VmState.runWith_inv`) with the invariant "the state is
`S` but for the gas, the loaded cells, the counters of jumps (fewer than `freeNestedContJump`) and
steps, `c5`, and the payloads of the top `k` stack entries" (`k` = 1 by default). Leaves two goals:
the run out of fuel from such a state, and the run with one more step from such a state, with the
hypothesis `ih` (the runs with at most as much fuel from any such state), which `vm_loop_close`
(the last resort of `vm_run`) applies when the run is back at the loop head. -/
elab "vm_loop" k:(num)? : tactic => Lean.Elab.Tactic.withMainContext do
  let k := (k.map (·.getNat)).getD 1
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_loop: no run in the goal"
  let exec := r.getArg! 0
  let n := r.getArg! 1
  let S := r.getArg! 2
  let (vals, fill, iChain) ← Exec.loopHoles S k
  let tys ← vals.mapM fun v => (inferType v : MetaM Expr)
  let stTy := mkConst ``VmState
  let inv ← withLocalDeclD `st stTy fun st => do
    let decls := (List.range vals.size).toArray.map fun i =>
      (Name.mkSimple s!"x{i}", fun (_ : Array Expr) => pure tys[i]!)
    let body ← withLocalDeclsD decls fun xs => do
      let bound ← mkAppM ``LT.lt #[xs[iChain]!, mkConst ``freeNestedContJump]
      let mut e ← mkAppM ``And #[← mkEq st (fill xs), bound]
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
  Exec.solveInvExists hinv.mvarId!
  let rule ← mkAppOptM ``VmState.runWith_inv #[exec, inv, motive, hz]
  let .forallE _ hsTy _ _ ← whnf (← inferType rule) | throwError "vm_loop: the loop rule"
  let hs ← mkFreshExprSyntheticOpaqueMVar hsTy
  let pf ← mkAppOptM ``VmState.runWith_inv #[exec, inv, motive, hz, hs, n, S, hinv]
  unless ← isDefEq (← inferType pf) t do throwError "vm_loop: the goal is not a property of the run"
  g.assign pf
  let (_, gz) ← hz.mvarId!.intro `st
  let (h0, gz) ← gz.intro `hinv
  let gz ← Exec.destructInv gz h0
  let (_, gs) ← hs.mvarId!.intro `n
  let (_, gs) ← gs.intro `st
  let (h1, gs) ← gs.intro `hinv
  let (_, gs) ← gs.intro `ih
  let gs ← Exec.destructInv gs h1
  Lean.Elab.Tactic.replaceMainGoal [gz, gs]

open Lean Meta in
/-- `vm_loop_close`: the run is back at the loop head of `vm_loop`: by the hypothesis `ih`, its fuel
at most that of `ih` (`omega`), its state the loop head with other parts (unification). -/
elab "vm_loop_close" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let some d := (← getLCtx).findFromUserName? `ih | throwError "vm_loop_close: no `ih`"
  let gs ← g.apply d.toExpr
  let mut rest := #[]
  for g' in gs do
    if ← g'.isAssigned then continue
    let ty ← whnfR (← instantiateMVars (← g'.getType))
    if ty.isAppOf ``LE.le then
      let r ← Lean.Elab.Tactic.run g' (do Lean.Elab.Tactic.evalTactic (← `(tactic| omega)))
      unless r.isEmpty do throwError "vm_loop_close: the fuel"
    else if ty.isAppOf ``Exists then
      Exec.solveInvExists g'
    else rest := rest.push g'
  Lean.Elab.Tactic.replaceMainGoal rest.toList

/-- The simp lemmas of a step (`Proofs/Exec/Tactic.lean`), with those of `vm_simp`. -/
syntax (name := vmStepSimp) "vm_step_simp" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| vm_step_simp $[[$args,*]]?) => do
    let args := args.getD ⟨#[]⟩
    `(tactic| set_option maxRecDepth 100000 in simp (config := { maxSteps := 2000000 }) (disch := vm_disch) only [
      TvmLean.Exec.runInstr, TvmLean.Exec.reduceInnerDispatchRun, TvmLean.Exec.unfoldModelRun,
      TvmLean.Exec.decodeCp0, TvmLean.Exec.codeBitsRemaining, TvmLean.Exec.codeRefsRemaining,
      TvmLean.Exec.codeOpcode24, TvmLean.Exec.codeRequiredVersion, TvmLean.Exec.stepCurrent,
      TvmLean.Exec.closedDictFacts, TvmLean.Exec.closedDictKeyBits, TvmLean.Exec.arrayLitPush,
      TvmLean.Exec.stepWithNone, TvmLean.Exec.foldIntSub, Stack.at, Stack.swap, cellCreateGasPrice,
      chksgnFreeCount, chksgnGasPrice, stackEntryGasPrice, freeStackDepth, tupleEntryGasPrice,
      VmState.registerChkSgnCall_eq, VM.pair_ite,
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

open Lean Meta Exec in
/-- `vm_split`: the first `if` of the goal (`Lean.Meta.findSplit?`). If the context and the bounds
of the symbolic load gas (`vm_load_bounds`) decide its condition (by linear arithmetic,
`proveByOmega?`: the gas left, the bounds of a slice), the `if`
is reduced to its branch without a new hypothesis; else the goal is split (`split`), each branch
with the condition or its negation as a hypothesis. A `match` on a value made of constructors
around a Boolean that is not a literal (`(.ok b, st)`, the flag a loop pops) is split on the cases
of the Boolean (`hvm_flag`), after which it reduces. Keeps the context of a run to the conditions
it does not decide, so that the next steps stay cheap. -/
elab "vm_split" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| vm_load_bounds))
  Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e ← findSplit? t | throwError "vm_split: no `if` or `match` to split"
  if e.isIte || e.isDIte then
    let c := e.getArg! 1 5
    -- a condition of `True` and `False` (left by an earlier rewrite of its parts): simplified
    if !c.hasFVar && !c.hasMVar && !c.isConstOf ``True && !c.isConstOf ``False &&
        (c.find? fun x => x.isAppOf ``True || x.isAppOf ``False).isSome then
      Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [and_self, and_true, true_and, and_false, false_and,
        or_true, true_or, or_false, false_or, not_true_eq_false, not_false_eq_true, if_true, if_false,
        dite_true, dite_false, ite_true, ite_false]))
      return
    let decided : Option (Bool × FVarId × MVarId) ←
      if c.isConstOf ``True || c.isConstOf ``False then pure none
      else if let some (h, g') ← assertByOmega? g (mkNot c) then pure (some (false, h, g'))
      else if let some (h, g') ← assertByOmega? g c then pure (some (true, h, g'))
      else pure none
    if let some (b, h, g') := decided then
      Lean.Elab.Tactic.replaceMainGoal [g']
      let hId := mkIdent (← g'.withContext h.getUserName)
      Lean.Elab.Tactic.withMainContext do
        if b then
          Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [$hId:ident, if_true, dite_true, ite_true,
            and_self, and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
            not_true_eq_false, not_false_eq_true, if_false, dite_false, ite_false]))
        else
          Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [$hId:ident, if_false, dite_false, ite_false,
            and_self, and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
            not_true_eq_false, not_false_eq_true, if_true, dite_true, ite_true]))
      Lean.Elab.Tactic.withMainContext do
        Lean.Elab.Tactic.evalTactic (← `(tactic| clear $hId:ident))
      return
  -- a `match` on a value built of constructors around a Boolean that is not a literal (the result
  -- `(.ok b, st)` of popping a flag): the cases of the Boolean, after which the `match` reduces
  if let some app ← matchMatcherApp? e then
    let mut found : Option Expr := none
    for d in app.discrs do
      if found.isNone then found ← boolInCtors? d 4
    if let some b := found then
      let gs ← g.generalize #[{ expr := b, xName? := `b, hName? := `hvm_flag }]
      let (fv, g') := (gs.1[0]!, gs.2)
      let cs ← g'.cases fv
      Lean.Elab.Tactic.replaceMainGoal (cs.map (·.mvarId)).toList
      let hId := mkIdent `hvm_flag
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals
        ((try simp only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not,
          Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true] at $hId:ident);
         (try vm_step_simp))))
      return
  Lean.Elab.Tactic.evalTactic (← `(tactic| split))

/-- One step of a run (`Proofs/Exec/Tactic.lean`): the goal mentions
`VmState.runWith execInstr (fuel + 1) st` (or `VmState.run`); it becomes the run after the step,
with the cases the step cannot decide as `if`s. Extra simp lemmas: `vm_step [h]`. -/
syntax (name := vmStep) "vm_step" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| vm_step $[[$args,*]]?) => do
    let args := args.getD ⟨#[]⟩
    `(tactic| ((try simp only [VmState.run_eq]); rw [VmState.runWith_succ']; (try simp only [TvmLean.Exec.stepWithNone]); vm_step_simp [$args,*]))

/-- A path whose conditions contradict each other is closed (`omega` on the hypotheses, with the
bounds of the symbolic gas of loads, `vm_load_bounds`). -/
macro "vm_prune" : tactic => `(tactic| first
  | (exfalso; vm_load_bounds; with_reducible omega)
  | (simp only [not_true_eq_false, not_false_eq_true, false_and, and_false, Bool.false_eq_true] at *; done))

/-- A path closed by a contradiction that is not arithmetic (a hypothesis `¬True`, `False`). -/
macro "vm_prune_cheap" : tactic => `(tactic| first
  | with_reducible contradiction
  | (simp only [not_true_eq_false, not_false_eq_true, false_and, and_false, Bool.false_eq_true] at *; done))

/-- The whole run (`Proofs/Exec/Tactic.lean`): one step at a time (`vm_step`); a case the step
cannot decide splits the goal (`split`), each branch with its condition as a hypothesis, and a
branch whose conditions contradict the hypotheses is closed (`vm_prune`). Goes on until every
run halts (or its fuel is not a successor): what is left is the goal of each halted path. Extra
simp lemmas: `vm_run [h]`. -/
syntax (name := vmRun) "vm_run" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| vm_run $[[$args,*]]?) => do
    let args := args.getD ⟨#[]⟩
    `(tactic| set_option maxRecDepth 100000 in repeat' (first
        | (vm_split <;> try vm_prune_cheap)
        | (vm_not_at_loop_head; vm_step [$args,*])
        | (vm_not_at_loop_head; vm_fuel <;> try simp only [VmState.runWith_zero, Excno.toInt])
        | (vm_has_run; vm_step_simp [$args,*])
        | vm_loop_close))

end TvmLean

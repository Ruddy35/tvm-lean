import Lean
-- BEGIN IMPORTS: written by tools/spec-coverage/spec_coverage.py (the modules of symbolic
-- execution, TvmLean/Proofs/Exec/ but its pilots, and the tactic of tools/contract-check)
import TvmLean.Proofs.Check.Tactic
import TvmLean.Proofs.Exec.Attr
import TvmLean.Proofs.Exec.Closure
import TvmLean.Proofs.Exec.Cont
import TvmLean.Proofs.Exec.Dict.Delete
import TvmLean.Proofs.Exec.Dict.Gas
import TvmLean.Proofs.Exec.Dict.Label
import TvmLean.Proofs.Exec.Dict.Loaded
import TvmLean.Proofs.Exec.Dict.Lookup
import TvmLean.Proofs.Exec.Dict.Map
import TvmLean.Proofs.Exec.Dict.Set
import TvmLean.Proofs.Exec.Dict.SetGet
import TvmLean.Proofs.Exec.Eval
import TvmLean.Proofs.Exec.Framed
import TvmLean.Proofs.Exec.FramedDict
import TvmLean.Proofs.Exec.IteInst
import TvmLean.Proofs.Exec.Load
import TvmLean.Proofs.Exec.LoopInv
import TvmLean.Proofs.Exec.Run
import TvmLean.Proofs.Exec.Spec.Arith
import TvmLean.Proofs.Exec.Spec.ArithExt
import TvmLean.Proofs.Exec.Spec.Cell
import TvmLean.Proofs.Exec.Spec.CellExt
import TvmLean.Proofs.Exec.Spec.Crypto
import TvmLean.Proofs.Exec.Spec.Dict
import TvmLean.Proofs.Exec.Spec.DictDel
import TvmLean.Proofs.Exec.Spec.DictSet
import TvmLean.Proofs.Exec.Spec.DictSetGet
import TvmLean.Proofs.Exec.Spec.Dispatch
import TvmLean.Proofs.Exec.Spec.Flow
import TvmLean.Proofs.Exec.Spec.Loop
import TvmLean.Proofs.Exec.Spec.Msg
import TvmLean.Proofs.Exec.Spec.MsgAddr
import TvmLean.Proofs.Exec.Spec.MsgExt
import TvmLean.Proofs.Exec.Spec.Stack
import TvmLean.Proofs.Exec.Spec.StackExt
import TvmLean.Proofs.Exec.Spec.TonEnv
import TvmLean.Proofs.Exec.Spec.Tuple
import TvmLean.Proofs.Exec.Step
import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.VM
-- END IMPORTS

/-!
# Which instructions symbolic execution runs, and how (`tools/spec-coverage`)

Run by `tools/spec-coverage/spec_coverage.py` (`lake env lean` on a copy of this file whose imports
it writes: every module of `TvmLean/Proofs/Exec/` but the pilots, and `TvmLean.Proofs.Check.Tactic`);
nothing here is part of the libraries. It reads the environment, as `vm_step` would
(`TvmLean/Proofs/Exec/Tactic.lean`, `runInstr`): an instruction runs by a lemma of the simp set
`vm_spec` whose instruction unifies with it (`applySpec`), else by its handler (`dispatchRun`: the
chain of `execInstr`'s dispatchers followed, then the run computed by the lemmas of `vm_run` and the
model's definitions unfolded where they run, `unfoldModelRun`).

For an instruction (decoded from a code cell, as the tactic decodes it) it prints

* the `vm_spec` lemmas whose instruction unifies with it (`withReducible isDefEq`, as `applySpec`),
  each with its module: the lemmas of the modules `TvmLean.Proofs.Check.Tactic` imports are those a
  module of `tools/contract-check` sees; the conditions on the state (the shape of the stack, a
  closed fact of the code) are not checked here — they are what a run must meet for the lemma to
  fire;
* its handler, statically: the VM programs it runs (the applications whose type is `VM _`), each
  computed by a lemma of `vm_run` (its left side `ExceptT.run (f ..) st`), or unfolded
  (`TvmLean.Exec.unfoldableModelDef`: a non-recursive definition of the model, then its body is
  looked into), or neither — a *blocker*: a recursive program, a combinator outside the model
  (`forIn`, `tryCatch`), an opaque definition. A handler with no blocker runs by unfolding (the
  conditions on unknown values left as `if`s and `match`es, which `vm_split` splits); one with a
  blocker leaves the run of that program unreduced in the goal.

`spec_coverage.py` runs it twice: importing `TvmLean.Proofs.Check.Tactic` only (contract-check's
environment: the lemmas that fire there, its `vm_run` set, the deep check), and importing every module
of `TvmLean/Proofs/Exec/` (the `vm_spec` lemmas a contract-check run would get from those modules).

Input and output are files named by environment variables:

* `SPEC_COVERAGE_MODE=inventory`: `SPEC_COVERAGE_IN` has lines
  `<form> <24-bit opcode in hex> [h] [d=<signature>]`; each opcode with a tail of 999 zero bits (else
  one bits) and four empty references is decoded and classified (`SAMPLE` lines; the handler analysed
  on the lines marked `h`; with `d=`, the deep check on a stack of that signature, `DEEP` lines), and
  the `vm_spec` lemmas are listed (`SPEC` lines).
* `SPEC_COVERAGE_MODE=precheck`: `SPEC_COVERAGE_IN` has lines `<name> <path of a BOC file>`; the code
  reachable from the BOC's first root (the code cells, the implicit `JMPREF`s, the continuations of
  `PUSHCONT`, `CALLREF`, `IF*REF`, ..., the procedures of `DICTPUSHCONST`) is decoded and each
  instruction classified (`INSTR` lines; `CODE` lines for the ends of the code); with
  `SPEC_COVERAGE_HANDLER=0`, the lemmas only.

Fields are separated by tabs; lists by `;`.
-/

namespace TvmLean.SpecCoverage

open Lean Meta

/-! ## The environment -/

/-- The modules `root` imports, directly or not, and itself. -/
def importClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let names := env.allImportedModuleNames
  let data := env.header.moduleData
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:names.size] do
    idx := idx.insert names[i]! i
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  for _ in [0:1000000] do
    let some m := todo.back? | break
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if let some i := idx[m]? then
      for imp in data[i]!.imports do
        todo := todo.push imp.module
  return seen

/-- The module that declares `n`. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.allImportedModuleNames[i.toNat]!
  | none => env.mainModule

/-- One line of the output: the fields, tabs and newlines inside them made spaces. -/
def line (fields : List String) : String :=
  "\t".intercalate (fields.map fun f => (f.replace "\t" " ").replace "\n" " ")

/-- An expression, printed on one line (at most `n` characters). -/
def pp (e : Expr) (n : Nat := 160) : MetaM String := do
  let s := toString (← ppExpr e)
  let s := " ".intercalate ((s.splitOn "\n").map String.trim)
  return if s.length > n then s.take n ++ "…" else s

/-! ## The lemmas of `vm_spec` -/

/-- A lemma of `vm_spec`: its name, module, whether a module of `tools/contract-check` sees it,
the instruction of its left side, and its conditions. -/
structure SpecLemma where
  name : Name
  module : Name
  inCheck : Bool
  instr : String
  conds : Array String

/-- The kind of a condition of a specification: an equation of the stack or of another part of the
state (`stack`, `regs.c0`, ...), a closed fact of the code (`closed: dictLookupLoads`), or another
condition (printed). -/
def condKind (st : Expr) (t : Expr) : MetaM String := do
  let t ← instantiateMVars t
  for f in [``dictLookupLoads, ``dictKeyBits?] do
    if (t.find? (·.isConstOf f)).isSome then return s!"closed:{f}"
  if let some (_, a, _) := t.eq? then
    -- a projection chain of the state: `st.stack`, `st.regs.c0`, ...
    let mut x := a
    let mut path : List String := []
    for _ in [0:8] do
      if x == st then break
      let .const f _ := x.getAppFn | break
      let some info ← getProjectionFnInfo? f | break
      path := (match f with | .str _ s => s | _ => toString f) :: path
      x := x.getArg! info.numParams
    if x == st && !path.isEmpty then return s!"state:{".".intercalate path}"
  return s!"cond:{← pp t 100}"

/-- The lemmas of `vm_spec`, with what `condKind` says of their conditions. -/
def specLemmas (inCheck : NameSet) : MetaM (Array SpecLemma) := do
  let some ext ← getSimpExtension? `vm_spec | throwError "no simp set vm_spec"
  let thms ← ext.getTheorems
  let env ← getEnv
  let mut out := #[]
  for thm in thms.post.values ++ thms.pre.values do
    let name := thm.origin.key
    let val ← thm.getValue
    let ty ← inferType val
    let r ← forallTelescopeReducing ty fun xs concl => do
      let some (_, lhs, _) := concl.eq? | return none
      unless lhs.isAppOf ``ExceptT.run && lhs.getAppNumArgs == 5 do return none
      let st := lhs.getArg! 4
      let m := lhs.getArg! 3
      let instr ← if m.isAppOfArity ``execInstr 1 then pp m.appArg! else pp m
      let mut conds := #[]
      for x in xs do
        let xt ← inferType x
        if ← isProp xt then conds := conds.push (← condKind st xt)
      return some (instr, conds)
    let some (instr, conds) := r | continue
    let mod := moduleOf env name
    out := out.push { name, module := mod, inCheck := inCheck.contains mod, instr, conds }
  return out

/-- The `vm_spec` lemmas whose left side unifies with the run of `iE` on a state (as `applySpec`). -/
def matchingSpecs (iE : Expr) : MetaM (Array Name) := do
  let some ext ← getSimpExtension? `vm_spec | return #[]
  let thms ← ext.getTheorems
  withLocalDeclD `st (mkConst ``VmState) fun st => do
    let run ← mkAppM ``ExceptT.run #[← mkAppM ``execInstr #[iE]]
    let e := mkApp run st
    let cands := (← thms.post.getMatch e) ++ (← thms.pre.getMatch e)
    let mut out := #[]
    for thm in cands do
      let s ← saveState
      let ok ← try
          let val ← thm.getValue
          let (_, _, concl) ← forallMetaTelescopeReducing (← inferType val)
          let some (_, lhs, _) := concl.eq? | pure false
          withReducible (isDefEq lhs e)
        catch _ => pure false
      s.restore
      if ok && !out.contains thm.origin.key then out := out.push thm.origin.key
    return out

/-! ## The handler of an instruction -/

/-- The programs a lemma of `vm_run` runs (`ExceptT.run (f ..) st`: `f`), and the definitions
`vm_run` unfolds. -/
def vmRunHeads : MetaM NameSet := do
  let some ext ← getSimpExtension? `vm_run | throwError "no simp set vm_run"
  let thms ← ext.getTheorems
  let mut heads : NameSet := {}
  for n in thms.toUnfold.toList do
    heads := heads.insert n
  for thm in thms.post.values ++ thms.pre.values do
    let val ← thm.getValue
    let some f ← forallTelescopeReducing (← inferType val) (fun _ concl => do
        let some (_, lhs, _) := concl.eq? | return none
        unless lhs.isAppOf ``ExceptT.run && lhs.getAppNumArgs ≥ 4 do return none
        return (lhs.getArg! 3).getAppFn.constName?)
      | continue
    heads := heads.insert f
  return heads

/-- Whether `e` is a VM program (its type `VM α`, i.e. `ExceptT Excno (StateM VmState) α`). -/
def isVMProgram (e : Expr) : MetaM Bool := do
  try
    let t ← whnfR (← inferType e)
    return t.isAppOfArity ``ExceptT 3 && (t.getArg! 0).isConstOf ``Excno
  catch _ => return false

/-- What the analysis of a handler found. -/
structure Found where
  /-- Programs computed by a lemma of `vm_run`. -/
  byLemma : NameSet := {}
  /-- Definitions of the model unfolded. -/
  unfolded : NameSet := {}
  /-- Programs neither computed nor unfolded, with why. -/
  blockers : Std.HashMap Name String := {}

/-- Why the program `c` is neither computed by a lemma of `vm_run` nor unfolded. -/
def blockReason (c : Name) : MetaM String := do
  if !(`TvmLean).isPrefixOf c && !TvmLean.Exec.isModelPrivate c then
    return "outside the model, no vm_run lemma"
  if c == ``VM.jump || c == ``VM.call || c == ``VM.callComputeStacks then return "jump/call, no vm_run lemma"
  match (← getEnv).find? c with
  | some (.defnInfo _) => return "recursive, no vm_run lemma"
  | some (.opaqueInfo _) => return "opaque"
  | some (.axiomInfo _) => return "axiom"
  | _ => return "not a definition"

/-- The constants that only shape a program (their branches are looked into): `match`es, `if`s. -/
def isStructural (c : Name) : MetaM Bool := do
  if isMatcherCore (← getEnv) c then return true
  return c == ``ite || c == ``dite || c == ``cond || c.isStr && (c.getString! == "casesOn" || c.getString! == "rec")

/-- Looks into the program `e` (at most `fuel` binders and unfoldings deep, `budget` subterms in
all): every VM program it runs is computed by a lemma of `vm_run`, unfolded (`unfoldableModelDef`,
its body looked into once), a dispatcher (followed, `followDispatch`), structural, or a blocker. -/
def scan (heads : NameSet) (found : IO.Ref Found) (budget : IO.Ref Nat) : Nat → Expr → MetaM Unit
  | 0, _ => pure ()
  | fuel + 1, e => do
    let b ← budget.get
    if b == 0 then return
    budget.set (b - 1)
    match e with
    | .mdata _ x => scan heads found budget fuel x
    | .proj _ _ x => scan heads found budget fuel x
    | .lam .. => lambdaTelescope e fun _ body => scan heads found budget fuel body
    | .letE .. => lambdaLetTelescope e fun _ body => scan heads found budget fuel body
    | .app .. | .const .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .const c _ := f then
        if ← isVMProgram e then
          if TvmLean.Exec.isDispatcher c then
            if let some e' ← withTransparency .all (TvmLean.Exec.followDispatch e) then
              if e' != e then
                scan heads found budget fuel e'
                return
          if heads.contains c then
            found.modify fun s => { s with byLemma := s.byLemma.insert c }
          else if ← isStructural c then
            pure ()
          else if ← TvmLean.Exec.unfoldableModelDef c then
            unless (← found.get).unfolded.contains c do
              found.modify fun s => { s with unfolded := s.unfolded.insert c }
              let ci ← getConstInfo c
              if let some v := ci.value? then
                scan heads found budget fuel v
          else
            let r ← blockReason c
            found.modify fun s => { s with blockers := s.blockers.insert c r }
      else
        scan heads found budget fuel f
      for a in args do
        scan heads found budget fuel a
    | _ => pure ()

/-- The handler of the instruction `iE` (`execInstr iE`, the dispatchers followed), analysed. -/
def analyseHandler (heads : NameSet) (iE : Expr) : MetaM Found := do
  let m ← mkAppM ``execInstr #[iE]
  let some h ← withTransparency .all (TvmLean.Exec.followDispatch m)
    | return { blockers := ({} : Std.HashMap Name String).insert ``execInstr "dispatch not followed" }
  let found ← IO.mkRef ({} : Found)
  let budget ← IO.mkRef 20000
  scan heads found budget 64 h
  found.get

/-- Runs `x` within `hb` thousand heartbeats; `none` if it fails or runs out of them. -/
def guarded {α : Type} (hb : Nat) (x : MetaM α) : MetaM (Option α) := do
  let s ← saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := hb * 1000 }) do
      return some (← x))
    (fun _ => do s.restore; return none)

/-- The fields of the classification of an instruction: its text, the `vm_spec` lemmas that unify
(those a module of `tools/contract-check` sees, the others), and, with `handler`, the handler
(`unfold` or `blocked`), its blockers and the programs computed by `vm_run`'s lemmas (else `-`). -/
def classify (heads : NameSet) (inCheck : NameSet) (cache : IO.Ref (Std.HashMap String (List String)))
    (handler : Bool) (i : Instr) : MetaM (List String) := do
  let key := toString i ++ (if handler then "|h" else "")
  if let some r := (← cache.get)[key]? then return r
  let iE := toExpr i
  let specs ← match ← guarded 2000 (matchingSpecs iE) with
    | some r => pure r
    | none => pure #[`timeout]
  let env ← getEnv
  let (sc, sl) := specs.partition fun n => inCheck.contains (moduleOf env n)
  let hs ← if handler then do
      let found ← match ← guarded 20000 (analyseHandler heads iE) with
        | some f => pure f
        | none => pure { blockers := ({} : Std.HashMap Name String).insert `analysis "the analysis ran out of heartbeats" }
      let blockers := found.blockers.toList.map fun (n, r) => s!"{n} ({r})"
      pure [if found.blockers.isEmpty then "unfold" else "blocked", ";".intercalate blockers,
        ";".intercalate (found.byLemma.toList.map toString)]
    else pure ["-", "", ""]
  let r := [toString i, ";".intercalate (sc.toList.map toString), ";".intercalate (sl.toList.map toString)] ++ hs
  cache.modify (·.insert key r)
  return r

/-! ## Running an instruction on a symbolic state (`deep`) -/

end TvmLean.SpecCoverage

namespace TvmLean.SpecCoverage

open Lean Meta

/-- The run of an instruction by a lemma of `vm_spec` only (`TvmLean.Exec.applySpec`, the first
half of `vm_step`'s `runInstr`). -/
simproc specOnly (@ExceptT.run Excno (StateM VmState) _ (execInstr _) _) := fun e => do
  match ← TvmLean.Exec.applySpec e with
  | some r => return .visit r
  | none => return .continue

/-- The value of a stack entry of the signature letter `c` from the variable `x`: an integer, a
slice, a cell, a builder, a plain continuation on the code `x` (as `PUSHCONT` makes), a tuple, any
value, null. -/
def entryOf (c : Char) (x : Expr) : Expr :=
  match c with
  | 'I' => mkApp (mkConst ``Value.int) (mkApp (mkConst ``IntVal.num) x)
  | 'S' => mkApp (mkConst ``Value.slice) x
  | 'C' => mkApp (mkConst ``Value.cell) x
  | 'B' => mkApp (mkConst ``Value.builder) x
  | 'K' => mkApp (mkConst ``Value.cont)
      (mkApp4 (mkConst ``Continuation.ordinary) x (mkApp (mkConst ``Continuation.quit) (toExpr (0 : Int)))
        (mkConst ``OrdCregs.empty) (mkConst ``OrdCdata.empty))
  | 'T' => mkApp (mkConst ``Value.tuple) x
  | 'N' => mkConst ``Value.null
  | _ => x

def entryType (c : Char) : Expr :=
  match c with
  | 'I' => mkConst ``Int
  | 'S' => mkConst ``Slice
  | 'C' => mkConst ``Cell
  | 'B' => mkConst ``Builder
  | 'K' => mkConst ``Slice
  | 'T' => mkApp (mkConst ``Array [0]) (mkConst ``Value)
  | _ => mkConst ``Value

/-- The goal `P (ExceptT.run (execInstr iE) st)` with `st` written out as a run from the compute
phase writes it: the stack `s` with entries of the signature `sig` on top (the top last), the
current continuation the rest of an unknown code, codepage 0, `c0` a plain return continuation, `c1`
`quit 1`, `c2` the exception handler `excQuit`, `c3` a plain continuation (the code's root), `c7`
the one-entry tuple of the compute phase; the rest unknown. -/
def withDeepGoal {α : Type} [Inhabited α] (iE : Expr) (sig : String) (k : MVarId → MetaM α) : MetaM α := do
  let resTy ← mkAppM ``Prod #[← mkAppM ``Except #[mkConst ``Excno, mkConst ``Unit], mkConst ``VmState]
  let fixed : Array (Name × Expr) := #[(`s, mkConst ``Stack), (`st0, mkConst ``VmState), (`rc, mkConst ``Slice),
    (`root, mkConst ``Slice), (`rest, mkConst ``Slice), (`c4, mkConst ``Cell), (`c5, mkConst ``Cell),
    (`c7v, mkConst ``Value), (`P, ← mkArrow resTy (mkSort 0))]
  let entries := sig.toList.filter (· != 'N')
  let decls := fixed ++ (entries.toArray.mapIdx fun j c => (Name.mkSimple s!"x{j}", entryType c))
  withLocalDeclsDND decls fun xs => do
    let s := xs[0]!
    let st0 := xs[1]!
    let mut stk := s
    let mut j := 0
    for c in sig.toList do
      let v := if c == 'N' then entryOf c s else entryOf c xs[fixed.size + j]!
      if c != 'N' then j := j + 1
      stk := mkApp3 (mkConst ``Array.push [0]) (mkConst ``Value) stk v
    let quit (n : Int) := mkApp (mkConst ``Continuation.quit) (toExpr n)
    let plain (code : Expr) := mkApp4 (mkConst ``Continuation.ordinary) code (quit 0)
      (mkConst ``OrdCregs.empty) (mkConst ``OrdCdata.empty)
    let c7 := mkApp3 (mkConst ``Array.push [0]) (mkConst ``Value) (mkApp (mkConst ``Array.empty [0]) (mkConst ``Value)) xs[7]!
    let regs := mkAppN (mkConst ``Regs.mk) #[plain xs[2]!, quit 1, mkConst ``Continuation.excQuit, plain xs[3]!,
      xs[5]!, xs[6]!, c7]
    let fields := getStructureFields (← getEnv) ``VmState
    let mut args : Array Expr := #[]
    for f in fields do
      if f == `stack then args := args.push stk
      else if f == `regs then args := args.push regs
      else if f == `cc then args := args.push (plain xs[4]!)
      else if f == `cp then args := args.push (toExpr (0 : Int))
      else args := args.push (← mkProjection st0 f)
    let st := mkAppN (mkConst ``VmState.mk) args
    let run := mkApp (← mkAppM ``ExceptT.run #[← mkAppM ``execInstr #[iE]]) st
    let g ← mkFreshExprSyntheticOpaqueMVar (mkApp xs[8]! run)
    k g.mvarId!

/-- What is left of a run after `simp`: `none` if the goals mention no `execInstr` and no run of
a program (`ExceptT.run`), else the programs left. -/
def leftPrograms (gs : List MVarId) : MetaM (Array String) := do
  let out ← IO.mkRef (#[] : Array String)
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    if (t.find? (·.isConstOf ``execInstr)).isSome then out.modify (·.push "execInstr")
    t.forEach' fun x => do
      if x.isAppOf ``ExceptT.run && x.getAppNumArgs ≥ 4 then
        let h := (x.getArg! 3).getAppFn
        let n := match h with
          | .const c _ => toString c
          | .fvar _ => "a variable program"
          | _ => "a program"
        out.modify fun a => if a.contains n then a else a.push n
      return true
  out.get

/-- The recursive definitions of the model applied in the goals (their results stay terms), and
the number of `if`s and `match`es (the cases a run splits on). -/
def opaqueTerms (gs : List MVarId) : MetaM (Array String × Nat) := do
  let env ← getEnv
  let mut out : Array String := #[]
  let mut cases := 0
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    let r ← IO.mkRef ((#[] : Array String), (0 : Nat))
    t.forEach fun x => do
      if x.isAppOf ``ite || x.isAppOf ``dite || (x.getAppFn.constName?.map (isMatcherCore env)).getD false then
        r.modify fun (a, n) => (a, n + 1)
    let _ ← t.forEach' fun x => do
      if let .const c _ := x.getAppFn then
        if (`TvmLean).isPrefixOf c && !env.isConstructor c && !(isStructure env c) then
          if let some (.defnInfo _) := env.find? c then
            unless (← TvmLean.Exec.unfoldableModelDef c) do
              let s := toString c
              r.modify fun (a, n) => (if a.contains s then a else a.push s, n)
      return true
    let (a, n) ← r.get
    out := a.foldl (fun acc s => if acc.contains s then acc else acc.push s) out
    cases := cases + n
  return (out, cases)

/-- Runs the tactic `tac` on `g` within `hb` thousand heartbeats and the recursion depth of a module
of tools/contract-check (100000): the goals left, or the error. -/
def runTac (g : MVarId) (tac : TSyntax `tactic) (hb : Nat) : MetaM (Except String (List MVarId)) := do
  let saved ← Core.getMessageLog
  let s ← saveState
  let r ← tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
        (fun ctx => { ctx with maxHeartbeats := hb * 1000, maxRecDepth := 100000 }) do
      let (gs, _) ← (Lean.Elab.Term.TermElabM.run (Lean.Elab.Tactic.run g (Lean.Elab.Tactic.evalTactic tac)))
      let msgs := (← Core.getMessageLog).toList
      if msgs.length > saved.toList.length && (msgs.drop saved.toList.length).any (·.severity == .error) then
        throwError "the tactic logged an error"
      return Except.ok gs)
    (fun ex => do
      s.restore
      let m ← ex.toMessageData.toString
      let m := if (m.splitOn "heartbeats").length > 1 then "heartbeats" else m
      return Except.error ((" ".intercalate (m.splitOn "\n")).take 80))
  modifyThe Core.State fun s => { s with messages := saved }
  return r

/-- The deep check of the instruction `iE` on a stack of signature `sig`: whether a `vm_spec` lemma
fires (`specOnly`), and what the handler's run (`vm_simp`) leaves: `computed` (no program left),
else the programs left; the recursive definitions whose results stay terms; the cases. -/
def deepCheck (iE : Expr) (sig : String) : MetaM (List String) := do
  let specR ← withDeepGoal iE sig fun g => do
    match ← runTac g (← `(tactic| simp (disch := vm_disch) only [TvmLean.SpecCoverage.specOnly])) 200000 with
    | .error _ => return "no"
    | .ok gs =>
      if (← leftPrograms gs).contains "execInstr" then return "no" else return "fires"
  let t0 ← IO.monoMsNow
  let handR ← withDeepGoal iE sig fun g => do
    match ← runTac g (← `(tactic| vm_simp)) 200000 with
    | .error m => return ["error", m, ""]
    | .ok gs =>
      let left ← leftPrograms gs
      let (opq, cases) ← opaqueTerms gs
      return [if left.isEmpty then s!"computed[{cases}]" else "stuck", ";".intercalate left.toList,
        ";".intercalate opq.toList]
  let dt := (← IO.monoMsNow) - t0
  return [specR] ++ handR ++ [s!"{dt}"]

/-! ## Inventory: the forms of the decoder -/

/-- The code cell of a 24-bit opcode with a tail of 999 zero bits (`ones`: one bits) and four empty
references, as the decoder audit (`tools/audit/decoder`) builds them. -/
def sampleCell (op : Nat) (ones : Bool) : Cell :=
  Cell.mkOrdinary (natToBits op 24 ++ Array.replicate 999 ones) #[Cell.empty, Cell.empty, Cell.empty, Cell.empty]

def parseHex (s : String) : Option Nat :=
  s.foldl (fun acc ch => acc.bind fun a =>
    let d? := if '0' ≤ ch ∧ ch ≤ '9' then some (ch.toNat - '0'.toNat)
      else if 'a' ≤ ch ∧ ch ≤ 'f' then some (ch.toNat - 'a'.toNat + 10)
      else if 'A' ≤ ch ∧ ch ≤ 'F' then some (ch.toNat - 'A'.toNat + 10) else none
    d?.map (a * 16 + ·)) (some 0)

def inventory (inp out : System.FilePath) : MetaM Unit := do
  let env ← getEnv
  let inCheck := importClosure env `TvmLean.Proofs.Check.Tactic
  let heads ← vmRunHeads
  let cache ← IO.mkRef ({} : Std.HashMap String (List String))
  -- written as it goes (a crash of the process leaves the lines before it)
  let h ← IO.FS.Handle.mk out .write
  let emit (l : String) : IO Unit := do h.putStrLn l; h.flush
  emit (line ["HEADS", ";".intercalate (heads.toList.map toString)])
  for s in ← specLemmas inCheck do
    emit (line ["SPEC", toString s.name, toString s.module, if s.inCheck then "1" else "0",
      s.instr, ";".intercalate s.conds.toList])
  for l in (← IO.FS.lines inp) do
    let parts := (l.splitOn " ").filter (· ≠ "")
    if parts.length < 2 then continue
    let form := parts[0]!
    let hex := parts[1]!
    let handler := parts.contains "h"
    let deepSig := (parts.find? (·.startsWith "d=")).map (·.drop 2)
    let some op := parseHex hex | continue
    let dec := match decodeCp0WithBits (Slice.ofCell (sampleCell op false)) with
      | .ok r => Except.ok r
      | .error _ => decodeCp0WithBits (Slice.ofCell (sampleCell op true))
    match dec with
    | .error e => emit (line ["SAMPLE", form, hex, s!"{cp0RequiredVersion op}", "decode-error", s!"{repr e}"])
    | .ok (i, _, _) =>
      let r ← classify heads inCheck cache handler i
      emit (line (["SAMPLE", form, hex, s!"{cp0RequiredVersion op}", "ok"] ++ r))
      if let some sig := deepSig then
        let d ← deepCheck (toExpr i) sig
        emit (line (["DEEP", form, hex, sig] ++ d))
  emit "END"

/-! ## Precheck: the code of a contract -/

/-- The leaves of a dictionary with `n`-bit keys (the values as slices, with their keys), at most
`fuel` nodes deep. -/
def dictLeaves : Nat → Cell → Nat → BitString → Array (BitString × Slice)
  | 0, _, _, _ => #[]
  | fuel + 1, c, n, pfx =>
    match parseDictLabel c n with
    | .error _ => #[]
    | .ok lbl =>
      let key := pfx ++ dictLabelBits lbl
      let rem := n - lbl.len
      if rem == 0 then #[(key, lbl.remainder.advanceBits lbl.storedBits)]
      else
        let s := lbl.remainder.advanceBits lbl.storedBits
        if s.refsRemaining < 2 then #[]
        else
          dictLeaves fuel (s.cell.refs[s.refPos]!) (rem - 1) (key.push false) ++
            dictLeaves fuel (s.cell.refs[s.refPos + 1]!) (rem - 1) (key.push true)

/-- A key as a signed integer (two's complement, the method ids of `DICTPUSHCONST`). -/
def keyInt (k : BitString) : Int :=
  let u := bitsToNat k
  if k.size > 0 && k[0]! then (u : Int) - (2 ^ k.size : Nat) else u

/-- The 24-bit opcode at the start of `s` (zero-padded, as `cp0RequiredVersion` reads it). -/
def op24 (s : Slice) : Nat :=
  let head := s.readBits (min 24 s.bitsRemaining)
  bitsToNat (head ++ Array.replicate (24 - head.size) false)

def hex6 (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.mk (List.replicate (6 - digits.length) '0' ++ digits)

/-- The code slices an instruction carries (its continuations), with a label each. -/
def codeOf (i : Instr) : Array (String × Slice) :=
  match i with
  | .pushCont c => #[("PUSHCONT", c)]
  | .pushRefCont c => #[("PUSHREFCONT", Slice.ofCell c)]
  | .ifref c => #[("IFREF", c)]
  | .ifnotref c => #[("IFNOTREF", c)]
  | .ifjmpref c => #[("IFJMPREF", c)]
  | .ifnotjmpref c => #[("IFNOTJMPREF", c)]
  | .ifrefElse c => #[("IFREFELSE", c)]
  | .ifelseRef c => #[("IFELSEREF", c)]
  | .ifrefElseRef t f => #[("IFREFELSEREF.then", t), ("IFREFELSEREF.else", f)]
  | .callRef c => #[("CALLREF", c)]
  | .jmpRef c => #[("JMPREF", c)]
  | .jmpRefData c => #[("JMPREFDATA", c)]
  | .contExt (.ifbitjmpref _ c) => #[("IFBITJMPREF", c)]
  | .contExt (.ifnbitjmpref _ c) => #[("IFNBITJMPREF", c)]
  | _ => #[]

/-- Walks the code from the slice `s` (labelled `loc`), at most `fuel` continuations deep: each
instruction classified, the continuations it carries walked, the implicit `JMPREF` followed, the
procedures of a `DICTPUSHCONST` walked (not those of a prefix dictionary, `PFXDICTSWITCH`).
`seen`: the slices walked (by cell and position); `out`: the lines printed. -/
def walk (name : String) (classifyI : Instr → MetaM (List String)) (seen : IO.Ref (Array (Cell × Nat × Nat)))
    (out : IO.Ref (Array String)) : Nat → String → Slice → MetaM Unit
  | 0, _, _ => pure ()
  | fuel + 1, loc, s0 => do
    if (← seen.get).any (fun (c, b, r) => b == s0.bitPos && r == s0.refPos && c == s0.cell) then return
    seen.modify (·.push (s0.cell, s0.bitPos, s0.refPos))
    let mut s := s0
    for _ in [0:2000] do
      if s.bitsRemaining == 0 then
        if s.refsRemaining == 0 then
          out.modify (·.push (line ["CODE", name, loc, "implicit RET"]))
        else
          out.modify (·.push (line ["CODE", name, loc, "implicit JMPREF"]))
          walk name classifyI seen out fuel s!"{loc}.refs[{s.refPos}]" (Slice.ofCell s.cell.refs[s.refPos]!)
        return
      let here := s!"{loc}@{s.bitPos}"
      match decodeCp0WithBits s with
      | .error e =>
        out.modify (·.push (line ["CODE", name, here, s!"no instruction decodes ({repr e})"]))
        return
      | .ok (i, _, rest) =>
        let r ← classifyI i
        let op := op24 s
        out.modify (·.push (line (["INSTR", name, here, hex6 op, s!"{cp0RequiredVersion op}"] ++ r)))
        for (what, c) in codeOf i do
          let loc' := if c.cell == s.cell then here else s!"{here}:{what}"
          walk name classifyI seen out fuel loc' c
        match i with
        | .dictPushConst d n =>
          for (k, v) in dictLeaves (n + 2) d n #[] do
            walk name classifyI seen out fuel s!"{here}:proc[{keyInt k}]" v
        | _ => pure ()
        s := rest

def precheck (inp out : System.FilePath) : MetaM Unit := do
  let env ← getEnv
  let inCheck := importClosure env `TvmLean.Proofs.Check.Tactic
  let heads ← vmRunHeads
  let cache ← IO.mkRef ({} : Std.HashMap String (List String))
  let handler := (← IO.getEnv "SPEC_COVERAGE_HANDLER") != some "0"
  let mut lines : Array String := #[]
  for s in ← specLemmas inCheck do
    lines := lines.push (line ["SPEC", toString s.name, toString s.module, if s.inCheck then "1" else "0",
      s.instr, ";".intercalate s.conds.toList])
  for l in (← IO.FS.lines inp) do
    let parts := (l.splitOn " ").filter (· ≠ "")
    let [name, path] := parts | continue
    let bytes ← IO.FS.readBinFile path
    match stdBocDeserializeMulti bytes with
    | .error _ => lines := lines.push (line ["CODE", name, "-", "BOC not read"])
    | .ok roots =>
      let some root := roots[0]? | continue
      let seen ← IO.mkRef #[]
      let outR ← IO.mkRef #[]
      walk name (classify heads inCheck cache handler) seen outR 64 "code" (Slice.ofCell root)
      lines := lines ++ (← outR.get)
  lines := lines.push "END"
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")

end TvmLean.SpecCoverage

-- as a module of tools/contract-check sets them around its theorems
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
open TvmLean.SpecCoverage in
#eval show Lean.MetaM Unit from do
  let mode := (← IO.getEnv "SPEC_COVERAGE_MODE").getD ""
  let some inp ← IO.getEnv "SPEC_COVERAGE_IN" | throwError "SPEC_COVERAGE_IN is not set"
  let some out ← IO.getEnv "SPEC_COVERAGE_OUT" | throwError "SPEC_COVERAGE_OUT is not set"
  match mode with
  | "inventory" => inventory inp out
  | "precheck" => precheck inp out
  | m => throwError "SPEC_COVERAGE_MODE: inventory or precheck, not `{m}`"
  -- the output is written: exit at once, not after the kernel has checked the auxiliary lemmas the
  -- runs made (`decide` on large literals of the samples takes the kernel up to an hour)
  IO.Process.exit 0

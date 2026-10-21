import TvmLean.Proofs.Exec.VM

/-!
# Running an instruction on a symbolic state: `vm_simp`

`execInstr i` is a chain of dispatchers, one per instruction family (`execInstrStack i <|
execInstrCont i <| ...`), each matching on the instruction and passing it to the next one
otherwise. For a known instruction (a constructor, its arguments may be unknown) the simproc
`reduceExecInstrRun` follows the chain in `ExceptT.run (execInstrX i next) st` to the handler of
`i`, by unfolding the dispatchers and reducing their `match` (a definitional step, no proof term).
Some dispatchers read the state before passing on (`execInstrFlowRunvm` reads the gas): their
`get` is run by `VM.run_bind` and `VM.run_get`, and the chain is followed again.

A helper of the model that no lemma of `vm_run` computes is unfolded where it is run
(`unfoldModelRun`), if it is not recursive; the jumps (`VM.jump`, `VM.call`) are left to their
lemmas, as unfolded on an unknown continuation they only grow.

`vm_simp` is `simp` with these simprocs, the lemmas of the simp set `vm_run` (the monad and the
primitives, `Proofs/Exec/VM.lean`) and the arithmetic of stack indices, with `omega` to decide the
conditions on stack depths (`vm_disch`), each branch of an `if` simplified knowing its condition:
on a state whose stack is known on top (`s.push a`), the run of an instruction computes to its
result, with the conditions it cannot decide left as `if`s.
-/

namespace TvmLean.Exec

open Lean Meta Simp

/-- The dispatchers of `execInstr`: `TvmLean.execInstr*` (each matches on the instruction and
passes it on, `execInstrFlowRunvm` after reading the gas). -/
def isDispatcher (n : Name) : Bool :=
  match n with
  | .str p s => p == `TvmLean && s.startsWith "execInstr"
  | _ => false

/-- Follows the chain of dispatchers from `m` (an application of a dispatcher to an instruction)
to the first term whose head is not a dispatcher: the handler's program, or a `bind` of a
dispatcher that reads the state. At most `fuel` unfoldings. -/
def followDispatch (m : Expr) (fuel : Nat := 5000) : MetaM (Option Expr) := do
  let mut cur := m
  for _ in [0:fuel] do
    let some f := cur.getAppFn.constName? | return some cur
    if !isDispatcher f then return some cur
    let some cur' ← unfoldDefinition? cur | return none
    cur ← whnfCore cur'
  return none

/-- `ExceptT.run (d i next) st` for a dispatcher `d` and an instruction `i` whose constructor is
known: the run of what the chain of dispatchers gives `i` to. -/
dsimproc reduceExecInstrRun (@ExceptT.run Excno (StateM VmState) _ _ _) := fun e => do
  let args := e.getAppArgs
  unless e.isAppOf ``ExceptT.run && args.size == 5 do return .continue
  let m := args[3]!
  let some f := m.getAppFn.constName? | return .continue
  unless isDispatcher f do return .continue
  -- the instruction must be a constructor application for the matches to reduce
  unless m.getAppArgs.any (fun a => a.getAppFn.isConst && a.getAppFn.constName!.getPrefix == ``TvmLean.Instr) do
    return .continue
  match ← withTransparency .all (followDispatch m) with
  | some m' => if m' == m then return .continue else return .visit (mkAppN e.getAppFn (args.set! 3 m'))
  | none => return .continue

/-- Whether the definition `n` may be unfolded where no lemma computes it: a function of the model
(namespace `TvmLean`), not recursive (its value uses no recursor, `brecOn` or well-founded
fixpoint), so that unfolding it terminates, and not one of the jumps (`VM.jump`, `VM.call`). -/
def unfoldableModelDef (n : Name) : MetaM Bool := do
  unless (`TvmLean).isPrefixOf n do return false
  -- jumps and calls are computed by the lemmas of `vm_run` for the continuations they cover;
  -- unfolded on an unknown continuation they only grow
  if n == ``VM.jump || n == ``VM.call || n == ``VM.callComputeStacks then return false
  let some (.defnInfo info) := (← getEnv).find? n | return false
  let recursive := info.value.find? (fun e => match e with
    | .const c _ => c == n || c == ``WellFounded.fix || c.isStr && (c.getString! == "rec" ||
        c.getString! == "brecOn" || c.getString! == "binductionOn")
    | _ => false)
  return recursive.isNone

/-- `ExceptT.run (f args) st` for a VM program `f args` of the model that no lemma of `vm_run`
computes (simp tries the lemmas first): `f` unfolded, if it may be (`unfoldableModelDef`). -/
dsimproc unfoldModelRun (@ExceptT.run Excno (StateM VmState) _ _ _) := fun e => do
  let args := e.getAppArgs
  unless e.isAppOf ``ExceptT.run && args.size == 5 do return .continue
  let m := args[3]!
  let some f := m.getAppFn.constName? | return .continue
  if isDispatcher f then return .continue
  unless ← unfoldableModelDef f do return .continue
  match ← withTransparency .all (unfoldDefinition? m) with
  | some m' => return .visit (mkAppN e.getAppFn (args.set! 3 m'.headBeta))
  | none => return .continue

end TvmLean.Exec

namespace TvmLean

/-- The discharger of `vm_simp`: a hypothesis, linear arithmetic, or `simp` with the hypotheses. -/
macro "vm_disch" : tactic =>
  `(tactic| first | assumption | omega | (simp (config := { decide := true }) only [*]; done))

/-- `simp` that runs a VM program on a state (`Proofs/Exec/Eval.lean`): the dispatch of
`execInstr`, the simp set `vm_run`, the conditions on the stack depth by `omega` (`vm_disch`).
Extra simp lemmas may be given: `vm_simp [h]`. -/
syntax (name := vmSimp) "vm_simp" (" [" Lean.Parser.Tactic.simpArg,* "]")? (Lean.Parser.Tactic.location)? :
  tactic

macro_rules
  | `(tactic| vm_simp $[[$args,*]]? $[$loc]?) => do
    let args := args.getD ⟨#[]⟩
    `(tactic| simp (config := { contextual := true }) (disch := vm_disch) only [TvmLean.Exec.reduceExecInstrRun,
        TvmLean.Exec.unfoldModelRun, vm_run, Array.size_push,
        Array.pop_push, Array.size_pop, if_pos, if_neg, dif_pos, dif_neg, if_true, if_false, dite_true,
        dite_false, Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false, ne_eq,
        Nat.add_sub_cancel, Nat.sub_self, Nat.add_one_sub_one, Nat.sub_zero, and_true, true_and,
        decide_eq_true_eq, decide_eq_false_iff_not, decide_not, Bool.not_not, Bool.not_true,
        Bool.not_false, Decidable.not_not, Bool.not_eq_true', Bool.not_eq_false', beq_iff_eq,
        Int.ofNat_eq_coe, Int.toNat_natCast, Bool.and_eq_true, Bool.or_eq_true, Bool.eq_false_iff, ite_not,
        $args,*]
        $[$loc]?)

end TvmLean

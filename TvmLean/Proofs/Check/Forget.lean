import TvmLean.Proofs.Check.Tactic
import TvmLean.Proofs.Exec.Framed

/-!
# Checking an invariant over all transactions: what no end of a path depends on

`ran_case` (TvmLean/Proofs/Check/Tactic.lean) runs a contract from a state whose `c7` is any value.
An instruction that writes `c7` (`RAND`, `SETRAND`: the seed, `SETGLOB`: a global) leaves it as a
term of the run (the seed a SHA-512 digest of the one before), which every later read of `c7`
(`NOW`, `LTIME`, `RAND` again) carries along. `check_forget_c7` makes it a variable again: a run
from a state with any `c7` there keeps the invariant, so the run from the state with that `c7` does
(the goal is the first applied to the term). The invariant is about the data only, and every read of
a `c7` that is a variable is a case of its own anyway: the paths are those of a run with any `c7`
from there.
-/

namespace TvmLean.Check

open Lean Meta Elab Tactic

/-- The register `c7` of the run in the goal `t` (`VmState.runWith exec fuel S`, `S` written out),
with the term to forget in it: the payload `P` of `#[.tuple P]` (one entry, the parameters), else the
register itself; `none` if it is a variable, or the variable parameters of `#[.tuple P]` or `#[v]`. -/
def c7ToForget? (t : Expr) : MetaM (Option Expr) := do
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | return none
  let S := r.getArg! 2
  unless S.isAppOfArity ``VmState.mk 20 do return none
  let fields := getStructureFields (← getEnv) ``VmState
  let some iR := fields.idxOf? `regs | return none
  let regs := S.getArg! iR
  unless regs.isAppOfArity ``Regs.mk 7 do return none
  let c7 := regs.getArg! 6
  if c7.isFVar || !c7.hasFVar then return none
  -- the one entry of `#[v]` (`List.toArray [v]`) or `#[].push v`
  let one? : Option Expr :=
    if c7.isAppOfArity ``Array.push 3 then
      let b := c7.getArg! 1
      if b.isAppOfArity ``List.toArray 2 && (b.getArg! 1).isAppOfArity ``List.nil 1 then some (c7.getArg! 2)
      else if b.isAppOfArity ``Array.empty 1 || b.isAppOfArity ``Array.mkEmpty 2 then some (c7.getArg! 2)
      else none
    else if c7.isAppOfArity ``List.toArray 2 then
      let l := c7.getArg! 1
      if l.isAppOfArity ``List.cons 3 && (l.getArg! 2).isAppOfArity ``List.nil 1 then some (l.getArg! 1)
      else none
    else none
  match one? with
  | some v =>
    if v.isFVar then return none
    if v.isAppOfArity ``Value.tuple 1 then
      let P := v.appArg!
      if P.isFVar || !P.hasFVar then return none
      return some P
    if !v.hasFVar then return none
    return some v
  | none => return some c7

/-- `check_forget_c7`: the register `c7` of the run in the goal, a term of the run (`RAND` wrote
its seed back), made a variable (`generalize`; its parameters only, when it is `#[.tuple params]`),
the hypotheses about what it was cleared (`vm_clear_unused`). Sound: the goal for every `c7` there
implies the goal. Fails if `c7` is a variable already (or its parameters are). -/
elab "check_forget_c7" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Keeps 2 || t.isAppOfArity ``KeepsActs 3 do
    throwError "check_forget_c7: not a run to keep"
  let some e ← c7ToForget? t | throwError "check_forget_c7: nothing to forget"
  let (_, g') ← g.generalize #[{ expr := e, xName? := `params }]
  replaceMainGoal [g']
  evalTactic (← `(tactic| vm_clear_unused))

end TvmLean.Check

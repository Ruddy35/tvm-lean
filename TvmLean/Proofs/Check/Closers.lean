import Lean

/-!
# Checking an invariant over all transactions: the closers of the ends of the paths

At the end of a path that commits, `ran_case` (TvmLean/Proofs/Check/Tactic.lean, `commitPath`) proves
the parts of the invariant the data left must satisfy: widths of fields, ranges the stores checked.
The context of a long path holds many facts `omega` reads (the ranges of the numbers read, of the
results of arithmetic, of the stores), most of them about other numbers; with all of them `omega`
may find a proof whose term nests deeper than the kernel checks (`deep recursion`). `check_omega_rel`
gives `omega` the facts that share a term with the goal only.
-/

namespace TvmLean.Check

open Lean Meta Elab Tactic

/-- The number of trailing arguments of an application of `n` that `omega` reads through
(arithmetic, comparisons, connectives, casts), or `none` for a function it takes as an atom. -/
def omegaReads (n : Name) : Option Nat :=
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow, ``LT.lt, ``LE.le,
      ``GT.gt, ``GE.ge, ``Eq, ``Ne, ``And, ``Or, ``Iff, ``Min.min, ``Max.max].contains n then some 2
  else if [``Not, ``Nat.cast, ``Int.cast, ``Int.toNat, ``Int.natAbs, ``Int.ofNat, ``Neg.neg,
      ``Nat.succ].contains n then some 1
  else none

/-- The atoms of `e` for `omega`: the maximal subterms it does not read through (applications of
other functions, variables), at most `depth` applications deep (deeper, the subterm is an atom);
literals are none. -/
def omegaAtoms (e : Expr) (acc : Array Expr := #[]) : (depth : Nat := 64) → Array Expr
  | 0 => if acc.contains e then acc else acc.push e
  | depth + 1 =>
    let e := e.consumeMData
    let add (a : Array Expr) : Array Expr := if a.contains e then a else a.push e
    if e.isRawNatLit || e.isLit then acc
    else match e.getAppFn with
      | .const n _ =>
        if n == ``OfNat.ofNat then acc
        else match omegaReads n with
          | some k =>
            let args := e.getAppArgs
            if args.size < k then add acc
            else (args.extract (args.size - k) args.size).foldl (fun a x => omegaAtoms x a depth) acc
          | none => add acc
      | _ => add acc

/-- `check_omega_rel`: `omega` with the hypotheses that share an atom with the goal (`omegaAtoms`),
the others cleared. Fails if the goal has no atom, or as `omega` does. -/
elab "check_omega_rel" : tactic => withMainContext do
  let g ← getMainGoal
  let goalAtoms := omegaAtoms (← instantiateMVars (← g.getType))
  if goalAtoms.isEmpty then throwError "check_omega_rel: no atom in the goal"
  let mut clear : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    unless (omegaAtoms ty).any goalAtoms.contains do clear := clear.push d.fvarId
  replaceMainGoal [← g.tryClearMany clear]
  evalTactic (← `(tactic| omega))

end TvmLean.Check

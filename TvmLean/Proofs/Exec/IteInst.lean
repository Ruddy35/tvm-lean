import Lean

/-!
# Fresh instances of `if`

`simp` rewrites the condition of an `if` by a definitional step (a projection of a state written out
reduced, a lemma proved by `rfl` such as `Int.toNat_natCast`) without touching its `Decidable`
instance, which keeps the old form of the condition. Every later unification of that `if` with a
lemma about `if` (`VmState.runCont_ite`, `VmState.instrEnd_ite`, `StepResult.state_ite`, …) checks
that the instance's type is that of the condition, by unfolding: in a run of wallet v3, the flag
`CHKSIGNU` pushes (`if chkSignU … then -1 else 0`, its instance stated with the state's
`globalVersion` and `(↑(bitsToNat …)).toNat`) cost 0.3 s a check, some 400 checks in one step.

`iteFreshInst` and `diteFreshInst` (simprocs for `vm_run`'s simp set) give such an `if` the instance
of its condition (`Decidable` is a subsingleton: `ite_inst_eq`, `dite_inst_eq`), once. With them the
run of `recv_external` from its signature check to the end (TvmLean/Proofs/Contracts/Wallet3Run/)
takes 44 s instead of 183 s.
-/

namespace TvmLean.Exec

open Lean Meta

theorem ite_inst_eq {α : Sort _} {c : Prop} (i₁ i₂ : Decidable c) (a b : α) :
    @ite α c i₁ a b = @ite α c i₂ a b := by
  cases Subsingleton.elim i₁ i₂; rfl

theorem dite_inst_eq {α : Sort _} {c : Prop} (i₁ i₂ : Decidable c) (a : c → α) (b : ¬c → α) :
    @dite α c i₁ a b = @dite α c i₂ a b := by
  cases Subsingleton.elim i₁ i₂; rfl

/-- An `if` whose instance is not stated for its condition gets the instance of its condition. -/
simproc iteFreshInst (@ite _ _ _ _ _) := fun e => do
  let_expr ite α c inst a b := e | return .continue
  let instTy ← instantiateMVars (← inferType inst)
  let_expr Decidable c' := instTy | return .continue
  if c' == c then return .continue
  let some inst' ← synthInstance? (mkApp (mkConst ``Decidable) c) | return .continue
  let u ← getLevel α
  let e' := mkApp5 (mkConst ``ite [u]) α c inst' a b
  let pf := mkAppN (mkConst ``ite_inst_eq [u]) #[α, c, inst, inst', a, b]
  return .done { expr := e', proof? := some pf }

/-- `iteFreshInst` for `dite`. -/
simproc diteFreshInst (@dite _ _ _ _ _) := fun e => do
  let_expr dite α c inst a b := e | return .continue
  let instTy ← instantiateMVars (← inferType inst)
  let_expr Decidable c' := instTy | return .continue
  if c' == c then return .continue
  let some inst' ← synthInstance? (mkApp (mkConst ``Decidable) c) | return .continue
  let u ← getLevel α
  let e' := mkApp5 (mkConst ``dite [u]) α c inst' a b
  let pf := mkAppN (mkConst ``dite_inst_eq [u]) #[α, c, inst, inst', a, b]
  return .done { expr := e', proof? := some pf }

end TvmLean.Exec

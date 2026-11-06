import Lean
import TvmLean.Model
import TvmLean.Semantics

/-!
# Facts several proof libraries share

Small equations about the model's definitions that more than one of `TvmLean/Proofs/{Contracts,
Exec,Tx,WF}` needs. They live here, once, so that every proof module can be imported together with
every other (a declaration may be made only once). No attributes: each library adds the ones it
works with (`attribute [simp] ...`, `attribute [vm_run] ...`) where it imports this module. Last,
the access to the private definitions of the instruction files (`private%`, `private_eq%`,
`unfold_private`).
-/

namespace TvmLean

theorem natToBits_size (n k : Nat) : (natToBits n k).size = k := by
  simp [natToBits]

theorem bitsToNat_push (bs : BitString) (b : Bool) :
    bitsToNat (bs.push b) = 2 * bitsToNat bs + (if b then 1 else 0) := by
  simp [bitsToNat, Nat.shiftLeft_eq, Nat.mul_comm]

/-- The bits of `n` on `k + 1` digits: those of `n / 2` on `k`, then the lowest bit. -/
theorem natToBits_succ (n k : Nat) :
    natToBits n (k + 1) = (natToBits (n / 2) k).push (n.testBit 0) := by
  apply Array.ext
  · simp [natToBits_size]
  · intro i h1 _
    simp only [natToBits, Array.getElem_ofFn, Array.getElem_push, Array.size_ofFn]
    split
    · simp only [Nat.testBit_div_two]
      congr 1
      omega
    · have : i = k := by simp [natToBits_size] at h1; omega
      subst this
      simp

theorem bit_eq_mod_two (n : Nat) : (if n.testBit 0 = true then 1 else 0) = n % 2 := by
  rw [Nat.testBit_zero]; split <;> simp_all <;> omega

/-- `bitsToNat` reads back `natToBits` modulo `2 ^ k`. -/
theorem bitsToNat_natToBits (n k : Nat) : bitsToNat (natToBits n k) = n % 2 ^ k := by
  induction k generalizing n with
  | zero => simp [natToBits, bitsToNat, Nat.mod_one]
  | succ k ih =>
    rw [natToBits_succ, bitsToNat_push, ih, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mod_mul,
      bit_eq_mod_two]
    omega

theorem bitsToNat_natToBits_of_lt {n k : Nat} (h : n < 2 ^ k) : bitsToNat (natToBits n k) = n := by
  rw [bitsToNat_natToBits, Nat.mod_eq_of_lt h]

theorem StepResult.state_continue (st : VmState) : (StepResult.continue st).state = st := rfl
theorem StepResult.state_halt (n : Int) (st : VmState) : (StepResult.halt n st).state = st := rfl

theorem OrdCregs.empty_c0 : OrdCregs.empty.c0 = none := rfl
theorem OrdCregs.empty_c1 : OrdCregs.empty.c1 = none := rfl
theorem OrdCregs.empty_c2 : OrdCregs.empty.c2 = none := rfl
theorem OrdCregs.empty_c3 : OrdCregs.empty.c3 = none := rfl
theorem OrdCregs.empty_c4 : OrdCregs.empty.c4 = none := rfl
theorem OrdCregs.empty_c5 : OrdCregs.empty.c5 = none := rfl
theorem OrdCregs.empty_c7 : OrdCregs.empty.c7 = none := rfl
theorem OrdCdata.empty_stack : OrdCdata.empty.stack = #[] := rfl

/-! ## The private definitions of the instruction files

A helper of an instruction file (`private def`) cannot be named from another module; the proofs of
several libraries reach it by these (the `WF` proofs, the framed steps of `Exec`). -/

open Lean Elab Tactic Meta in
/-- `unfold_private M f` unfolds in the goal the private definition `f` of the module `M` (a helper
of an instruction file, `private def`, which cannot be named from another module), so that `mvcgen`
sees its code. -/
elab "unfold_private " m:ident n:ident : tactic => do
  let full := Name.mkNum (`_private ++ m.getId) 0 ++ n.getId
  unless (← getEnv).contains full do
    throwError "unfold_private: no private definition {n.getId} in {m.getId}"
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let t' ← deltaExpand t (· == full)
    replaceMainGoal [← g.replaceTargetDefEq t'.headBeta]

open Lean Elab Term in
/-- `private% M f`: the private definition `f` of the module `M`, as a term (to state its
specification). -/
elab "private% " m:ident n:ident : term => do
  let full := Name.mkNum (`_private ++ m.getId) 0 ++ n.getId
  let some ci := (← getEnv).find? full
    | throwError "private%: no private definition {n.getId} in {m.getId}"
  return mkConst full (ci.levelParams.map fun _ => levelZero)

open Lean Elab Term Meta in
/-- `private_eq% M f`: the unfolding equation of the private definition `f` of the module `M`, also
of a recursive one (whose body `unfold_private` cannot show: it would unfold its fixpoint). -/
elab "private_eq% " m:ident n:ident : term => do
  let full := Name.mkNum (`_private ++ m.getId) 0 ++ n.getId
  unless (← getEnv).contains full do
    throwError "private_eq%: no private definition {n.getId} in {m.getId}"
  let some eqn ← getUnfoldEqnFor? full (nonRec := true)
    | throwError "private_eq%: no unfolding equation for {n.getId}"
  let ci ← getConstInfo eqn
  return mkConst eqn (ci.levelParams.map fun _ => levelZero)

end TvmLean

import TvmLean.Proofs.Check.Framed

/-!
# Checking an invariant over all transactions: a stack the step leaves as a fold

`REVERSE x,y` (`Spec.reverse`, TvmLean/Proofs/Exec/Spec/StackExt.lean) leaves the stack as
`List.foldl` of `Array.set!` over `List.range' 0 (x / 2)`: the next instruction's specification,
which needs the stack written out as `Array.push`es, does not apply, and the run stops there (the
`XCHG3` after `REVERSE` in the NFT item of the corpus). `check_stack_unfold`, one more step of
`check_extra_step` (TvmLean/Proofs/Check/Framed.lean), writes such a stack out: the range unfolded,
the fold unrolled, each `set!` and `[i]!` of a stack of known size pushed through its `push`es.
-/

namespace TvmLean.Check

theorem getElem!_push' {α : Type} [Inhabited α] (xs : Array α) (x : α) (i : Nat) :
    (xs.push x)[i]! = if i = xs.size then x else xs[i]! := by
  by_cases h : i = xs.size
  · subst h; simp
  · rw [if_neg h]
    by_cases hl : i < xs.size
    · rw [getElem!_pos (xs.push x) i (by simp; omega), getElem!_pos xs i hl, Array.getElem_push_lt hl]
    · rw [getElem!_neg (xs.push x) i (by simp; omega), getElem!_neg xs i hl]

theorem setIfInBounds_push' {α : Type} (xs : Array α) (x v : α) (i : Nat) :
    (xs.push x).setIfInBounds i v = if i = xs.size then xs.push v else (xs.setIfInBounds i v).push x := by
  unfold Array.setIfInBounds
  by_cases h : i = xs.size
  · subst h
    rw [if_pos rfl, dif_pos (by simp), Array.set_push, dif_neg (Nat.lt_irrefl _)]
  · rw [if_neg h]
    by_cases hl : i < xs.size
    · rw [dif_pos (by simp; omega), dif_pos hl, Array.set_push, dif_pos hl]
    · rw [dif_neg (by simp; omega), dif_neg hl]

theorem empty_setIfInBounds {α : Type} (i : Nat) (v : α) : (#[] : Array α).setIfInBounds i v = #[] := by
  simp

/-- Writing back at `i` what an array holds at `i` leaves it as it is, `i` in bounds or not (the
`XCHG s0,s0` of a stack; a step of every run: `check_run_simp`). -/
@[check_run_simp] theorem setIfInBounds_getElem!_self {α : Type} [Inhabited α] (a : Array α) (i : Nat) :
    a.setIfInBounds i a[i]! = a := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, Array.setIfInBounds_def, dif_pos h, Array.set_getElem_self]
  · exact Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h)

@[check_run_simp] theorem set!_getElem!_self {α : Type} [Inhabited α] (a : Array α) (i : Nat) :
    a.set! i a[i]! = a := by
  rw [Array.set!_eq_setIfInBounds, setIfInBounds_getElem!_self]

theorem range'_zero (s : Nat) : List.range' s 0 = [] := rfl
theorem range'_one (s : Nat) : List.range' s 1 = [s] := rfl
theorem range'_two (s : Nat) : List.range' s 2 = [s, s + 1] := rfl
theorem range'_three (s : Nat) : List.range' s 3 = [s, s + 1, s + 2] := rfl
theorem range'_four (s : Nat) : List.range' s 4 = [s, s + 1, s + 2, s + 3] := rfl
theorem range'_five (s : Nat) : List.range' s 5 = [s, s + 1, s + 2, s + 3, s + 4] := rfl
theorem range'_six (s : Nat) : List.range' s 6 = [s, s + 1, s + 2, s + 3, s + 4, s + 5] := rfl
theorem range'_seven (s : Nat) : List.range' s 7 = [s, s + 1, s + 2, s + 3, s + 4, s + 5, s + 6] := rfl
theorem range'_eight (s : Nat) : List.range' s 8 = [s, s + 1, s + 2, s + 3, s + 4, s + 5, s + 6, s + 7] := rfl

open Lean Meta Elab Tactic in
/-- `check_stack_unfold`: a run whose stack is a `List.foldl` (the stack `REVERSE` leaves): the
fold over a range of at most 8 unrolled, `set!` and `[i]!` pushed through the `push`es of a stack of
known size (`getElem!_push'`, `setIfInBounds_push'`, the conditions on literals decided). Fails if
there is no fold or nothing changes. -/
elab "check_stack_unfold" : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  -- only the stack of the state the run is about to step from is looked at (cheap: every step tries it)
  -- `Keeps P r` or `KeepsActs P A r`: the run is the last argument
  unless t.isAppOfArity ``Keeps 2 || t.isAppOfArity ``KeepsActs 3 do throwError "check_stack_unfold: not a run"
  let r := t.appArg!
  unless r.isAppOfArity ``VmState.runWith 3 do throwError "check_stack_unfold: not a run"
  let S := r.getArg! 2
  unless S.isAppOfArity ``VmState.mk 20 && (S.getArg! 0).isAppOf ``List.foldl do
    throwError "check_stack_unfold: no fold"
  evalTactic (← `(tactic| simp only [range'_zero, range'_one, range'_two, range'_three, range'_four,
    range'_five, range'_six, range'_seven, range'_eight, List.foldl_cons, List.foldl_nil,
    set!_getElem!_self, setIfInBounds_getElem!_self,
    Array.set!_eq_setIfInBounds, getElem!_push', setIfInBounds_push', empty_setIfInBounds, Array.size_push,
    List.size_toArray, List.length_nil, Nat.zero_add, Nat.add_zero, Nat.reduceDiv, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceEqDiff, reduceIte]))

end TvmLean.Check

namespace TvmLean

macro_rules
  | `(tactic| check_extra_step [$_args,*]) => `(tactic| check_stack_unfold)

end TvmLean

import TvmLean.Proofs.Exec.Eval

/-!
# A loop of the model as the fold of its body

A handler that loops over a range (`for i in [0:n] do ...`, a `forIn` with mutable variables `σ`)
whose body may raise an exception runs as the fold of the body's run over the list of the range
(`VM.foldRun`): the variables passed from one turn to the next, the first exception ending it with
the state it raised in. `VM.run_forIn_fold` states it for a body given by its run `f`; a
specification then writes the loop as `VM.foldRun f (List.range' 0 n) init st`, a term that `simp`
computes when `n` is a numeral (`VM.foldRun_nil`, `VM.foldRun_cons`, `List.range'_succ`).
-/

namespace TvmLean

/-- The run of a loop whose body runs as `f i x` (`i` the index, `x` the variables): the variables
after the last turn, or the first exception with the state it raised in. -/
def VM.foldRun {σ : Type} (f : Nat → σ → VmState → Except Excno σ × VmState) :
    List Nat → σ → VmState → Except Excno σ × VmState
  | [], x, st => (.ok x, st)
  | i :: l, x, st =>
    match f i x st with
    | (.ok y, st') => VM.foldRun f l y st'
    | (.error e, st') => (.error e, st')

@[vm_run] theorem VM.foldRun_nil {σ : Type} (f : Nat → σ → VmState → Except Excno σ × VmState) (x : σ)
    (st : VmState) : VM.foldRun f [] x st = (.ok x, st) := rfl

@[vm_run] theorem VM.foldRun_cons {σ : Type} (f : Nat → σ → VmState → Except Excno σ × VmState) (i : Nat)
    (l : List Nat) (x : σ) (st : VmState) :
    VM.foldRun f (i :: l) x st =
      match f i x st with
      | (.ok y, st') => VM.foldRun f l y st'
      | (.error e, st') => (.error e, st') := rfl

/-- **A loop as the fold of its body.** A `forIn` over `l` whose body, on the index `i` and the
variables `x`, runs as `f i x` and goes on (`ForInStep.yield`) when it does not raise. -/
theorem VM.run_forIn_fold {σ : Type} (l : List Nat) (init : σ) (b : Nat → σ → VM (ForInStep σ))
    (f : Nat → σ → VmState → Except Excno σ × VmState)
    (hb : ∀ i ∈ l, ∀ (x : σ) (st : VmState),
      ExceptT.run (b i x) st = VM.bindRes (f i x st) (fun y => pure (ForInStep.yield y)))
    (st : VmState) :
    ExceptT.run (forIn l init b) st = VM.foldRun f l init st := by
  induction l generalizing init st with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons, VM.run_bind, hb i (List.mem_cons_self ..), VM.foldRun_cons]
    generalize f i init st = r
    rcases r with ⟨_ | y, st'⟩
    · rfl
    · exact ih y (fun j hj => hb j (List.mem_cons_of_mem _ hj)) st'

/-- **A loop that only reads the state**, as `List.foldlM` of its body's result: a `forIn` over `l`
whose body, on the index `i` and the variables `x`, leaves the state `st` as it is and goes on with
the result of `g i x` (the exception of `g i x` raised in `st`). -/
theorem VM.run_forIn_except {σ : Type} (l : List Nat) (init : σ) (b : Nat → σ → VM (ForInStep σ))
    (g : Nat → σ → Except Excno σ) (st : VmState)
    (hb : ∀ i ∈ l, ∀ (x : σ), ExceptT.run (b i x) st =
      match g i x with
      | .ok y => ((.ok (.yield y), st) : Except Excno (ForInStep σ) × VmState)
      | .error e => (.error e, st)) :
    ExceptT.run (forIn l init b) st =
      match l.foldlM (fun x i => g i x) init with
      | .ok y => ((.ok y, st) : Except Excno σ × VmState)
      | .error e => (.error e, st) := by
  induction l generalizing init with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons, VM.run_bind, hb i (List.mem_cons_self ..), List.foldlM_cons]
    generalize g i init = r
    rcases r with e | y
    · rfl
    · exact ih y (fun j hj => hb j (List.mem_cons_of_mem _ hj))

/-- The loop of a handler over the indices `i .. i + n - 1` whose body runs as `f i x`: `VM.foldRun`
by recursion on the count (`VM.foldRun_range'`), which `simp` unfolds for a numeral count (its
equations are of `vm_run`). -/
@[vm_run] def VM.loopRun {σ : Type} (f : Nat → σ → VmState → Except Excno σ × VmState) :
    Nat → Nat → σ → VmState → Except Excno σ × VmState
  | 0, _, x, st => (.ok x, st)
  | n + 1, i, x, st =>
    match f i x st with
    | (.ok y, st') => VM.loopRun f n (i + 1) y st'
    | (.error e, st') => (.error e, st')

theorem VM.foldRun_range' {σ : Type} (f : Nat → σ → VmState → Except Excno σ × VmState) :
    ∀ (n i : Nat) (x : σ) (st : VmState), VM.foldRun f (List.range' i n) x st = VM.loopRun f n i x st
  | 0, _, _, _ => rfl
  | n + 1, i, x, st => by
    rw [List.range'_succ]
    unfold VM.foldRun VM.loopRun
    generalize f i x st = r
    rcases r with ⟨_ | y, st'⟩
    · rfl
    · exact VM.foldRun_range' f n (i + 1) y st'

/-- **The loop `for i in [0:n]` of a handler** whose body, on the index `i < n` and the variables
`x`, runs as `f i x` and goes on: `VM.loopRun f n 0`. -/
theorem VM.run_forIn_range {σ : Type} (n : Nat) (init : σ) (b : Nat → σ → VM (ForInStep σ))
    (f : Nat → σ → VmState → Except Excno σ × VmState)
    (hb : ∀ i, i < n → ∀ (x : σ) (st : VmState),
      ExceptT.run (b i x) st = VM.bindRes (f i x st) (fun y => pure (ForInStep.yield y)))
    (st : VmState) :
    ExceptT.run (forIn [:n] init b) st = VM.loopRun f n 0 init st := by
  rw [Std.Range.forIn_eq_forIn_range', VM.run_forIn_fold _ _ _ f
    (fun i hi x st => hb i (by simp [List.mem_range'_1, Std.Range.size] at hi; omega) x st)]
  simp only [Std.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact VM.foldRun_range' f n 0 init st

end TvmLean

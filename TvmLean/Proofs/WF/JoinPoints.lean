import TvmLean.Proofs.WF.Calls

/-!
# Handlers with many join points

`mvcgen` inlines the join points of a handler (`__do_jp`, the code after an `if` or a `match` that
binds or changes variables) at every jump, so a handler with `n` such points in a row makes
`2ⁿ` copies of the code after them (`RUNVM` has 19 and does not finish), and `mvcgen +jp`, which
would not copy them, fails on `RUNVM` with an ill-typed proof term (Lean 4.24). The tools here prove
such a handler a join point at a time, outside in:

```
unfold handler
extract_lets -underBinder +onlyGivenNames jp       -- the first join point, by name
have hjp : ∀ x, VM.KeepsIf (H x) (jp x) VmState.WF := ?jp
· clear_value jp                                    -- the code that jumps to it, with `hjp`
  mvcgen
  all_goals (try jp_close (hjp _))                  -- each jump: the specification of `jp`
  all_goals wf_cont                                 -- `H x` at each jump, and the other conditions
intro x                                             -- the body of `jp`
apply VM.KeepsIf.of_keeps
intro hx
unfold jp
refine VM.Keeps.bind VM.Keeps.get' fun st hst => ?_ -- its steps, up to the next join point
...
```

`extract_lets -underBinder` extracts the `let`s at the head of the code only (a plain
`extract_lets` lifts the `let`s of the whole handler); `unfold jp` unfolds the join point in the
goal at once (`simp only [jp]` takes half a minute on `RUNVM`). The facts each join point needs are
its assumption `H`; the facts no longer needed are best cleared, since `grind` instantiates every
quantified hypothesis on every value it sees.

* `VM.KeepsIf H m Q`: `VM.Keeps` under a pure assumption `H` (the precondition of a join point);
  `VM.KeepsIf.of_keeps`;
* `VM.Keeps.bind`, `VM.Keeps.pure'`, `VM.Keeps.get'`, `VM.Keeps.set'`, `VM.Keeps.ofWF`: the steps;
* `VM.Keeps.forIn_list`, `VM.Keeps.forIn_range`: loops in the VM monad with an invariant of their
  state (`mvcgen`'s loop invariants are not offered on a loop alone);
* `jp_close h`: a jump to a join point closed by its specification `h`.
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

/-- `VM.Keeps` under a pure assumption: the precondition of a join point. -/
abbrev VM.KeepsIf {α : Type} (H : Prop) (m : VM α) (Q : α → Prop) : Prop :=
  ⦃fun st => ⌜st.WF ∧ H⌝⦄ m ⦃post⟨fun a st => ⌜st.WF ∧ Q a⌝, fun _ st => ⌜st.WF⌝⟩⦄

theorem VM.KeepsIf.of_keeps {α : Type} {H : Prop} {m : VM α} {Q : α → Prop}
    (h : H → m.Keeps Q) : VM.KeepsIf H m Q := by
  apply VM.triple_of_run
  intro st ⟨hs, hH⟩
  exact VM.triple_run (h hH) st hs

theorem VM.Keeps.bind {α β : Type} {x : VM α} {f : α → VM β} {Q : α → Prop} {R : β → Prop}
    (hx : x.Keeps Q) (hf : ∀ a, Q a → (f a).Keeps R) : (x >>= f).Keeps R :=
  Triple.bind _ _ hx fun a => VM.KeepsIf.of_keeps (hf a)

/-- An operation whose specification keeps states well-formed and says nothing of its result. -/
theorem VM.Keeps.ofWF {α : Type} {m : VM α}
    (h : ⦃fun st => ⌜st.WF⌝⦄ m ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄) :
    m.Keeps fun _ => True :=
  VM.spec_mono h (fun _ h => h) (fun _ _ h => ⟨h, trivial⟩) (fun _ _ h => h)

theorem VM.Keeps.pure' {α : Type} {Q : α → Prop} {a : α} (h : Q a) :
    (pure a : VM α).Keeps Q := by
  mvcgen

theorem VM.Keeps.get' : (get : VM VmState).Keeps VmState.WF := by
  mvcgen

theorem VM.Keeps.set' {s : VmState} (h : s.WF) : (set s : VM PUnit).Keeps fun _ => True := by
  mvcgen

/-- A loop over a list in the VM monad keeps states well-formed and an invariant of its state, if
every step does. -/
theorem VM.Keeps.forIn_list {α β : Type} (P : β → Prop) (l : List α) {init : β}
    {f : α → β → VM (ForInStep β)} (h0 : P init)
    (hf : ∀ a b, P b → (f a b).Keeps fun s => P s.value) : (forIn l init f).Keeps P := by
  induction l generalizing init with
  | nil => exact VM.Keeps.pure' h0
  | cons a l ih =>
    rw [List.forIn_cons]
    refine VM.Keeps.bind (hf a init h0) fun s hs => ?_
    cases s with
    | done b => exact VM.Keeps.pure' hs
    | yield b => exact ih hs

/-- A loop over a range in the VM monad, as `VM.Keeps.forIn_list`. -/
theorem VM.Keeps.forIn_range {β : Type} (P : β → Prop) (r : Std.Range) {init : β}
    {f : Nat → β → VM (ForInStep β)} (h0 : P init)
    (hf : ∀ i b, P b → (f i b).Keeps fun s => P s.value) : (forIn r init f).Keeps P := by
  rw [Std.Range.forIn_eq_forIn_range']
  exact VM.Keeps.forIn_list P _ h0 hf

/-- Closes a jump to a join point, `wp⟦jp args⟧ Q st` (or the condition `mvcgen` leaves before
it, `∀ st, st.WF → ... → wp⟦jp args⟧ Q st`), by the specification `h` of the join point applied to
the arguments (`jp_close (hjp _ _)`); leaves the assumption of the specification. -/
macro "jp_close " h:term : tactic => `(tactic|
  first
    | (intro s hs; intros; refine $h s ⟨by first | exact hs | exact hs.1 | wf_cont, ?_⟩)
    | (refine $h _ ⟨by first | assumption | wf_cont, ?_⟩))

end TvmLean

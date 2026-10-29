import TvmLean.Proofs.Check.Tactic
import TvmLean.Proofs.Tx.Upgrade

/-!
# Checking a contract whose code may change

`ran_preserves_of` (TvmLean/Proofs/Check/Tactic.lean) gives the obligation of
`Reachable.code_fixed`: the action lists are `SafeActs`, without `SETCODE`. For a contract that may
change its code, `tools/contract-check` states the runs of each kind of transaction with the action
lists described by `Acts K` (`RunsKeepActs`, `KeepsActs`), `K` the condition on a code a `SETCODE`
installs, which may read the message (its body: e.g. "signed by the owner"). `ran_keeps_of` collects
the six statements: every committed run commits data satisfying `P`, and an action list of the
predicate of its kind of transaction. With it:

* `ReachableWhile.good_codes` (TvmLean/Proofs/Tx/Upgrade.lean): any code the condition `K` admits
  may be installed; while the code is `C`, the data satisfies `P`, and the code is `C` or one that
  `K` admits for the body of some message (`Installable K`, `ran_installs_of`);
* `Reachable.code_self`: the condition is `c = C` (the code installs only itself, `Acts.setCode_of_actionIn`);
  the code is `C` and the data satisfies `P` in every reachable shard account (`ran_self_of`).
-/

namespace TvmLean.Check

open TvmLean.Tx

/-- **The six kinds of transaction together** (`ran_preserves_of` for `RunsKeepActs`, with an
action-list predicate per message or tick-tock): every committed run of `C` from data satisfying
`P` commits data satisfying `P` and an action list of the predicate of some message or tick-tock. -/
theorem ran_keeps_of {C : Cell} {P : Option Cell → Prop}
    {Aext Aint : Int → Int → Cell → Slice → Cell → Prop} {Att : Int → Int → Int → Cell → Prop}
    (hC : C.special = false)
    (hext : ∀ bal val msg body, RunsKeepActs C P (Aext bal val msg body) (computePhaseStack bal val msg body true) (4 ≤ ·))
    (hextOld : ∀ bal val msg body,
      RunsKeepActs C P (Aext bal val msg body) (computePhaseStack bal val msg body true) (· < 4))
    (hint : ∀ bal val msg body,
      RunsKeepActs C P (Aint bal val msg body) (computePhaseStack bal val msg body false) (4 ≤ ·))
    (hintOld : ∀ bal val msg body,
      RunsKeepActs C P (Aint bal val msg body) (computePhaseStack bal val msg body false) (· < 4))
    (htt : ∀ bal addr tock, RunsKeepActs C P (Att bal addr tock) (tickTockStack bal addr tock) (4 ≤ ·))
    (httOld : ∀ bal addr tock, RunsKeepActs C P (Att bal addr tock) (tickTockStack bal addr tock) (· < 4)) :
    ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧
      ((∃ bal val msg body, Aext bal val msg body c5) ∨ (∃ bal val msg body, Aint bal val msg body c5) ∨
        ∃ bal addr tock, Att bal addr tock c5) := by
  intro data c4 c5 hP hr
  obtain ⟨st, ⟨gv, libs, stack, c7, gl, gm, gc, mdd, mll, hstack, rfl⟩, hcomm, -, rfl, rfl⟩ := hr
  rw [convertCodeCell_ordinary C gv libs hC] at hcomm ⊢
  have hst : ({ computePhaseInit C (data.getD Cell.empty) stack #[c7] gl gm gc gv with
      libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll } : VmState) =
      start C (data.getD Cell.empty) stack c7 gl gm gc gv libs mdd mll #[] := rfl
  rw [hst, vmFinal_eq] at hcomm ⊢
  rcases hstack with ⟨bal, val, msg, body, ext, rfl⟩ | ⟨bal, addr, tock, rfl⟩
  · cases ext
    · have hk := fun fuel => if hgv : 4 ≤ gv then hint bal val msg body data hP c7 gl gm gc gv hgv libs mdd mll #[] fuel
        else hintOld bal val msg body data hP c7 gl gm gc gv (by omega) libs mdd mll #[] fuel
      obtain ⟨h4, h5⟩ := hk _ hcomm
      exact ⟨h4, Or.inr (Or.inl ⟨bal, val, msg, body, h5⟩)⟩
    · have hk := fun fuel => if hgv : 4 ≤ gv then hext bal val msg body data hP c7 gl gm gc gv hgv libs mdd mll #[] fuel
        else hextOld bal val msg body data hP c7 gl gm gc gv (by omega) libs mdd mll #[] fuel
      obtain ⟨h4, h5⟩ := hk _ hcomm
      exact ⟨h4, Or.inl ⟨bal, val, msg, body, h5⟩⟩
  · have hk := fun fuel => if hgv : 4 ≤ gv then htt bal addr tock data hP c7 gl gm gc gv hgv libs mdd mll #[] fuel
      else httOld bal addr tock data hP c7 gl gm gc gv (by omega) libs mdd mll #[] fuel
    obtain ⟨h4, h5⟩ := hk _ hcomm
    exact ⟨h4, Or.inr (Or.inr ⟨bal, addr, tock, h5⟩)⟩

/-- A code that a `SETCODE` of the runs may install under the condition `K` on the body of the
message (`none` for tick-tock): `K (some body) c` for some body, or `K none c`. -/
def Installable (K : Option Slice → Cell → Prop) (c : Cell) : Prop :=
  (∃ body, K (some body) c) ∨ K none c

/-- **The six kinds of transaction with a condition on the codes installed** (`ran_keeps_of` with the
action lists `Acts (K (some body))` of a message and `Acts (K none)` of tick-tock): every committed run
of `C` from data satisfying `P` commits data satisfying `P`, and every `SETCODE` of its action list
installs a code that `K` admits for the body of some message (`Installable K`,
`Acts.setCode_of_actionIn`). The obligation of `ReachableWhile.good_codes`. -/
theorem ran_installs_of {C : Cell} {P : Option Cell → Prop} {K : Option Slice → Cell → Prop}
    (hC : C.special = false)
    (hext : ∀ bal val msg body,
      RunsKeepActs C P (Acts (K (some body))) (computePhaseStack bal val msg body true) (4 ≤ ·))
    (hextOld : ∀ bal val msg body,
      RunsKeepActs C P (Acts (K (some body))) (computePhaseStack bal val msg body true) (· < 4))
    (hint : ∀ bal val msg body,
      RunsKeepActs C P (Acts (K (some body))) (computePhaseStack bal val msg body false) (4 ≤ ·))
    (hintOld : ∀ bal val msg body,
      RunsKeepActs C P (Acts (K (some body))) (computePhaseStack bal val msg body false) (· < 4))
    (htt : ∀ bal addr tock, RunsKeepActs C P (Acts (K none)) (tickTockStack bal addr tock) (4 ≤ ·))
    (httOld : ∀ bal addr tock, RunsKeepActs C P (Acts (K none)) (tickTockStack bal addr tock) (· < 4)) :
    ∀ data c4 c5, P data → Ran C data c4 c5 →
      P (some c4) ∧ ∀ c, ActionIn c5 (.setCode c) → Installable K c := by
  intro data c4 c5 hP hr
  obtain ⟨h4, h5⟩ := ran_keeps_of (Aext := fun _ _ _ body => Acts (K (some body)))
    (Aint := fun _ _ _ body => Acts (K (some body))) (Att := fun _ _ _ => Acts (K none))
    hC hext hextOld hint hintOld htt httOld data c4 c5 hP hr
  refine ⟨h4, fun c hin => ?_⟩
  rcases h5 with ⟨_, _, _, body, h⟩ | ⟨_, _, _, body, h⟩ | ⟨_, _, _, h⟩
  · exact Or.inl ⟨body, h.setCode_of_actionIn hin⟩
  · exact Or.inl ⟨body, h.setCode_of_actionIn hin⟩
  · exact Or.inr (h.setCode_of_actionIn hin)

/-- The obligation of `Reachable.code_self` from the six kinds of transaction, the action lists
`Acts (· = C)`: every `SETCODE` installs `C` itself. -/
theorem ran_self_of {C : Cell} {P : Option Cell → Prop} (hC : C.special = false)
    (hext : ∀ bal val msg body,
      RunsKeepActs C P (Acts (· = C)) (computePhaseStack bal val msg body true) (4 ≤ ·))
    (hextOld : ∀ bal val msg body,
      RunsKeepActs C P (Acts (· = C)) (computePhaseStack bal val msg body true) (· < 4))
    (hint : ∀ bal val msg body,
      RunsKeepActs C P (Acts (· = C)) (computePhaseStack bal val msg body false) (4 ≤ ·))
    (hintOld : ∀ bal val msg body,
      RunsKeepActs C P (Acts (· = C)) (computePhaseStack bal val msg body false) (· < 4))
    (htt : ∀ bal addr tock, RunsKeepActs C P (Acts (· = C)) (tickTockStack bal addr tock) (4 ≤ ·))
    (httOld : ∀ bal addr tock, RunsKeepActs C P (Acts (· = C)) (tickTockStack bal addr tock) (· < 4)) :
    ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧ ∀ c, ActionIn c5 (.setCode c) → c = C := by
  intro data c4 c5 hP hr
  obtain ⟨h4, h5⟩ := ran_keeps_of (Aext := fun _ _ _ _ => Acts (· = C)) (Aint := fun _ _ _ _ => Acts (· = C))
    (Att := fun _ _ _ => Acts (· = C)) hC hext hextOld hint hintOld htt httOld data c4 c5 hP hr
  have ha : Acts (· = C) c5 := by
    rcases h5 with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, h⟩ <;> exact h
  exact ⟨h4, fun c hin => ha.setCode_of_actionIn hin⟩

end TvmLean.Check

import TvmLean.Proofs.Check.Upgrade

/-!
# The runs of a contract from an ordinary message cell

`Ran` (TvmLean/Proofs/Tx/Effect.lean) records that the message cell of a compute phase is ordinary
(`MsgOrd`, TvmLean/Proofs/Tx/InMsg.lean: C++ reads the message with `vm::load_cell_slice`, which
refuses a special cell, and the model refuses it at the same places). The theorems here are those
of TvmLean/Proofs/Check/Tactic.lean and Upgrade.lean with the runs of a message given
`msg.special = false`: `ran_preserves_ord_of` (the obligation of `Reachable.code_fixed`),
`ran_keeps_ord_of`, `ran_installs_ord_of` (of `ReachableWhile.good_codes`), `ran_self_ord_of` (of
`Reachable.code_self`). `tools/contract-check` states the runs of a message so: the `CTOS` of the
message (`in_msg_full.begin_parse()`) runs by its lemma (`Spec.ctos` needs `c.special = false`), and
the theorem over all transactions is the same.
-/

namespace TvmLean.Check

open TvmLean.Tx

/-- **The obligation of `Reachable.code_fixed` from the runs of each kind of transaction**,
`ran_preserves_of` with the runs of a message from an ordinary message cell. -/
theorem ran_preserves_ord_of {C : Cell} {P : Option Cell → Prop} (hC : C.special = false)
    (hext : ∀ bal val msg body, msg.special = false →
      RunsKeep C P (computePhaseStack bal val msg body true) (4 ≤ ·))
    (hextOld : ∀ bal val msg body, msg.special = false →
      RunsKeep C P (computePhaseStack bal val msg body true) (· < 4))
    (hint : ∀ bal val msg body, msg.special = false →
      RunsKeep C P (computePhaseStack bal val msg body false) (4 ≤ ·))
    (hintOld : ∀ bal val msg body, msg.special = false →
      RunsKeep C P (computePhaseStack bal val msg body false) (· < 4))
    (htt : ∀ bal addr tock, RunsKeep C P (tickTockStack bal addr tock) (4 ≤ ·))
    (httOld : ∀ bal addr tock, RunsKeep C P (tickTockStack bal addr tock) (· < 4)) :
    ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧ ∀ c, ¬ActionIn c5 (.setCode c) := by
  intro data c4 c5 hP hr
  obtain ⟨st, ⟨gv, libs, stack, c7, gl, gm, gc, mdd, mll, hstack, rfl⟩, hcomm, -, rfl, rfl, hmsg⟩ := hr
  rw [convertCodeCell_ordinary C gv libs hC] at hcomm ⊢
  have hst : ({ computePhaseInit C (data.getD Cell.empty) stack #[c7] gl gm gc gv with
      libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll } : VmState) =
      start C (data.getD Cell.empty) stack c7 gl gm gc gv libs mdd mll #[] := rfl
  rw [hst, vmFinal_eq] at hcomm ⊢
  generalize hS : start C (data.getD Cell.empty) stack c7 gl gm gc gv libs mdd mll #[] = S at hcomm ⊢
  have hk : Keeps P (VmState.runWith execInstr (S.gas.stepBound + 16) S) := by
    subst hS
    rcases hstack with ⟨bal, val, msg, body, ext, rfl⟩ | ⟨bal, addr, tock, rfl⟩
    · have hm : msg.special = false := hmsg bal val msg body ext rfl
      cases ext
      · by_cases hgv : 4 ≤ gv
        · exact hint bal val msg body hm data hP c7 gl gm gc gv hgv libs mdd mll #[] _
        · exact hintOld bal val msg body hm data hP c7 gl gm gc gv (by omega) libs mdd mll #[] _
      · by_cases hgv : 4 ≤ gv
        · exact hext bal val msg body hm data hP c7 gl gm gc gv hgv libs mdd mll #[] _
        · exact hextOld bal val msg body hm data hP c7 gl gm gc gv (by omega) libs mdd mll #[] _
    · by_cases hgv : 4 ≤ gv
      · exact htt bal addr tock data hP c7 gl gm gc gv hgv libs mdd mll #[] _
      · exact httOld bal addr tock data hP c7 gl gm gc gv (by omega) libs mdd mll #[] _
  obtain ⟨h4, h5⟩ := hk hcomm
  exact ⟨h4, h5.noSetCode⟩

/-- `ran_keeps_of` (TvmLean/Proofs/Check/Upgrade.lean) with the runs of a message from an ordinary
message cell. -/
theorem ran_keeps_ord_of {C : Cell} {P : Option Cell → Prop}
    {Aext Aint : Int → Int → Cell → Slice → Cell → Prop} {Att : Int → Int → Int → Cell → Prop}
    (hC : C.special = false)
    (hext : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Aext bal val msg body) (computePhaseStack bal val msg body true) (4 ≤ ·))
    (hextOld : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Aext bal val msg body) (computePhaseStack bal val msg body true) (· < 4))
    (hint : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Aint bal val msg body) (computePhaseStack bal val msg body false) (4 ≤ ·))
    (hintOld : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Aint bal val msg body) (computePhaseStack bal val msg body false) (· < 4))
    (htt : ∀ bal addr tock, RunsKeepActs C P (Att bal addr tock) (tickTockStack bal addr tock) (4 ≤ ·))
    (httOld : ∀ bal addr tock, RunsKeepActs C P (Att bal addr tock) (tickTockStack bal addr tock) (· < 4)) :
    ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧
      ((∃ bal val msg body, Aext bal val msg body c5) ∨ (∃ bal val msg body, Aint bal val msg body c5) ∨
        ∃ bal addr tock, Att bal addr tock c5) := by
  intro data c4 c5 hP hr
  obtain ⟨st, ⟨gv, libs, stack, c7, gl, gm, gc, mdd, mll, hstack, rfl⟩, hcomm, -, rfl, rfl, hmsg⟩ := hr
  rw [convertCodeCell_ordinary C gv libs hC] at hcomm ⊢
  have hst : ({ computePhaseInit C (data.getD Cell.empty) stack #[c7] gl gm gc gv with
      libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll } : VmState) =
      start C (data.getD Cell.empty) stack c7 gl gm gc gv libs mdd mll #[] := rfl
  rw [hst, vmFinal_eq] at hcomm ⊢
  rcases hstack with ⟨bal, val, msg, body, ext, rfl⟩ | ⟨bal, addr, tock, rfl⟩
  · have hm : msg.special = false := hmsg bal val msg body ext rfl
    cases ext
    · have hk := fun fuel => if hgv : 4 ≤ gv then hint bal val msg body hm data hP c7 gl gm gc gv hgv libs mdd mll #[] fuel
        else hintOld bal val msg body hm data hP c7 gl gm gc gv (by omega) libs mdd mll #[] fuel
      obtain ⟨h4, h5⟩ := hk _ hcomm
      exact ⟨h4, Or.inr (Or.inl ⟨bal, val, msg, body, h5⟩)⟩
    · have hk := fun fuel => if hgv : 4 ≤ gv then hext bal val msg body hm data hP c7 gl gm gc gv hgv libs mdd mll #[] fuel
        else hextOld bal val msg body hm data hP c7 gl gm gc gv (by omega) libs mdd mll #[] fuel
      obtain ⟨h4, h5⟩ := hk _ hcomm
      exact ⟨h4, Or.inl ⟨bal, val, msg, body, h5⟩⟩
  · have hk := fun fuel => if hgv : 4 ≤ gv then htt bal addr tock data hP c7 gl gm gc gv hgv libs mdd mll #[] fuel
      else httOld bal addr tock data hP c7 gl gm gc gv (by omega) libs mdd mll #[] fuel
    obtain ⟨h4, h5⟩ := hk _ hcomm
    exact ⟨h4, Or.inr (Or.inr ⟨bal, addr, tock, h5⟩)⟩

/-- `ran_installs_of` with the runs of a message from an ordinary message cell: the obligation of
`ReachableWhile.good_codes`. -/
theorem ran_installs_ord_of {C : Cell} {P : Option Cell → Prop} {K : Option Slice → Cell → Prop}
    (hC : C.special = false)
    (hext : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Acts (K (some body))) (computePhaseStack bal val msg body true) (4 ≤ ·))
    (hextOld : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Acts (K (some body))) (computePhaseStack bal val msg body true) (· < 4))
    (hint : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Acts (K (some body))) (computePhaseStack bal val msg body false) (4 ≤ ·))
    (hintOld : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Acts (K (some body))) (computePhaseStack bal val msg body false) (· < 4))
    (htt : ∀ bal addr tock, RunsKeepActs C P (Acts (K none)) (tickTockStack bal addr tock) (4 ≤ ·))
    (httOld : ∀ bal addr tock, RunsKeepActs C P (Acts (K none)) (tickTockStack bal addr tock) (· < 4)) :
    ∀ data c4 c5, P data → Ran C data c4 c5 →
      P (some c4) ∧ ∀ c, ActionIn c5 (.setCode c) → Installable K c := by
  intro data c4 c5 hP hr
  obtain ⟨h4, h5⟩ := ran_keeps_ord_of (Aext := fun _ _ _ body => Acts (K (some body)))
    (Aint := fun _ _ _ body => Acts (K (some body))) (Att := fun _ _ _ => Acts (K none))
    hC hext hextOld hint hintOld htt httOld data c4 c5 hP hr
  refine ⟨h4, fun c hin => ?_⟩
  rcases h5 with ⟨_, _, _, body, h⟩ | ⟨_, _, _, body, h⟩ | ⟨_, _, _, h⟩
  · exact Or.inl ⟨body, h.setCode_of_actionIn hin⟩
  · exact Or.inl ⟨body, h.setCode_of_actionIn hin⟩
  · exact Or.inr (h.setCode_of_actionIn hin)

/-- `ran_self_of` with the runs of a message from an ordinary message cell: the obligation of
`Reachable.code_self`. -/
theorem ran_self_ord_of {C : Cell} {P : Option Cell → Prop} (hC : C.special = false)
    (hext : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Acts (· = C)) (computePhaseStack bal val msg body true) (4 ≤ ·))
    (hextOld : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Acts (· = C)) (computePhaseStack bal val msg body true) (· < 4))
    (hint : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Acts (· = C)) (computePhaseStack bal val msg body false) (4 ≤ ·))
    (hintOld : ∀ bal val msg body, msg.special = false →
      RunsKeepActs C P (Acts (· = C)) (computePhaseStack bal val msg body false) (· < 4))
    (htt : ∀ bal addr tock, RunsKeepActs C P (Acts (· = C)) (tickTockStack bal addr tock) (4 ≤ ·))
    (httOld : ∀ bal addr tock, RunsKeepActs C P (Acts (· = C)) (tickTockStack bal addr tock) (· < 4)) :
    ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧ ∀ c, ActionIn c5 (.setCode c) → c = C := by
  intro data c4 c5 hP hr
  obtain ⟨h4, h5⟩ := ran_keeps_ord_of (Aext := fun _ _ _ _ => Acts (· = C)) (Aint := fun _ _ _ _ => Acts (· = C))
    (Att := fun _ _ _ => Acts (· = C)) hC hext hextOld hint hintOld htt httOld data c4 c5 hP hr
  have ha : Acts (· = C) c5 := by
    rcases h5 with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, h⟩ <;> exact h
  exact ⟨h4, fun c hin => ha.setCode_of_actionIn hin⟩

end TvmLean.Check

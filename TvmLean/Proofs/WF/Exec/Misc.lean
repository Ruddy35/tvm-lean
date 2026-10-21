import TvmLean.Proofs.WF.Cells

/-!
# The Misc family keeps states well-formed

`execInstrMisc_WF : FamilyWF execInstrMisc`: `CDATASIZE(Q)` and `SDATASIZE(Q)` count the distinct
cells below a cell or slice and push integers. The count (`VM.visitDataSizeCell`, recursive on the
cell) only charges gas for the cells it loads, so it keeps the state well-formed
(`VM.visitDataSizeCell_spec`, by recursion on the cell as the function itself; the hashes it
compares stay variables).

`SDATASIZE` loops over the references with a `try ... catch` and a `break` in the body: `mvcgen`
on the whole handler leaves the match on the result of the body (`DoResultSBC`) unsolved and builds
a term the kernel rejects. So its steps are bound by hand (`Triple.bind`), the code after the
bound is checked is a join point with a specification of its own, the loop is
`VM.forIn_range_WF` (a loop whose every step keeps the state well-formed), and the result of the
body is taken apart by `rcases` before `mvcgen` sees the match.
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

theorem WF.mem_of_toList_eq {α : Type} {a : Array α} {l₁ l₂ : List α} {x : α}
    (h : a.toList = l₁ ++ x :: l₂) : x ∈ a := by
  rw [Array.mem_def, h]; simp

/-- C++ `VmStorageStat::add_storage`: the count of the cells below a cell keeps the state
well-formed. -/
theorem VM.visitDataSizeCell_spec (limit : Nat) (c : Cell) (acc : DataSizeAcc) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.visitDataSizeCell limit c acc
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  have ih : ∀ r ∈ c.refs, ∀ acc, ⦃fun st => ⌜st.WF⌝⦄ VM.visitDataSizeCell limit r acc
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ :=
    fun r hr acc => VM.visitDataSizeCell_spec limit r acc
  rw [VM.visitDataSizeCell]
  generalize ByteArray.mk (Cell.hashBytes c) = h
  mvcgen [ih] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc [WF.mem_of_toList_eq]
termination_by sizeOf c
decreasing_by
  all_goals
    have h1 := Array.sizeOf_lt_of_mem hr
    cases c
    simp_all
    omega

/-- `CDATASIZE(Q)` keeps the state well-formed. -/
theorem VM.execCdataSize_WF (quiet : Bool) : (VM.execCdataSize quiet).KeepsWF := by
  mvcgen [VM.execCdataSize, VM.visitDataSizeCell_spec]
  all_goals wf_vc

/-- A loop over a range in the VM monad whose every step keeps the state well-formed. -/
theorem VM.forIn_range_WF {β : Type} {xs : Std.Range} {init : β} {f : Nat → β → VM (ForInStep β)}
    (hf : ∀ i b, ⦃fun st => ⌜st.WF⌝⦄ f i b ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄) :
    ⦃fun st => ⌜st.WF⌝⦄ forIn xs init f ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  refine Spec.forIn_range (m := VM) (post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩) ?_
  intro pref cur suff h b
  apply SPred.entails.trans (hf cur b)
  apply (wp (f cur b)).mono _ _
  refine ⟨fun r => ?_, ExceptConds.entails.refl _⟩
  cases r <;> exact SPred.entails.refl _

/-- `SDATASIZE(Q)` keeps the state well-formed (its steps bound by hand, see the module
docstring). -/
theorem VM.execSdataSize_spec (quiet : Bool) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.execSdataSize quiet ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold VM.execSdataSize
  refine Triple.bind _ _ (VM.checkUnderflow_spec 2) fun _ => ?_
  refine Triple.bind _ _ VM.popInt_spec fun bound => ?_
  refine Triple.bind _ _ (VM.spec_mono VM.popSlice_spec (fun _ h => h) (fun _ _ h => h.1)
    (fun _ _ h => h)) fun s => ?_
  extract_lets maxBoundNat maxBound src acc0 ok0 okF jp
  have hjp : ∀ n, ⦃fun st => ⌜st.WF⌝⦄ jp n ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
    intro n
    simp only [jp]
    refine Triple.bind _ _ (VM.forIn_range_WF fun i b => ?_) fun r => ?_
    · refine Triple.bind (m := VM) (ps := .except Excno (.arg VmState .pure))
        (Q := fun _ st => ⌜st.WF⌝) _ _ ?_ fun r => ?_
      · mvcgen [VM.visitDataSizeCell_spec]
        all_goals wf_vc
      · rcases r with ⟨_, ⟨_, _⟩⟩ | ⟨⟨_, _⟩⟩ | ⟨⟨_, _⟩⟩ <;> mvcgen
    · obtain ⟨acc, ok⟩ := r
      mvcgen
      all_goals wf_vc
  clear_value jp
  mvcgen
  all_goals try wf_vc
  all_goals exact hjp _ _ ‹_›

theorem execInstrMisc_WF : FamilyWF execInstrMisc := by
  intro i next hi hnext
  unfold execInstrMisc
  split
  · exact VM.execCdataSize_WF _
  · exact VM.spec_mono (VM.execSdataSize_spec _) (fun _ h => h) (fun _ _ h => ⟨h, trivial⟩)
      (fun _ _ h => h)
  · exact hnext

end TvmLean

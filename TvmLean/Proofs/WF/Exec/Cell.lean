import TvmLean.Proofs.WF.Cells

/-!
# The Cell family keeps states well-formed

`execInstrCell_WF`: every handler of `execInstrCell` (`TvmLean/Semantics/Exec/Cell/`) keeps
`VmState.WF`, so the family does. Most handlers are `mvcgen` and `wf_cells` (`Cells.lean`); the
others:
* `STI`, `STU` and their variants (`execInstrCellStIntFixed`, `execInstrCellStIntVar`): the code
  after the integer and the builder are taken is a join point on the pair, which `mvcgen` does not
  take apart; it gets a specification of its own (`hjp`);
* `HASHBU` (`execInstrCellExt`): the hash and the integer pushed are generalized and the steps bound
  by hand, so that neither `mvcgen` nor the kernel computes the hash;
* `XLOAD` (`execInstrCellExt`): the join point on the resolved cell (an `Except`) gets a
  specification of its own.
-/

open Std.Do

set_option mvcgen.warning false

-- the store of a variable-length integer (`execInstrCellExt`) needs more than the default
set_option maxHeartbeats 4000000

namespace TvmLean

theorem execInstrCellCtos_WF : FamilyWF execInstrCellCtos := by
  intro i next hi hnext
  mvcgen [execInstrCellCtos, hnext]
  all_goals wf_cells

theorem execInstrCellXctos_WF : FamilyWF execInstrCellXctos := by
  intro i next hi hnext
  mvcgen [execInstrCellXctos, hnext]
  all_goals wf_cells

theorem execInstrCellNewc_WF : FamilyWF execInstrCellNewc := by
  intro i next hi hnext
  mvcgen [execInstrCellNewc, hnext]
  all_goals wf_cells

theorem execInstrCellEndc_WF : FamilyWF execInstrCellEndc := by
  intro i next hi hnext
  mvcgen [execInstrCellEndc, hnext]
  all_goals wf_cells

theorem execInstrCellEnds_WF : FamilyWF execInstrCellEnds := by
  intro i next hi hnext
  mvcgen [execInstrCellEnds, hnext]
  all_goals wf_cells

theorem execInstrCellSbits_WF : FamilyWF execInstrCellSbits := by
  intro i next hi hnext
  mvcgen [execInstrCellSbits, hnext]
  all_goals wf_cells

theorem execInstrCellSrefs_WF : FamilyWF execInstrCellSrefs := by
  intro i next hi hnext
  mvcgen [execInstrCellSrefs, hnext]
  all_goals wf_cells

theorem execInstrCellSbitrefs_WF : FamilyWF execInstrCellSbitrefs := by
  intro i next hi hnext
  mvcgen [execInstrCellSbitrefs, hnext]
  all_goals wf_cells

theorem execInstrCellCdepth_WF : FamilyWF execInstrCellCdepth := by
  intro i next hi hnext
  mvcgen [execInstrCellCdepth, hnext]
  all_goals wf_cells

theorem execInstrCellSempty_WF : FamilyWF execInstrCellSempty := by
  intro i next hi hnext
  mvcgen [execInstrCellSempty, hnext]
  all_goals wf_cells

theorem execInstrCellSdempty_WF : FamilyWF execInstrCellSdempty := by
  intro i next hi hnext
  mvcgen [execInstrCellSdempty, hnext]
  all_goals wf_cells

theorem execInstrCellSrempty_WF : FamilyWF execInstrCellSrempty := by
  intro i next hi hnext
  mvcgen [execInstrCellSrempty, hnext]
  all_goals wf_cells

theorem execInstrCellSdCntLead0_WF : FamilyWF execInstrCellSdCntLead0 := by
  intro i next hi hnext
  mvcgen [execInstrCellSdCntLead0, hnext]
  all_goals wf_cells

theorem execInstrCellSdCntTrail0_WF : FamilyWF execInstrCellSdCntTrail0 := by
  intro i next hi hnext
  mvcgen [execInstrCellSdCntTrail0, hnext]
  all_goals wf_cells

theorem execInstrCellSdEq_WF : FamilyWF execInstrCellSdEq := by
  intro i next hi hnext
  mvcgen [execInstrCellSdEq, hnext]
  all_goals wf_cells

theorem execInstrCellSdPpfx_WF : FamilyWF execInstrCellSdPpfx := by
  intro i next hi hnext
  mvcgen [execInstrCellSdPpfx, hnext]
  all_goals wf_cells

theorem execInstrCellSdPpfxRev_WF : FamilyWF execInstrCellSdPpfxRev := by
  intro i next hi hnext
  mvcgen [execInstrCellSdPpfxRev, hnext]
  all_goals wf_cells

theorem execInstrCellSdPfx_WF : FamilyWF execInstrCellSdPfx := by
  intro i next hi hnext
  mvcgen [execInstrCellSdPfx, hnext]
  all_goals wf_cells

theorem execInstrCellSdPfxRev_WF : FamilyWF execInstrCellSdPfxRev := by
  intro i next hi hnext
  mvcgen [execInstrCellSdPfxRev, hnext]
  all_goals wf_cells

theorem execInstrCellSdLexCmp_WF : FamilyWF execInstrCellSdLexCmp := by
  intro i next hi hnext
  mvcgen [execInstrCellSdLexCmp, hnext]
  all_goals wf_cells

theorem execInstrCellSdcutfirst_WF : FamilyWF execInstrCellSdcutfirst := by
  intro i next hi hnext
  mvcgen [execInstrCellSdcutfirst, hnext]
  all_goals wf_cells

theorem execInstrCellSdskipfirst_WF : FamilyWF execInstrCellSdskipfirst := by
  intro i next hi hnext
  mvcgen [execInstrCellSdskipfirst, hnext]
  all_goals wf_cells

theorem execInstrCellSdcutlast_WF : FamilyWF execInstrCellSdcutlast := by
  intro i next hi hnext
  mvcgen [execInstrCellSdcutlast, hnext]
  all_goals wf_cells

theorem execInstrCellSdskiplast_WF : FamilyWF execInstrCellSdskiplast := by
  intro i next hi hnext
  mvcgen [execInstrCellSdskiplast, hnext]
  all_goals wf_cells

theorem execInstrCellSdBeginsX_WF : FamilyWF execInstrCellSdBeginsX := by
  intro i next hi hnext
  mvcgen [execInstrCellSdBeginsX, hnext]
  all_goals wf_cells

theorem execInstrCellSdBeginsConst_WF : FamilyWF execInstrCellSdBeginsConst := by
  intro i next hi hnext
  mvcgen [execInstrCellSdBeginsConst, hnext]
  all_goals wf_cells

theorem execInstrCellLdu_WF : FamilyWF execInstrCellLdu := by
  intro i next hi hnext
  mvcgen [execInstrCellLdu, hnext]
  all_goals wf_cells

theorem execInstrCellLoadInt_WF : FamilyWF execInstrCellLoadInt := by
  intro i next hi hnext
  mvcgen [execInstrCellLoadInt, hnext]
  all_goals wf_cells

theorem execInstrCellLoadIntVar_WF : FamilyWF execInstrCellLoadIntVar := by
  intro i next hi hnext
  mvcgen [execInstrCellLoadIntVar, hnext]
  all_goals wf_cells

theorem execInstrCellLdref_WF : FamilyWF execInstrCellLdref := by
  intro i next hi hnext
  mvcgen [execInstrCellLdref, hnext]
  all_goals wf_cells

theorem execInstrCellLdrefRtos_WF : FamilyWF execInstrCellLdrefRtos := by
  intro i next hi hnext
  mvcgen [execInstrCellLdrefRtos, hnext]
  all_goals wf_cells

theorem execInstrCellPldRefIdx_WF : FamilyWF execInstrCellPldRefIdx := by
  intro i next hi hnext
  mvcgen [execInstrCellPldRefIdx, hnext]
  all_goals wf_cells

theorem execInstrCellLoadSliceX_WF : FamilyWF execInstrCellLoadSliceX := by
  intro i next hi hnext
  mvcgen [execInstrCellLoadSliceX, hnext]
  all_goals wf_cells

theorem execInstrCellLoadSliceFixed_WF : FamilyWF execInstrCellLoadSliceFixed := by
  intro i next hi hnext
  mvcgen [execInstrCellLoadSliceFixed, hnext]
  all_goals wf_cells

theorem execInstrCellSti_WF : FamilyWF execInstrCellSti := by
  intro i next hi hnext
  mvcgen [execInstrCellSti, hnext]
  all_goals wf_cells

theorem execInstrCellStu_WF : FamilyWF execInstrCellStu := by
  intro i next hi hnext
  mvcgen [execInstrCellStu, hnext]
  all_goals wf_cells

theorem execInstrCellStIntVar_WF : FamilyWF execInstrCellStIntVar := by
  intro i next hi hnext
  unfold execInstrCellStIntVar
  split
  · -- `mvcgen` does not take the join points on a pair apart: they get a spec of their own
    refine Triple.bind _ _ (VM.checkUnderflow_spec 3) fun _ => ?_
    extract_lets maxBits jp2 jp1
    refine Triple.bind _ _ (VM.popNatUpTo_spec maxBits) fun bits => ?_
    extract_lets jp
    have hjp : ∀ p : IntVal × Builder,
        ⦃fun st => ⌜st.WF ∧ p.2.WF⌝⦄ jp p ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
      intro ⟨x, b⟩
      cases x <;> simp only [jp, jp1, jp2] <;> mvcgen <;> wf_cells
    clear_value jp jp1 jp2
    mvcgen
    all_goals try wf_cells
    all_goals (refine hjp _ _ ?_; simp only [SPred.down_pure]; wf_cells)
  · exact hnext

theorem execInstrCellStIntFixed_WF : FamilyWF execInstrCellStIntFixed := by
  intro i next hi hnext
  unfold execInstrCellStIntFixed
  split
  · -- as for `execInstrCellStIntVar`
    extract_lets jp2 jp1 jp
    have hjp : ∀ p : IntVal × Builder,
        ⦃fun st => ⌜st.WF ∧ p.2.WF⌝⦄ jp p ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
      intro ⟨x, b⟩
      cases x <;> simp only [jp, jp1, jp2] <;> mvcgen <;> wf_cells
    clear_value jp jp1 jp2
    mvcgen
    all_goals try wf_cells
    all_goals (refine hjp _ _ ?_; simp only [SPred.down_pure]; wf_cells)
  · exact hnext

theorem execInstrCellStSlice_WF : FamilyWF execInstrCellStSlice := by
  intro i next hi hnext
  mvcgen [execInstrCellStSlice, hnext]
  all_goals wf_cells

theorem execInstrCellStb_WF : FamilyWF execInstrCellStb := by
  intro i next hi hnext
  mvcgen [execInstrCellStb, hnext]
  all_goals wf_cells

theorem execInstrCellStbRef_WF : FamilyWF execInstrCellStbRef := by
  intro i next hi hnext
  mvcgen [execInstrCellStbRef, hnext]
  all_goals wf_cells

theorem execInstrCellStref_WF : FamilyWF execInstrCellStref := by
  intro i next hi hnext
  mvcgen [execInstrCellStref, hnext]
  all_goals wf_cells

theorem execInstrCellBbits_WF : FamilyWF execInstrCellBbits := by
  intro i next hi hnext
  mvcgen [execInstrCellBbits, hnext]
  all_goals wf_cells

theorem execInstrCellStSliceConst_WF : FamilyWF execInstrCellStSliceConst := by
  intro i next hi hnext
  mvcgen [execInstrCellStSliceConst, hnext]
  all_goals wf_cells

theorem execInstrCellStZeroes_WF : FamilyWF execInstrCellStZeroes := by
  intro i next hi hnext
  mvcgen [execInstrCellStZeroes, hnext]
  all_goals wf_cells

theorem execInstrCellStOnes_WF : FamilyWF execInstrCellStOnes := by
  intro i next hi hnext
  mvcgen [execInstrCellStOnes, hnext]
  all_goals wf_cells

theorem execInstrCellStSame_WF : FamilyWF execInstrCellStSame := by
  intro i next hi hnext
  mvcgen [execInstrCellStSame, hnext]
  all_goals wf_cells

theorem execInstrCellExt_WF : FamilyWF execInstrCellExt := by
  intro i next hi hnext
  unfold execInstrCellExt
  split
  · split
    · -- BTOS
      mvcgen
      all_goals wf_cells
    · -- STLE
      mvcgen
      all_goals wf_cells
    · -- STREF with a constant reference
      mvcgen
      all_goals wf_cells
    · -- STREF2 with constant references
      mvcgen
      all_goals wf_cells
    · -- HASHBU: the hash and the integer pushed are kept out of sight of `mvcgen` and of the
      -- kernel, which would evaluate the range check of the integer on the hash
      dsimp (config := { zeta := false }) only [VM.KeepsWF, VM.Keeps]
      refine Triple.bind _ _ (VM.checkUnderflow_spec 1) fun _ => ?_
      refine Triple.bind _ _ VM.popBuilder_spec fun b => ?_
      extract_lets c h
      clear_value h
      generalize IntVal.num (Int.ofNat h) = x
      refine Triple.bind _ _ (VM.spec_mono (VM.checkNewCellDepth_spec b.refs) (fun _ h => h.1)
        (fun _ _ h => h) (fun _ _ h => h)) fun _ => ?_
      exact VM.spec_mono (VM.pushIntQuiet_spec x false) (fun _ h => h)
        (fun _ _ h => ⟨h, trivial⟩) (fun _ _ h => h)
    · exact hnext
    · exact hnext
    · -- PLDUZ
      mvcgen
      all_goals wf_cells
    · -- LDVARINT
      mvcgen
      all_goals wf_cells
    · -- STVARINT
      mvcgen
      all_goals wf_cells
    · -- XLOAD: the join point on the resolved cell gets a spec of its own
      dsimp (config := { zeta := false }) only [VM.KeepsWF, VM.Keeps]
      refine Triple.bind _ _ (VM.checkUnderflow_spec 1) fun _ => ?_
      refine Triple.bind _ _ VM.popCell_spec fun c0 => ?_
      have hget : ⦃fun st => ⌜st.WF ∧ c0.WF⌝⦄ (get : VM VmState)
          ⦃post⟨fun _ st => ⌜st.WF ∧ c0.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
        mvcgen
      refine Triple.bind _ _ hget fun g => ?_
      extract_lets jpr jpo jpu
      have hjpr : ∀ r : Except Excno Cell, ⦃fun st => ⌜st.WF ∧ ∀ c, r = .ok c → c.WF⌝⦄ jpr r
          ⦃post⟨fun _ st => ⌜st.WF ∧ True⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
        intro r
        cases r <;> simp only [jpr] <;> mvcgen <;> wf_cells
      clear_value jpr
      mvcgen
      all_goals try wf_cells
      all_goals (refine hjpr _ _ ?_; simp only [SPred.down_pure]; wf_cells)
  · exact hnext

theorem execInstrCell_WF : FamilyWF execInstrCell := by
  intro i next hi hnext
  unfold execInstrCell
  exact execInstrCellCtos_WF i _ hi <|
    execInstrCellXctos_WF i _ hi <|
    execInstrCellNewc_WF i _ hi <|
    execInstrCellEndc_WF i _ hi <|
    execInstrCellEnds_WF i _ hi <|
    execInstrCellSbits_WF i _ hi <|
    execInstrCellSrefs_WF i _ hi <|
    execInstrCellSbitrefs_WF i _ hi <|
    execInstrCellCdepth_WF i _ hi <|
    execInstrCellSempty_WF i _ hi <|
    execInstrCellSdempty_WF i _ hi <|
    execInstrCellSrempty_WF i _ hi <|
    execInstrCellSdCntLead0_WF i _ hi <|
    execInstrCellSdCntTrail0_WF i _ hi <|
    execInstrCellSdEq_WF i _ hi <|
    execInstrCellSdPpfx_WF i _ hi <|
    execInstrCellSdPpfxRev_WF i _ hi <|
    execInstrCellSdPfx_WF i _ hi <|
    execInstrCellSdPfxRev_WF i _ hi <|
    execInstrCellSdLexCmp_WF i _ hi <|
    execInstrCellSdcutfirst_WF i _ hi <|
    execInstrCellSdskipfirst_WF i _ hi <|
    execInstrCellSdcutlast_WF i _ hi <|
    execInstrCellSdskiplast_WF i _ hi <|
    execInstrCellSdBeginsX_WF i _ hi <|
    execInstrCellSdBeginsConst_WF i _ hi <|
    execInstrCellLdu_WF i _ hi <|
    execInstrCellLoadInt_WF i _ hi <|
    execInstrCellLoadIntVar_WF i _ hi <|
    execInstrCellLdref_WF i _ hi <|
    execInstrCellLdrefRtos_WF i _ hi <|
    execInstrCellPldRefIdx_WF i _ hi <|
    execInstrCellLoadSliceX_WF i _ hi <|
    execInstrCellLoadSliceFixed_WF i _ hi <|
    execInstrCellSti_WF i _ hi <|
    execInstrCellStu_WF i _ hi <|
    execInstrCellStIntVar_WF i _ hi <|
    execInstrCellStIntFixed_WF i _ hi <|
    execInstrCellStSlice_WF i _ hi <|
    execInstrCellStb_WF i _ hi <|
    execInstrCellStbRef_WF i _ hi <|
    execInstrCellStref_WF i _ hi <|
    execInstrCellBbits_WF i _ hi <|
    execInstrCellStSliceConst_WF i _ hi <|
    execInstrCellStZeroes_WF i _ hi <|
    execInstrCellStOnes_WF i _ hi <|
    execInstrCellStSame_WF i _ hi <|
    execInstrCellExt_WF i _ hi <|
    hnext

end TvmLean

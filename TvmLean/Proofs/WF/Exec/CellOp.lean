import TvmLean.Proofs.WF.Cells

/-!
# The CellOp family keeps states well-formed

`execInstrCellOp_WF`: every handler of `execInstrCellOp` (`TvmLean/Semantics/Exec/CellOp/`) keeps
`VmState.WF`, so the family does (`CellOpWF`: the operations carry no cell, the handlers do not need
the instruction to be well-formed). Most handlers are `mvcgen` and `wf_cells` (`Cells.lean`); the
others: `BDEPTH` has a loop (its invariant), `CHASHI` and `CHASHIX` bind their steps by hand so that
the hash is never computed (`VM.spec_mono`; the level information is generalized), and `ENDXC`
needs `Builder.finalizeCopy_WF`.
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

/-- What a handler of `execInstrCellOp` owes (its operations carry no cell). -/
def CellOpWF (h : CellInstr → VM Unit → VM Unit) : Prop :=
  ∀ op next, next.KeepsWF → (h op next).KeepsWF

theorem execCellOpExt_WF : CellOpWF execCellOpExt := by
  intro op next hnext
  mvcgen [execCellOpExt, hnext]
  all_goals wf_cells

theorem execCellOpSubslice_WF : CellOpWF execCellOpSubslice := by
  intro op next hnext
  mvcgen [execCellOpSubslice, hnext]
  all_goals wf_cells

theorem execCellOpSplit_WF : CellOpWF execCellOpSplit := by
  intro op next hnext
  mvcgen [execCellOpSplit, hnext]
  all_goals wf_cells

theorem execCellOpPldRefVar_WF : CellOpWF execCellOpPldRefVar := by
  intro op next hnext
  mvcgen [execCellOpPldRefVar, hnext]
  all_goals wf_cells

theorem execCellOpLoadLeInt_WF : CellOpWF execCellOpLoadLeInt := by
  intro op next hnext
  mvcgen [execCellOpLoadLeInt, hnext]
  all_goals wf_cells

theorem execCellOpLdZeroes_WF : CellOpWF execCellOpLdZeroes := by
  intro op next hnext
  mvcgen [execCellOpLdZeroes, hnext]
  all_goals wf_cells

theorem execCellOpLdOnes_WF : CellOpWF execCellOpLdOnes := by
  intro op next hnext
  mvcgen [execCellOpLdOnes, hnext]
  all_goals wf_cells

theorem execCellOpLdSame_WF : CellOpWF execCellOpLdSame := by
  intro op next hnext
  mvcgen [execCellOpLdSame, hnext]
  all_goals wf_cells

theorem execCellOpSdepth_WF : CellOpWF execCellOpSdepth := by
  intro op next hnext
  mvcgen [execCellOpSdepth, hnext]
  all_goals wf_cells

theorem execCellOpClevel_WF : CellOpWF execCellOpClevel := by
  intro op next hnext
  mvcgen [execCellOpClevel, hnext]
  all_goals wf_cells

theorem execCellOpClevelMask_WF : CellOpWF execCellOpClevelMask := by
  intro op next hnext
  mvcgen [execCellOpClevelMask, hnext]
  all_goals wf_cells

theorem execCellOpChashI_WF : CellOpWF execCellOpChashI := by
  intro op next hnext
  unfold execCellOpChashI
  split
  · -- `mvcgen` must not see the hash: the steps are bound by hand and the hash generalized
    dsimp only [VM.KeepsWF, VM.Keeps]
    refine Triple.bind _ _ VM.popCell_spec fun c => ?_
    generalize c.computeLevelInfo? = r
    cases r
    · mvcgen
      all_goals wf_cells
    · simp only [pure_bind]
      generalize bytesToNatBE _ = n
      mvcgen
      all_goals wf_cells
  · exact hnext

theorem execCellOpCdepthI_WF : CellOpWF execCellOpCdepthI := by
  intro op next hnext
  mvcgen [execCellOpCdepthI, hnext]
  all_goals wf_cells

theorem execCellOpChashIX_WF : CellOpWF execCellOpChashIX := by
  intro op next hnext
  unfold execCellOpChashIX
  split
  · -- as for `CHASHI`
    dsimp only [VM.KeepsWF, VM.Keeps]
    refine Triple.bind _ _ (VM.popNatUpTo_spec 3) fun i => ?_
    refine Triple.bind _ _
      (VM.spec_mono VM.popCell_spec (fun _ h => h.1) (fun _ _ h => h) (fun _ _ h => h)) fun c => ?_
    generalize c.computeLevelInfo? = r
    cases r
    · mvcgen
      all_goals wf_cells
    · simp only [pure_bind]
      generalize bytesToNatBE _ = n
      mvcgen
      all_goals wf_cells
  · exact hnext

theorem execCellOpCdepthIX_WF : CellOpWF execCellOpCdepthIX := by
  intro op next hnext
  mvcgen [execCellOpCdepthIX, hnext]
  all_goals wf_cells

theorem execCellOpSchkBits_WF : CellOpWF execCellOpSchkBits := by
  intro op next hnext
  mvcgen [execCellOpSchkBits, hnext]
  all_goals wf_cells

theorem execCellOpSchkRefs_WF : CellOpWF execCellOpSchkRefs := by
  intro op next hnext
  mvcgen [execCellOpSchkRefs, hnext]
  all_goals wf_cells

theorem execCellOpSchkBitRefs_WF : CellOpWF execCellOpSchkBitRefs := by
  intro op next hnext
  mvcgen [execCellOpSchkBitRefs, hnext]
  all_goals wf_cells

theorem execCellOpBdepth_WF : CellOpWF execCellOpBdepth := by
  intro op next hnext
  mvcgen [execCellOpBdepth, hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_cells

theorem execCellOpBrefs_WF : CellOpWF execCellOpBrefs := by
  intro op next hnext
  mvcgen [execCellOpBrefs, hnext]
  all_goals wf_cells

theorem execCellOpBbitrefs_WF : CellOpWF execCellOpBbitrefs := by
  intro op next hnext
  mvcgen [execCellOpBbitrefs, hnext]
  all_goals wf_cells

theorem execCellOpBrembits_WF : CellOpWF execCellOpBrembits := by
  intro op next hnext
  mvcgen [execCellOpBrembits, hnext]
  all_goals wf_cells

theorem execCellOpBremrefs_WF : CellOpWF execCellOpBremrefs := by
  intro op next hnext
  mvcgen [execCellOpBremrefs, hnext]
  all_goals wf_cells

theorem execCellOpBrembitrefs_WF : CellOpWF execCellOpBrembitrefs := by
  intro op next hnext
  mvcgen [execCellOpBrembitrefs, hnext]
  all_goals wf_cells

theorem execCellOpBchkBitsImm_WF : CellOpWF execCellOpBchkBitsImm := by
  intro op next hnext
  mvcgen [execCellOpBchkBitsImm, hnext]
  all_goals wf_cells

theorem execCellOpBchk_WF : CellOpWF execCellOpBchk := by
  intro op next hnext
  mvcgen [execCellOpBchk, hnext]
  all_goals wf_cells

theorem execInstrCellOp_WF : FamilyWF execInstrCellOp := by
  intro i next hi hnext
  unfold execInstrCellOp
  split
  · rename_i op
    exact execCellOpExt_WF op _ <|
      execCellOpSubslice_WF op _ <|
      execCellOpSplit_WF op _ <|
      execCellOpPldRefVar_WF op _ <|
      execCellOpLoadLeInt_WF op _ <|
      execCellOpLdZeroes_WF op _ <|
      execCellOpLdOnes_WF op _ <|
      execCellOpLdSame_WF op _ <|
      execCellOpSdepth_WF op _ <|
      execCellOpClevel_WF op _ <|
      execCellOpClevelMask_WF op _ <|
      execCellOpChashI_WF op _ <|
      execCellOpCdepthI_WF op _ <|
      execCellOpChashIX_WF op _ <|
      execCellOpCdepthIX_WF op _ <|
      execCellOpSchkBits_WF op _ <|
      execCellOpSchkRefs_WF op _ <|
      execCellOpSchkBitRefs_WF op _ <|
      execCellOpBdepth_WF op _ <|
      execCellOpBrefs_WF op _ <|
      execCellOpBbitrefs_WF op _ <|
      execCellOpBrembits_WF op _ <|
      execCellOpBremrefs_WF op _ <|
      execCellOpBrembitrefs_WF op _ <|
      execCellOpBchkBitsImm_WF op _ <|
      execCellOpBchk_WF op _ <|
      hnext
  · exact hnext

end TvmLean

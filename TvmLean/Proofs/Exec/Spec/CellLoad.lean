import TvmLean.Proofs.Exec.Spec.CellCut

/-!
# Specifications: `LDREFRTOS`, `XLOAD`, `XLOADQ` of an ordinary cell

In the format of `Proofs/Exec/Spec/Cell.lean` (`Spec.ctos`): the load of an ordinary cell is charged
(`VmState.registerCellLoad`, out of gas at once):

* `LDREFRTOS` (C++ `exec_load_ref_rev_to_slice`, cellops.cpp) on the stack `s sl`: the rest of the
  slice without its first reference, then that reference loaded as a slice; cell_und without one;
* `XLOAD`, `XLOADQ` (C++ `exec_load_special_cell`): before version 5 the cell back as it is (then -1
  if quiet), not loaded; from version 5 the cell loaded and back (then -1 if quiet).
-/

namespace TvmLean.Spec

/-- `LDREFRTOS` on the stack `s sl`, the first reference of the slice an ordinary cell. -/
@[vm_spec] theorem ldrefRtos (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl))
    (hc : (sl.cell.refs[sl.refPos]!).special = false) :
    ExceptT.run (execInstr .ldrefRtos) st =
      if sl.haveRefs 1 then
        if ({ st with stack := s.push (.slice { sl with refPos := sl.refPos + 1 }) }.registerCellLoad
            sl.cell.refs[sl.refPos]!).gasExhaustedNow then
          (.error .outOfGas, { st with stack := s.push (.slice { sl with refPos := sl.refPos + 1 }) }.registerCellLoad
            sl.cell.refs[sl.refPos]!)
        else
          (.ok (), { { st with stack := s.push (.slice { sl with refPos := sl.refPos + 1 }) }.registerCellLoad
              sl.cell.refs[sl.refPos]! with
            stack := (s.push (.slice { sl with refPos := sl.refPos + 1 })).push
              (.slice (Slice.ofCell sl.cell.refs[sl.refPos]!)) })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs, hc]

set_option maxHeartbeats 1000000 in
/-- `XLOAD` (`q` false), `XLOADQ` (`q` true) of an ordinary cell on the stack `s c`. -/
@[vm_spec] theorem xload (st : VmState) (s : Stack) (c : Cell) (q : Bool) (hs : st.stack = s.push (.cell c))
    (hc : c.special = false) :
    ExceptT.run (execInstr (.cellExt (.xload q))) st =
      if st.globalVersion < 5 then
        (.ok (), { st with stack := if q then (s.push (.cell c)).push (.int (.num (-1))) else s.push (.cell c) })
      else if ({ st with stack := s }.registerCellLoad c).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s }.registerCellLoad c)
      else
        (.ok (), { { st with stack := s }.registerCellLoad c with
          stack := if q then (s.push (.cell c)).push (.int (.num (-1))) else s.push (.cell c) }) := by
  -- the version and the flag decided on the right first (the contextual simp of vm_simp loops on a
  -- branch that assumes a false literal)
  by_cases hv : st.globalVersion < 5
  · cases q
    · simp only [hv, if_true, if_false, Bool.false_eq_true]; vm_simp [hs, hv]
    · simp only [hv, if_true]; vm_simp [hs, hv]
  · cases q
    · simp only [hv, if_false, Bool.false_eq_true]; vm_simp [hs, hv, hc, VM.registerCellLoadSpecial]
    · simp only [hv, if_true, if_false]; vm_simp [hs, hv, hc, VM.registerCellLoadSpecial]

end TvmLean.Spec

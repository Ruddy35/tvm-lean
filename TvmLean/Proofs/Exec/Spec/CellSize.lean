import TvmLean.Proofs.Exec.Spec.CellExt

/-!
# Specifications: `CDATASIZE`, `SDATASIZE` and their quiet forms

In the format of `Proofs/Exec/Spec/CellExt.lean`: C++ `exec_compute_data_size` (tonops.cpp:1528),
the number of distinct cells, bits and references below a cell or in a slice, at most a bound of
cells (cell_ov above it, `0` if quiet). The count is the model's function, kept opaque: the run of
`VM.visitDataSizeCell` (C++ `VmStorageStat::add_storage`, which charges each new cell's load) from
the state with the operands popped, and for a slice the loop over its references `sdataSizeLoop`
(the loop of the model's `VM.execSdataSize`); the results are pushed on the stack of the state the
count leaves.

* `CDATASIZE`, `CDATASIZEQ` (opcodes `F941`, `F940`): `cdataSize` on a cell, `cdataSize_null` on
  null (`0 0 0`);
* `SDATASIZE`, `SDATASIZEQ` (opcodes `F943`, `F942`): `sdataSize`.

The bound is an integer on top, range_chk if negative; above `2^63 - 1` it is `2^63 - 1`. The
`try ... catch` of the handlers is `VM.run_tryCatch`.
-/

namespace TvmLean

/-- `try x catch h` in the VM: the result of `x`, or `h` run on its exception from the state `x`
left. -/
@[vm_run] theorem VM.run_tryCatch {α : Type} (x : VM α) (h : Excno → VM α) (st : VmState) :
    ExceptT.run (tryCatch x h) st =
      match ExceptT.run x st with
      | (.ok a, st') => (.ok a, st')
      | (.error e, st') => ExceptT.run (h e) st' := by
  change (ExceptT.tryCatch x h).run st = _
  unfold ExceptT.tryCatch ExceptT.run ExceptT.mk
  simp only [bind, StateT.bind]
  generalize x st = p
  rcases p with ⟨r, st'⟩
  cases r <;> rfl

/-- `VM.visitDataSizeCell` as its well-founded definition leaves it (`unfoldModelRun` unfolds it to
`_unary`). -/
theorem VM.visitDataSizeCell_unary (l : Nat) (c : Cell) (a : DataSizeAcc) :
    VM.visitDataSizeCell._unary l ⟨c, a⟩ = VM.visitDataSizeCell l c a := by
  delta VM.visitDataSizeCell; rfl

/-- The loop of `SDATASIZE` (C++ `exec_compute_data_size` on a slice, tonops.cpp:1528-1556; the
loop of the model's `VM.execSdataSize`): from the bits and references left in the slice, each
reference counted by `VM.visitDataSizeCell` with the bound `limit`; cell_ov stops the loop with
the flag `false`. -/
def sdataSizeLoop (limit : Nat) (s : Slice) : VM (MProd DataSizeAcc Bool) :=
  forIn [s.refPos:s.cell.refs.size]
    (⟨{ DataSizeAcc.empty with bits := s.bitsRemaining, refs := s.refsRemaining }, true⟩ : MProd DataSizeAcc Bool)
    fun i r => do
      let res ← tryCatch
        (do
          let acc' ← VM.visitDataSizeCell limit s.cell.refs[i]! r.1
          pure (DoResultSBC.pureReturn () (⟨acc', r.2⟩ : MProd DataSizeAcc Bool)))
        (fun ex => match ex with
          | .cellOv => pure (DoResultSBC.break (⟨r.1, false⟩ : MProd DataSizeAcc Bool))
          | e => throw e)
      match res with
      | .pureReturn _ u => pure (ForInStep.yield ⟨u.1, u.2⟩)
      | .break u => pure (ForInStep.done ⟨u.1, u.2⟩)
      | .continue u => pure (ForInStep.yield ⟨u.1, u.2⟩)

namespace Spec

/-- The handler with the flag `quiet` decided, reached by `unfoldModelRun`. -/
local macro "data_size_pre" : tactic =>
  `(tactic| simp only [TvmLean.Exec.reduceExecInstrRun, TvmLean.Exec.unfoldModelRun, VM.run_bind, VM.run_get,
    VM.bindRes_ok, Bool.false_eq_true, if_false, if_true])

/-- `CDATASIZE`, `CDATASIZEQ` (C++ `exec_compute_data_size`, tonops.cpp:1528-1556, mode 0 and 1,
opcodes `F941`, `F940`) on a cell: the bound `n` on top (range_chk if negative), the cell below;
the numbers of distinct cells, bits and references below it counted by `VM.visitDataSizeCell`, then
-1 if quiet; cell_ov from the count (more cells than the bound) is `0` if quiet, other exceptions
(out of gas) are raised. -/
@[vm_spec] theorem cdataSize (st : VmState) (s : Stack) (c : Cell) (n : Int) (quiet : Bool)
    (hs : st.stack = (s.push (.cell c)).push (.int (.num n))) :
    ExceptT.run (execInstr (.cellExt (.cdataSize quiet))) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else
        match ExceptT.run (VM.visitDataSizeCell (if 9223372036854775807 < n then 9223372036854775807 else n.toNat) c
            DataSizeAcc.empty) { st with stack := s } with
        | (.ok acc, st') =>
          (.ok (), { st' with
            stack :=
              let s1 := ((st'.stack.push (.int (.num acc.cells))).push (.int (.num acc.bits))).push (.int (.num acc.refs))
              if quiet then s1.push (.int (.num (-1))) else s1 })
        | (.error e, st') =>
          if quiet then
            if e = .cellOv then (.ok (), { st' with stack := st'.stack.push (.int (.num 0)) }) else (.error e, st')
          else (.error e, st') := by
  by_cases hn : n < 0
  · cases quiet <;> vm_simp [hs, hn]
  · generalize hr : ExceptT.run (VM.visitDataSizeCell (if 9223372036854775807 < n then 9223372036854775807 else n.toNat)
      c DataSizeAcc.empty) { st with stack := s } = r
    cases quiet <;> data_size_pre <;> vm_simp [hs, hn, Nat.reduceShiftLeft] <;>
      rw [VM.visitDataSizeCell_unary, hr] <;> rcases r with ⟨e | acc, st'⟩ <;>
      first | (cases e <;> vm_simp) | vm_simp

/-- `CDATASIZE`, `CDATASIZEQ` on null: `0 0 0` (then -1 if quiet). -/
@[vm_spec] theorem cdataSize_null (st : VmState) (s : Stack) (n : Int) (quiet : Bool)
    (hs : st.stack = (s.push .null).push (.int (.num n))) :
    ExceptT.run (execInstr (.cellExt (.cdataSize quiet))) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else (.ok (), { st with
        stack :=
          let s1 := ((s.push (.int (.num 0))).push (.int (.num 0))).push (.int (.num 0))
          if quiet then s1.push (.int (.num (-1))) else s1 }) := by
  cases quiet <;> data_size_pre <;> vm_simp [hs]

/-- `SDATASIZE`, `SDATASIZEQ` (C++ `exec_compute_data_size`, tonops.cpp:1528-1556, mode 2 and 3,
opcodes `F943`, `F942`): the bound `n` on top (range_chk if negative), the slice below; the bits and
references left in the slice and the distinct cells below its references (`sdataSizeLoop`), then
-1 if quiet; if the count stops on cell_ov, `0` if quiet, else cell_ov. -/
@[vm_spec] theorem sdataSize (st : VmState) (s : Stack) (sl : Slice) (n : Int) (quiet : Bool)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num n))) :
    ExceptT.run (execInstr (.cellExt (.sdataSize quiet))) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else
        match ExceptT.run (sdataSizeLoop (if 9223372036854775807 < n then 9223372036854775807 else n.toNat) sl)
            { st with stack := s } with
        | (.ok r, st') =>
          if r.2 then
            (.ok (), { st' with
              stack :=
                let s1 := ((st'.stack.push (.int (.num r.1.cells))).push (.int (.num r.1.bits))).push
                  (.int (.num r.1.refs))
                if quiet then s1.push (.int (.num (-1))) else s1 })
          else if quiet then (.ok (), { st' with stack := st'.stack.push (.int (.num 0)) })
          else (.error .cellOv, st')
        | (.error e, st') => (.error e, st') := by
  by_cases hn : n < 0
  · cases quiet <;> vm_simp [hs, hn]
  · generalize hr : ExceptT.run (sdataSizeLoop (if 9223372036854775807 < n then 9223372036854775807 else n.toNat) sl)
      { st with stack := s } = r
    cases quiet <;> data_size_pre <;> vm_simp [hs, hn, Nat.reduceShiftLeft] <;>
      change VM.bindRes (ExceptT.run (sdataSizeLoop (if 9223372036854775807 < n then 9223372036854775807 else n.toNat)
        sl) { st with stack := s }) _ = _ <;>
      rw [hr] <;> rcases r with ⟨e | ⟨acc, ok⟩, st'⟩ <;> first | vm_simp | (cases ok <;> vm_simp)

end Spec

end TvmLean

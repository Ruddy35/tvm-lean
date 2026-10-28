import TvmLean.Proofs.Exec.Spec.Cell

/-!
# Specifications: dictionaries loaded and stored

`LDDICT`, `PLDDICT` (C++ `exec_load_dict`, dictops.cpp) and `STDICT` (C++
`exec_store_dict`) in the format of `Proofs/Exec/Spec/Cell.lean`: a dictionary in a slice is a bit
(`1` if it is not empty) and, if the bit is `1`, a reference to its root (`HashmapE`, `Maybe ^Cell`);
on the stack, the root cell or `null`. Nothing is loaded (the root is not read).
-/

namespace TvmLean.Spec

/-- `LDDICT` (C++ `exec_load_dict`): the first bit of the slice says whether a root follows (its
first reference); pushed the root (or `null`), then the rest of the slice. A slice without that bit
or that reference: cell_und. -/
@[vm_spec] theorem lddict (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.lddict false false)) st =
      if (sl.haveBits 1 && sl.haveRefs (if (sl.readBits 1)[0]! then 1 else 0)) = true then
        (.ok (), { st with stack :=
          ((s.push (if (sl.readBits 1)[0]! then .cell sl.cell.refs[sl.refPos]! else .null)).push
            (.slice { sl with bitPos := sl.bitPos + 1, refPos := sl.refPos + (if (sl.readBits 1)[0]! then 1 else 0) })) })
      else (.error .cellUnd, { st with stack := s }) := by
  by_cases h1 : sl.haveBits 1 = true
  · by_cases h2 : (sl.readBits 1)[0]! = true
    · by_cases h3 : sl.haveRefs 1 = true
      · simp only [h1, h2, h3, if_true, Bool.and_true]; vm_simp [hs, h1, h2, h3]
      · simp only [h1, h2, h3, if_true, Bool.and_false, Bool.false_eq_true, if_false]; vm_simp [hs, h1, h2, h3]
    · simp only [Bool.not_eq_true] at h2
      by_cases h3 : sl.haveRefs 0 = true
      · simp only [h1, h2, h3, if_true, Bool.and_true, Bool.false_eq_true, if_false]; vm_simp [hs, h1, h2, h3]
      · simp only [h1, h2, h3, Bool.and_false, Bool.false_eq_true, if_false]; vm_simp [hs, h1, h2, h3]
  · simp only [Bool.not_eq_true] at h1
    simp only [h1, Bool.false_and, Bool.false_eq_true, if_false]; vm_simp [hs, h1]

/-- `PLDDICT` (C++ `exec_load_dict` with preload): the root (or `null`) pushed, the slice dropped;
cell_und as `LDDICT`. -/
@[vm_spec] theorem plddict (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.lddict true false)) st =
      if (sl.haveBits 1 && sl.haveRefs (if (sl.readBits 1)[0]! then 1 else 0)) = true then
        (.ok (), { st with stack := s.push (if (sl.readBits 1)[0]! then .cell sl.cell.refs[sl.refPos]! else .null) })
      else (.error .cellUnd, { st with stack := s }) := by
  by_cases h1 : sl.haveBits 1 = true
  · by_cases h2 : (sl.readBits 1)[0]! = true
    · by_cases h3 : sl.haveRefs 1 = true
      · simp only [h1, h2, h3, if_true, Bool.and_true]; vm_simp [hs, h1, h2, h3]
      · simp only [h1, h2, h3, if_true, Bool.and_false, Bool.false_eq_true, if_false]; vm_simp [hs, h1, h2, h3]
    · simp only [Bool.not_eq_true] at h2
      by_cases h3 : sl.haveRefs 0 = true
      · simp only [h1, h2, h3, if_true, Bool.and_true, Bool.false_eq_true, if_false]; vm_simp [hs, h1, h2, h3]
      · simp only [h1, h2, h3, Bool.and_false, Bool.false_eq_true, if_false]; vm_simp [hs, h1, h2, h3]
  · simp only [Bool.not_eq_true] at h1
    simp only [h1, Bool.false_and, Bool.false_eq_true, if_false]; vm_simp [hs, h1]

/-- `STDICT` (C++ `exec_store_dict`) of the empty dictionary (`null`): the bit `0` stored; cell_ov
if the builder is full. -/
@[vm_spec] theorem stdict_null (st : VmState) (s : Stack) (b : Builder)
    (hs : st.stack = (s.push .null).push (.builder b)) :
    ExceptT.run (execInstr .stdict) st =
      if b.canExtendBy 1 0 then (.ok (), { st with stack := s.push (.builder (b.storeBits #[false])) })
      else (.error .cellOv, { st with stack := s }) := by
  vm_simp [hs, Option.isSome_none]

/-- `STDICT` of a root cell: the bit `1` stored and the root as the next reference; cell_ov if the
builder has no room for them. -/
@[vm_spec] theorem stdict_cell (st : VmState) (s : Stack) (c : Cell) (b : Builder)
    (hs : st.stack = (s.push (.cell c)).push (.builder b)) :
    ExceptT.run (execInstr .stdict) st =
      if b.canExtendBy 1 1 then
        (.ok (), { st with stack := s.push (.builder { b.storeBits #[true] with refs := b.refs.push c }) })
      else (.error .cellOv, { st with stack := s }) := by
  vm_simp [hs, Builder.storeBits, Option.isSome_some]

end TvmLean.Spec

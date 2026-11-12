import TvmLean.Proofs.Exec.Spec.DictLoad

/-!
# Specifications: dictionaries in slices skipped, cut, loaded quietly

In the format of `Proofs/Exec/Spec/DictLoad.lean` (a dictionary in a slice is a bit and, if it is
`1`, a reference; nothing loaded), the conditions in the order of the model's handlers:

* `SKIPDICT` (C++ `exec_skip_dict`, dictops.cpp): the slice without the dictionary; cell_und if it
  has not the bit, or not the reference the bit asks for;
* `LDDICTS`, `PLDDICTS` (C++ `exec_load_dict_slice`): the dictionary as a new slice
  (`Slice.prefixCell`), then the rest of the slice unless prefetching; cell_und as `SKIPDICT`;
* `LDDICTQ`, `PLDDICTQ` (C++ `exec_load_dict` quiet): as `LDDICT`, `PLDDICT`, then -1; a slice
  without the dictionary back (unless prefetching), then 0.
-/

namespace TvmLean.Spec

/-- `SKIPDICT` on the stack `s sl`. -/
@[vm_spec] theorem skipdict (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .skipdict) st =
      if sl.haveBits 1 then
        if sl.haveRefs (if (sl.readBits 1)[0]! then 1 else 0) then
          (.ok (), { st with stack := s.push (.slice
            { sl with bitPos := sl.bitPos + 1, refPos := sl.refPos + (if (sl.readBits 1)[0]! then 1 else 0) }) })
        else (.error .cellUnd, { st with stack := s })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

/-- `LDDICTS` (`p` false), `PLDDICTS` (`p` true) on the stack `s sl`. -/
@[vm_spec] theorem lddicts (st : VmState) (s : Stack) (sl : Slice) (p : Bool) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.dictExt (.lddicts p))) st =
      if sl.haveBits 1 then
        if sl.haveRefs (if (sl.readBits 1)[0]! then 1 else 0) then
          let rest : Slice :=
            { sl with bitPos := sl.bitPos + 1, refPos := sl.refPos + (if (sl.readBits 1)[0]! then 1 else 0) }
          let s1 := s.push (.slice (Slice.ofCell (Slice.prefixCell sl rest)))
          (.ok (), { st with stack := if p then s1 else s1.push (.slice rest) })
        else (.error .cellUnd, { st with stack := s })
      else (.error .cellUnd, { st with stack := s }) := by
  cases p <;> (try simp only [if_true, if_false, Bool.false_eq_true]) <;> vm_simp [hs]

/-- `LDDICTQ` (`p` false), `PLDDICTQ` (`p` true) on the stack `s sl`: the condition of the handler is
the bit, then the reference it asks for. -/
@[vm_spec] theorem lddictQ (st : VmState) (s : Stack) (sl : Slice) (p : Bool) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.lddict p true)) st =
      if (if sl.haveBits 1 then sl.haveRefs (if (sl.readBits 1)[0]! then 1 else 0) else false) = true then
        let rest : Slice :=
          { sl with bitPos := sl.bitPos + 1, refPos := sl.refPos + (if (sl.readBits 1)[0]! then 1 else 0) }
        if (sl.readBits 1)[0]! then
          let s1 := s.push (.cell sl.cell.refs[sl.refPos]!)
          (.ok (), { st with stack := (if p then s1 else s1.push (.slice rest)).push (.int (.num (-1))) })
        else
          let s1 := s.push .null
          (.ok (), { st with stack := (if p then s1 else s1.push (.slice rest)).push (.int (.num (-1))) })
      else (.ok (), { st with stack := (if p then s else s.push (.slice sl)).push (.int (.num 0)) }) := by
  cases p <;> (try simp only [if_true, if_false, Bool.false_eq_true]) <;> vm_simp [hs]

end TvmLean.Spec

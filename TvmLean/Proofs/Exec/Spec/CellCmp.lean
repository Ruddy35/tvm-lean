import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: prefixes and suffixes of slices, the size checks of a slice, quiet reference stores

In the format of `Proofs/Exec/Spec/Stack.lean`, on any slices and builders; a count from the stack
is an integer, range_chk outside its range (C++ `pop_smallint_range`, the count popped).

* `SDPFX`, `SDPFXREV`, `SDPPFX`, `SDPPFXREV`, `SDSFX`, `SDSFXREV`, `SDPSFX`, `SDPSFXREV` (C++
  `exec_bin_cs_cmp`, cellops.cpp:268, 321-328) on the stack `s s1 s2`: -1 if the bits of `s1` are a
  (proper) prefix, suffix of those of `s2` (`REV`: of `s2` in `s1`), else 0;
* `SCHKBITS`, `SCHKREFS`, `SCHKBITREFS` and their quiet forms (C++ `exec_slice_chk_op_args`,
  `exec_slice_chk_op_args2`, cellops.cpp:1286, 1302): whether the slice has `n` bits, `r`
  references, both; cell_und or a flag;
* `STREFQ` (C++ `exec_store_ref`, quiet, cellops.cpp:416) on the stack `s c b`, `STREFR`, `STREFRQ`
  (C++ `exec_store_ref_rev`, cellops.cpp:439) on the stack `s b c`: the cell as a new reference of
  the builder; if it has four, cell_ov, or (quiet) the stack back and -1.
-/

namespace TvmLean.Spec

/-- `SDPFX` (C++ `exec_bin_cs_cmp`, `is_prefix_of`) on the stack `s p sl`: whether the bits of `p`
are a prefix of those of `sl`. -/
@[vm_spec] theorem sdPfx (st : VmState) (s : Stack) (p sl : Slice)
    (hs : st.stack = (s.push (.slice p)).push (.slice sl)) :
    ExceptT.run (execInstr .sdPfx) st =
      (.ok (), { st with stack := s.push (.int (.num (if sl.haveBits (p.readBits p.bitsRemaining).size &&
        sl.readBits (p.readBits p.bitsRemaining).size == p.readBits p.bitsRemaining then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDPFXREV` on the stack `s sl p`: whether the bits of `p` are a prefix of those of `sl`. -/
@[vm_spec] theorem sdPfxRev (st : VmState) (s : Stack) (sl p : Slice)
    (hs : st.stack = (s.push (.slice sl)).push (.slice p)) :
    ExceptT.run (execInstr .sdPfxRev) st =
      (.ok (), { st with stack := s.push (.int (.num (if sl.haveBits (p.readBits p.bitsRemaining).size &&
        sl.readBits (p.readBits p.bitsRemaining).size == p.readBits p.bitsRemaining then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDPPFX` (`is_proper_prefix_of`) on the stack `s p sl`: whether the bits of `p` are a proper
prefix of those of `sl`. -/
@[vm_spec] theorem sdPpfx (st : VmState) (s : Stack) (p sl : Slice)
    (hs : st.stack = (s.push (.slice p)).push (.slice sl)) :
    ExceptT.run (execInstr .sdPpfx) st =
      (.ok (), { st with stack := s.push (.int (.num (if (p.readBits p.bitsRemaining).size <
          (sl.readBits sl.bitsRemaining).size &&
        (sl.readBits sl.bitsRemaining).take (p.readBits p.bitsRemaining).size == p.readBits p.bitsRemaining
        then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDPPFXREV` on the stack `s sl p`: whether the bits of `p` are a proper prefix of those of
`sl`. -/
@[vm_spec] theorem sdPpfxRev (st : VmState) (s : Stack) (sl p : Slice)
    (hs : st.stack = (s.push (.slice sl)).push (.slice p)) :
    ExceptT.run (execInstr .sdPpfxRev) st =
      (.ok (), { st with stack := s.push (.int (.num (if (p.readBits p.bitsRemaining).size <
          (sl.readBits sl.bitsRemaining).size &&
        (sl.readBits sl.bitsRemaining).extract 0 (p.readBits p.bitsRemaining).size == p.readBits p.bitsRemaining
        then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDSFX` (`is_suffix_of`) on the stack `s s1 s2`: whether the bits of `s1` are a suffix of those
of `s2` (`sliceBitsSuffixEq`). -/
@[vm_spec] theorem sdSfx (st : VmState) (s : Stack) (s1 s2 : Slice)
    (hs : st.stack = (s.push (.slice s1)).push (.slice s2)) :
    ExceptT.run (execInstr (.cellOp .sdSfx)) st =
      (.ok (), { st with stack := s.push (.int (.num (if sliceBitsSuffixEq s1 s2 then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDSFXREV` on the stack `s s1 s2`: whether the bits of `s2` are a suffix of those of `s1`. -/
@[vm_spec] theorem sdSfxRev (st : VmState) (s : Stack) (s1 s2 : Slice)
    (hs : st.stack = (s.push (.slice s1)).push (.slice s2)) :
    ExceptT.run (execInstr (.cellOp .sdSfxRev)) st =
      (.ok (), { st with stack := s.push (.int (.num (if sliceBitsSuffixEq s2 s1 then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDPSFX` (`is_proper_suffix_of`) on the stack `s s1 s2`: whether the bits of `s1` are a proper
suffix of those of `s2`. -/
@[vm_spec] theorem sdPsfx (st : VmState) (s : Stack) (s1 s2 : Slice)
    (hs : st.stack = (s.push (.slice s1)).push (.slice s2)) :
    ExceptT.run (execInstr (.cellOp .sdPsfx)) st =
      (.ok (), { st with stack := s.push (.int (.num
        (if s1.bitsRemaining < s2.bitsRemaining && sliceBitsSuffixEq s1 s2 then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDPSFXREV` on the stack `s s1 s2`: whether the bits of `s2` are a proper suffix of those of
`s1`. -/
@[vm_spec] theorem sdPsfxRev (st : VmState) (s : Stack) (s1 s2 : Slice)
    (hs : st.stack = (s.push (.slice s1)).push (.slice s2)) :
    ExceptT.run (execInstr (.cellOp .sdPsfxRev)) st =
      (.ok (), { st with stack := s.push (.int (.num
        (if s2.bitsRemaining < s1.bitsRemaining && sliceBitsSuffixEq s2 s1 then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SCHKBITS` (`q` false), `SCHKBITSQ` (`q` true) (C++ `exec_slice_chk_op_args`) on the stack
`s sl n`: whether the slice has `n` bits (range_chk outside `0..1023`); cell_und if not, or a flag. -/
@[vm_spec] theorem schkBits (st : VmState) (s : Stack) (sl : Slice) (n : Int) (q : Bool)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num n))) :
    ExceptT.run (execInstr (.cellOp (.schkBits q))) st =
      if 0 ≤ n ∧ n ≤ 1023 then
        if q then (.ok (), { st with stack := s.push (.int (.num (if sl.haveBits n.toNat then -1 else 0))) })
        else if sl.haveBits n.toNat then (.ok (), { st with stack := s })
        else (.error .cellUnd, { st with stack := s })
      else (.error .rangeChk, { st with stack := s.push (.slice sl) }) := by
  by_cases hm : 0 ≤ n ∧ n ≤ 1023
  · have h1 : ¬ n < 0 := by omega
    have h2 : ¬ n.toNat > 1023 := by omega
    rw [if_pos hm]
    cases q <;> cases h : sl.haveBits n.toNat <;> vm_simp [hs, h1, h2, h]
  · rw [if_neg hm]
    by_cases h1 : n < 0
    · cases q <;> vm_simp [hs, h1]
    · have h2 : n.toNat > 1023 := by omega
      cases q <;> vm_simp [hs, h1, h2]

/-- `SCHKREFS` (`q` false), `SCHKREFSQ` (`q` true) on the stack `s sl r`: whether the slice has `r`
references (range_chk outside `0..1023`); cell_und if not, or a flag. -/
@[vm_spec] theorem schkRefs (st : VmState) (s : Stack) (sl : Slice) (r : Int) (q : Bool)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num r))) :
    ExceptT.run (execInstr (.cellOp (.schkRefs q))) st =
      if 0 ≤ r ∧ r ≤ 1023 then
        if q then (.ok (), { st with stack := s.push (.int (.num (if sl.haveRefs r.toNat then -1 else 0))) })
        else if sl.haveRefs r.toNat then (.ok (), { st with stack := s })
        else (.error .cellUnd, { st with stack := s })
      else (.error .rangeChk, { st with stack := s.push (.slice sl) }) := by
  by_cases hm : 0 ≤ r ∧ r ≤ 1023
  · have h1 : ¬ r < 0 := by omega
    have h2 : ¬ r.toNat > 1023 := by omega
    rw [if_pos hm]
    cases q <;> cases h : sl.haveRefs r.toNat <;> vm_simp [hs, h1, h2, h]
  · rw [if_neg hm]
    by_cases h1 : r < 0
    · cases q <;> vm_simp [hs, h1]
    · have h2 : r.toNat > 1023 := by omega
      cases q <;> vm_simp [hs, h1, h2]

/-- `SCHKBITREFS` (`q` false), `SCHKBITREFSQ` (`q` true) (C++ `exec_slice_chk_op_args2`) on the
stack `s sl n r`: whether the slice has `n` bits and `r` references (range_chk outside `0..4` for
`r`, then outside `0..1023` for `n`); cell_und if not, or a flag. -/
@[vm_spec] theorem schkBitRefs (st : VmState) (s : Stack) (sl : Slice) (n r : Int) (q : Bool)
    (hs : st.stack = ((s.push (.slice sl)).push (.int (.num n))).push (.int (.num r))) :
    ExceptT.run (execInstr (.cellOp (.schkBitRefs q))) st =
      if 0 ≤ r ∧ r ≤ 4 then
        if 0 ≤ n ∧ n ≤ 1023 then
          if q then
            (.ok (), { st with stack := s.push (.int (.num
              (if sl.haveBits n.toNat && sl.haveRefs r.toNat then -1 else 0))) })
          else if sl.haveBits n.toNat && sl.haveRefs r.toNat then (.ok (), { st with stack := s })
          else (.error .cellUnd, { st with stack := s })
        else (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num n)) }) := by
  by_cases hr : 0 ≤ r ∧ r ≤ 4
  · have g1 : ¬ r < 0 := by omega
    have g2 : ¬ r.toNat > 4 := by omega
    rw [if_pos hr]
    by_cases hm : 0 ≤ n ∧ n ≤ 1023
    · have h1 : ¬ n < 0 := by omega
      have h2 : ¬ n.toNat > 1023 := by omega
      rw [if_pos hm]
      cases q <;> cases ha : sl.haveBits n.toNat <;> cases hb : sl.haveRefs r.toNat <;>
        vm_simp [hs, g1, g2, h1, h2, ha, hb]
    · rw [if_neg hm]
      by_cases h1 : n < 0
      · cases q <;> vm_simp [hs, g1, g2, h1]
      · have h2 : n.toNat > 1023 := by omega
        cases q <;> vm_simp [hs, g1, g2, h1, h2]
  · rw [if_neg hr]
    by_cases g1 : r < 0
    · cases q <;> vm_simp [hs, g1]
    · have g2 : r.toNat > 4 := by omega
      cases q <;> vm_simp [hs, g1, g2]

/-- `STREFQ` (C++ `exec_store_ref`, quiet) on the stack `s c b`: the cell as a new reference of the
builder and 0; if it has four, the stack back and -1. -/
@[vm_spec] theorem strefq (st : VmState) (s : Stack) (c : Cell) (b : Builder)
    (hs : st.stack = (s.push (.cell c)).push (.builder b)) :
    ExceptT.run (execInstr .strefq) st =
      if b.canExtendBy 0 1 then
        (.ok (), { st with stack := (s.push (.builder { b with refs := b.refs.push c })).push (.int (.num 0)) })
      else (.ok (), { st with stack := ((s.push (.cell c)).push (.builder b)).push (.int (.num (-1))) }) := by
  cases h : b.canExtendBy 0 1 <;> vm_simp [hs, h]

/-- `STREFR` (C++ `exec_store_ref_rev`) on the stack `s b c`: the cell as a new reference of the
builder; cell_ov if it has four. -/
@[vm_spec] theorem strefR (st : VmState) (s : Stack) (b : Builder) (c : Cell)
    (hs : st.stack = (s.push (.builder b)).push (.cell c)) :
    ExceptT.run (execInstr (.cellOp (.strefR false))) st =
      if b.canExtendBy 0 1 then (.ok (), { st with stack := s.push (.builder { b with refs := b.refs.push c }) })
      else (.error .cellOv, { st with stack := s }) := by
  cases h : b.canExtendBy 0 1 <;> vm_simp [hs, h]

/-- `STREFRQ` (C++ `exec_store_ref_rev`, quiet) on the stack `s b c`: the cell as a new reference of
the builder and 0; if it has four, the stack back and -1. -/
@[vm_spec] theorem strefRQ (st : VmState) (s : Stack) (b : Builder) (c : Cell)
    (hs : st.stack = (s.push (.builder b)).push (.cell c)) :
    ExceptT.run (execInstr (.cellOp (.strefR true))) st =
      if b.canExtendBy 0 1 then
        (.ok (), { st with stack := (s.push (.builder { b with refs := b.refs.push c })).push (.int (.num 0)) })
      else (.ok (), { st with stack := ((s.push (.builder b)).push (.cell c)).push (.int (.num (-1))) }) := by
  cases h : b.canExtendBy 0 1 <;> vm_simp [hs, h]

end TvmLean.Spec

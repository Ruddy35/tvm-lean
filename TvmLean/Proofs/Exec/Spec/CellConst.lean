import TvmLean.Proofs.Exec.Spec.Cell

/-!
# Specifications: constant slices and references of the code, builder sizes, runs of equal bits

In the format of `Proofs/Exec/Spec/Stack.lean`, on any slice or builder; a count from the stack is
an integer, range_chk outside its range (C++ `pop_smallint_range`, the count popped).

* `PUSHSLICE`, `PUSHSLICE_REFS`, `PUSHSLICE_LONG` (C++ `exec_push_slice_common`, cellops.cpp:83;
  one instruction of the model, `.pushSliceConst`): the slice of the code pushed; `PUSHNAN` (C++
  `exec_push_nan`, arithops.cpp:121): NaN pushed;
* `PUSHREFSLICE` (C++ `exec_push_ref`, mode 1, cellops.cpp:33) of an ordinary cell: its load charged
  (out of gas at once), its slice pushed;
* `STSLICECONST` (C++ `exec_store_const_slice`, cellops.cpp:777): the slice of the code appended to
  the builder; `STREFCONST`, `STREF2CONST` (C++ `exec_store_const_ref`, cellops.cpp:648): the
  references of the code; cell_ov if the builder has no room;
* `BTOS` (C++ `exec_builder_to_slice`, cellops.cpp:768): the builder finished (not charged, cell_ov
  above the maximal depth) and its slice pushed;
* `BBITREFS`, `BREMREFS`, `BREMBITREFS` (C++ `exec_2int_builder_func`, `exec_int_builder_func`,
  cellops.cpp:853-865): the bits and references of the builder, the references and bits left;
  `BCHKBITS k`, `BCHKBITSQ k` (C++ `exec_builder_chk_bits`, cellops.cpp:724): whether `k` bits fit,
  cell_ov or a flag;
* `SDFIRST` (C++ `exec_un_cs_cmp`, cellops.cpp:318): whether the slice begins with a one bit;
* `LDZEROES`, `LDONES`, `LDSAME` (C++ `exec_load_same`, cellops.cpp:1372): the number of leading
  zeroes, ones, bits equal to the flag, and the slice without them;
* `STZEROES`, `STONES`, `STSAME` (C++ `exec_store_same`, cellops.cpp:753): `n` zeroes, ones, bits
  equal to the flag appended; cell_ov if they do not fit.
-/

namespace TvmLean.Spec

/-- `PUSHSLICE`, `PUSHSLICE_REFS`, `PUSHSLICE_LONG` (C++ `exec_push_slice_common`): the slice of the
code is pushed. -/
@[vm_spec] theorem pushSliceConst (st : VmState) (sl : Slice) :
    ExceptT.run (execInstr (.pushSliceConst sl)) st = (.ok (), { st with stack := st.stack.push (.slice sl) }) := by
  vm_simp

/-- `PUSHNAN` (C++ `exec_push_nan`): NaN is pushed. -/
@[vm_spec] theorem pushNan (st : VmState) :
    ExceptT.run (execInstr (.pushInt .nan)) st = (.ok (), { st with stack := st.stack.push (.int .nan) }) := by
  vm_simp

/-- `PUSHREFSLICE` (C++ `exec_push_ref`, mode 1) of an ordinary cell: its load is charged (out of gas
at once), its slice pushed. -/
@[vm_spec] theorem pushRefSlice (st : VmState) (c : Cell) (hc : c.special = false) :
    ExceptT.run (execInstr (.pushRefSlice c)) st =
      if (st.registerCellLoad c).gasExhaustedNow then
        (.error .outOfGas, st.registerCellLoad c)
      else
        (.ok (), { st.registerCellLoad c with stack := st.stack.push (.slice (Slice.ofCell c)) }) := by
  vm_simp [hc]

/-- `STSLICECONST` (C++ `exec_store_const_slice`) on the stack `s b`: the bits and references of the
slice of the code appended to the builder; cell_ov if they do not fit. -/
@[vm_spec] theorem stSliceConst (st : VmState) (s : Stack) (b : Builder) (sl : Slice)
    (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.stSliceConst sl)) st =
      if b.canExtendBy sl.toCellRemaining.bits.size sl.toCellRemaining.refs.size then
        (.ok (), { st with stack := s.push (.builder { bits := b.bits ++ sl.toCellRemaining.bits,
                                                       refs := b.refs ++ sl.toCellRemaining.refs }) })
      else (.error .cellOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `STREFCONST` (C++ `exec_store_const_ref`, one reference) on the stack `s b`: the reference of
the code appended to the builder; cell_ov if it has four. -/
@[vm_spec] theorem stRefConst (st : VmState) (s : Stack) (b : Builder) (c : Cell)
    (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellExt (.stRefConst c))) st =
      if b.canExtendBy 0 1 then (.ok (), { st with stack := s.push (.builder { b with refs := b.refs.push c }) })
      else (.error .cellOv, { st with stack := s }) := by
  cases h : b.canExtendBy 0 1 <;> vm_simp [hs, h]

/-- `STREF2CONST` (C++ `exec_store_const_ref`, two references) on the stack `s b`: the two
references of the code appended to the builder; cell_ov if they do not fit. -/
@[vm_spec] theorem stRef2Const (st : VmState) (s : Stack) (b : Builder) (c1 c2 : Cell)
    (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellExt (.stRef2Const c1 c2))) st =
      if b.canExtendBy 0 2 then
        (.ok (), { st with stack := s.push (.builder { b with refs := (b.refs.push c1).push c2 }) })
      else (.error .cellOv, { st with stack := s }) := by
  cases h : b.canExtendBy 0 2 <;> vm_simp [hs, h]

/-- `BTOS` (C++ `exec_builder_to_slice`) on the stack `s b`: the builder finished (not charged;
cell_ov above the maximal depth), its slice pushed. -/
@[vm_spec] theorem btos (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellExt .btos)) st =
      if Cell.refsDepthOk b.refs then (.ok (), { st with stack := s.push (.slice (Slice.ofCell b.finalize)) })
      else (.error .cellOv, { st with stack := s }) := by
  cases h : Cell.refsDepthOk b.refs <;> vm_simp [hs, h]

/-- `BBITREFS` (C++ `exec_2int_builder_func`) on the stack `s b`: its bits and references. -/
@[vm_spec] theorem bbitrefs (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellOp .bbitrefs)) st =
      (.ok (), { st with stack := (s.push (.int (.num (Int.ofNat b.bits.size)))).push
                                    (.int (.num (Int.ofNat b.refs.size))) }) := by
  vm_simp [hs]

/-- `BREMREFS` (C++ `exec_int_builder_func`) on the stack `s b`: the references left. -/
@[vm_spec] theorem bremrefs (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellOp .bremrefs)) st =
      (.ok (), { st with stack := s.push (.int (.num (Int.ofNat (4 - b.refs.size)))) }) := by
  vm_simp [hs]

/-- `BREMBITREFS` (C++ `exec_2int_builder_func`) on the stack `s b`: the bits and references left. -/
@[vm_spec] theorem brembitrefs (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellOp .brembitrefs)) st =
      (.ok (), { st with stack := (s.push (.int (.num (Int.ofNat (1023 - b.bits.size))))).push
                                    (.int (.num (Int.ofNat (4 - b.refs.size)))) }) := by
  vm_simp [hs]

/-- `BCHKBITS k` (`q` false), `BCHKBITSQ k` (`q` true) (C++ `exec_builder_chk_bits`) on the stack
`s b`: whether `k` more bits fit, cell_ov if not, or a flag. -/
@[vm_spec] theorem bchkBitsImm (st : VmState) (s : Stack) (b : Builder) (k : Nat) (q : Bool)
    (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellOp (.bchkBitsImm k q))) st =
      if q then (.ok (), { st with stack := s.push (.int (.num (if b.canExtendBy k then -1 else 0))) })
      else if b.canExtendBy k then (.ok (), { st with stack := s })
      else (.error .cellOv, { st with stack := s }) := by
  cases q <;> cases h : b.canExtendBy k <;> vm_simp [hs, h]

/-- `SDFIRST` (C++ `exec_un_cs_cmp`) on the stack `s sl`: -1 if the slice begins with a one bit,
else 0. -/
@[vm_spec] theorem sdFirst (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cellOp .sdFirst)) st =
      (.ok (), { st with stack := s.push (.int (.num (if sl.haveBits 1 && sl.cell.bits[sl.bitPos]! then -1 else 0))) }) := by
  vm_simp [hs]

/-- `LDZEROES` (C++ `exec_load_same`, 0) on the stack `s sl`: the number of leading zeroes and the
slice without them. -/
@[vm_spec] theorem ldZeroes (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cellOp .ldZeroes)) st =
      (.ok (), { st with
        stack := (s.push (.int (.num (Int.ofNat (sl.countLeading false))))).push
          (.slice (if sl.countLeading false > 0 then sl.advanceBits (sl.countLeading false) else sl)) }) := by
  vm_simp [hs]

/-- `LDONES` (C++ `exec_load_same`, 1) on the stack `s sl`: the number of leading ones and the slice
without them. -/
@[vm_spec] theorem ldOnes (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cellOp .ldOnes)) st =
      (.ok (), { st with
        stack := (s.push (.int (.num (Int.ofNat (sl.countLeading true))))).push
          (.slice (if sl.countLeading true > 0 then sl.advanceBits (sl.countLeading true) else sl)) }) := by
  vm_simp [hs]

/-- `LDSAME` (C++ `exec_load_same`, -1) on the stack `s sl v`: the number of leading bits equal to
the flag `v` (range_chk outside `0..1`) and the slice without them. -/
@[vm_spec] theorem ldSame (st : VmState) (s : Stack) (sl : Slice) (v : Int)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num v))) :
    ExceptT.run (execInstr (.cellOp .ldSame)) st =
      if 0 ≤ v ∧ v ≤ 1 then
        (.ok (), { st with
          stack := (s.push (.int (.num (Int.ofNat (sl.countLeading (decide (v.toNat = 1))))))).push
            (.slice (if sl.countLeading (decide (v.toNat = 1)) > 0 then
              sl.advanceBits (sl.countLeading (decide (v.toNat = 1))) else sl)) })
      else (.error .rangeChk, { st with stack := s.push (.slice sl) }) := by
  by_cases hm : 0 ≤ v ∧ v ≤ 1
  · have h1 : ¬ v < 0 := by omega
    have h2 : ¬ v.toNat > 1 := by omega
    rw [if_pos hm]
    vm_simp [hs, h1, h2]
  · rw [if_neg hm]
    by_cases h1 : v < 0
    · vm_simp [hs, h1]
    · have h2 : v.toNat > 1 := by omega
      vm_simp [hs, h1, h2]

/-- `STZEROES` (C++ `exec_store_same`, 0) on the stack `s b n`: `n` zeroes appended (range_chk
outside `0..1023`, cell_ov if they do not fit). -/
@[vm_spec] theorem stZeroes (st : VmState) (s : Stack) (b : Builder) (n : Int)
    (hs : st.stack = (s.push (.builder b)).push (.int (.num n))) :
    ExceptT.run (execInstr .stZeroes) st =
      if 0 ≤ n ∧ n ≤ 1023 then
        if b.canExtendBy n.toNat then
          (.ok (), { st with stack := s.push (.builder (b.storeBits (Array.replicate n.toNat false))) })
        else (.error .cellOv, { st with stack := s })
      else (.error .rangeChk, { st with stack := s.push (.builder b) }) := by
  by_cases hm : 0 ≤ n ∧ n ≤ 1023
  · have h1 : ¬ n < 0 := by omega
    have h2 : ¬ n.toNat > 1023 := by omega
    rw [if_pos hm]
    vm_simp [hs, h1, h2]
  · rw [if_neg hm]
    by_cases h1 : n < 0
    · vm_simp [hs, h1]
    · have h2 : n.toNat > 1023 := by omega
      vm_simp [hs, h1, h2]

/-- `STONES` (C++ `exec_store_same`, 1) on the stack `s b n`: `n` ones appended (range_chk outside
`0..1023`, cell_ov if they do not fit). -/
@[vm_spec] theorem stOnes (st : VmState) (s : Stack) (b : Builder) (n : Int)
    (hs : st.stack = (s.push (.builder b)).push (.int (.num n))) :
    ExceptT.run (execInstr .stOnes) st =
      if 0 ≤ n ∧ n ≤ 1023 then
        if b.canExtendBy n.toNat then
          (.ok (), { st with stack := s.push (.builder (b.storeBits (Array.replicate n.toNat true))) })
        else (.error .cellOv, { st with stack := s })
      else (.error .rangeChk, { st with stack := s.push (.builder b) }) := by
  by_cases hm : 0 ≤ n ∧ n ≤ 1023
  · have h1 : ¬ n < 0 := by omega
    have h2 : ¬ n.toNat > 1023 := by omega
    rw [if_pos hm]
    vm_simp [hs, h1, h2]
  · rw [if_neg hm]
    by_cases h1 : n < 0
    · vm_simp [hs, h1]
    · have h2 : n.toNat > 1023 := by omega
      vm_simp [hs, h1, h2]

/-- `STSAME` (C++ `exec_store_same`, -1) on the stack `s b n v`: `n` bits equal to the flag `v`
appended (range_chk outside `0..1`, `0..1023`; cell_ov if they do not fit). -/
@[vm_spec] theorem stSame (st : VmState) (s : Stack) (b : Builder) (n v : Int)
    (hs : st.stack = ((s.push (.builder b)).push (.int (.num n))).push (.int (.num v))) :
    ExceptT.run (execInstr .stSame) st =
      if 0 ≤ v ∧ v ≤ 1 then
        if 0 ≤ n ∧ n ≤ 1023 then
          if b.canExtendBy n.toNat then
            (.ok (), { st with stack := s.push (.builder (b.storeBits (Array.replicate n.toNat (v.toNat == 1)))) })
          else (.error .cellOv, { st with stack := s })
        else (.error .rangeChk, { st with stack := s.push (.builder b) })
      else (.error .rangeChk, { st with stack := (s.push (.builder b)).push (.int (.num n)) }) := by
  by_cases hv : 0 ≤ v ∧ v ≤ 1
  · have g1 : ¬ v < 0 := by omega
    have g2 : ¬ v.toNat > 1 := by omega
    rw [if_pos hv]
    by_cases hm : 0 ≤ n ∧ n ≤ 1023
    · have h1 : ¬ n < 0 := by omega
      have h2 : ¬ n.toNat > 1023 := by omega
      rw [if_pos hm]
      vm_simp [hs, g1, g2, h1, h2]
    · rw [if_neg hm]
      by_cases h1 : n < 0
      · vm_simp [hs, g1, g2, h1]
      · have h2 : n.toNat > 1023 := by omega
        vm_simp [hs, g1, g2, h1, h2]
  · rw [if_neg hv]
    by_cases g1 : v < 0
    · vm_simp [hs, g1]
    · have g2 : v.toNat > 1 := by omega
      vm_simp [hs, g1, g2]

end TvmLean.Spec

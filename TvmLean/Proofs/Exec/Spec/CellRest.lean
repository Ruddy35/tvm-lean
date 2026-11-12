import TvmLean.Proofs.Exec.Eval
import TvmLean.Proofs.Exec.Spec.Cell

/-!
# Specifications: substrings and splits of slices, references by index, levels, hashes and depths
by level, `PLDUZ`, `ENDCST`, `ENDXC`, `SDLEXCMP`

In the format of `Proofs/Exec/Spec/Stack.lean`, on any slice, builder or cell. A count taken from
the stack is an integer, range_chk if it is negative or above the limit of the instruction (C++
`pop_smallint_range`), the count popped.

* `SDSUBSTR` (C++ `exec_slice_op_args2`, cellops.cpp): `n` bits of the slice from offset `o`, a new
  slice; cell_und if the slice is shorter;
* `SPLIT`, `SPLITQ` (C++ `exec_split`): the first `n` bits and `r` references of the slice
  (`Slice.prefixCell`), then the rest; cell_und, or (quiet) the slice back and 0;
* `PLDREFVAR` (C++ `exec_preload_ref`): the reference `i` of the slice;
* `CLEVEL`, `CLEVELMASK` (C++ `exec_cell_level`, `exec_cell_level_mask`);
* `CHASHI i`, `CDEPTHI i`, `CHASHIX`, `CDEPTHIX` (C++ `exec_cell_hash_i`, `exec_cell_depth_i`):
  the hash and the depth of the cell at level `i`, from its level information
  (`Cell.computeLevelInfo?`, cell_und if the cell has none);
* `PLDUZ c` (C++ `exec_preload_uint_fixed_0e`): the first `32 (c + 1)` bits of the slice as an
  unsigned integer, the bits past its end zeroes, the slice kept;
* `ENDCST` (C++ `exec_store_builder_as_ref_rev`, not quiet, as `STBREFR`): `STBREFR` (`stbRef_rev`);
* `ENDXC` (C++ `exec_builder_to_special_cell`): the creation charged, then the builder finished as
  an ordinary or (a flag not 0) exotic cell (`Builder.finalizeCopy`);
* `SDLEXCMP` (C++ `exec_ibin_cs_cmp`, `CellSlice::lex_cmp`): the lexicographic comparison of the
  bits of two slices (`Spec.lexCmpBits`, the comparison of the handler).
-/

namespace TvmLean.Spec

/-- `SDSUBSTR` on the stack `s sl o n`: `n` bits of the slice from offset `o` as a new slice without
references. -/
@[vm_spec] theorem sdSubstr (st : VmState) (s : Stack) (sl : Slice) (o n : Int)
    (hs : st.stack = ((s.push (.slice sl)).push (.int (.num o))).push (.int (.num n))) :
    ExceptT.run (execInstr (.cellOp .sdSubstr)) st =
      if n < 0 then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num o)) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num o)) })
      else if o < 0 then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if 1023 < o.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if sl.haveBits (o.toNat + n.toNat) then
        (.ok (), { st with stack := s.push (.slice (Slice.ofCell (Cell.mkOrdinary
          (sl.cell.bits.extract (sl.bitPos + o.toNat) (sl.bitPos + o.toNat + n.toNat)) #[]))) })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

set_option maxHeartbeats 4000000 in
/-- `SPLIT` (`q` false), `SPLITQ` (`q` true) on the stack `s sl n r`: the first `n` bits and `r`
references of the slice as a new slice, then the rest, then -1 if quiet; if the slice is shorter,
cell_und, or (quiet) the slice back and 0. -/
@[vm_spec] theorem splitSlice (st : VmState) (s : Stack) (sl : Slice) (n r : Int) (q : Bool)
    (hs : st.stack = ((s.push (.slice sl)).push (.int (.num n))).push (.int (.num r))) :
    ExceptT.run (execInstr (.cellOp (.split q))) st =
      if r < 0 then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num n)) })
      else if 4 < r.toNat then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num n)) })
      else if n < 0 then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if ¬sl.haveBits n.toNat = true ∨ ¬sl.haveRefs r.toNat = true then
        if q then (.ok (), { st with stack := (s.push (.slice sl)).push (.int (.num 0)) })
        else (.error .cellUnd, { st with stack := s })
      else
        let rest : Slice := { sl with bitPos := sl.bitPos + n.toNat, refPos := sl.refPos + r.toNat }
        let s1 := (s.push (.slice (Slice.ofCell (Slice.prefixCell sl rest)))).push (.slice rest)
        (.ok (), { st with stack := if q then s1.push (.int (.num (-1))) else s1 }) := by
  cases q <;> vm_simp [hs]

/-- `PLDREFVAR` on the stack `s sl i`: the reference `i` of the slice; cell_und if it has fewer. -/
@[vm_spec] theorem pldRefVar (st : VmState) (s : Stack) (sl : Slice) (i : Int)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num i))) :
    ExceptT.run (execInstr (.cellOp .pldRefVar)) st =
      if i < 0 then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if 3 < i.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if sl.haveRefs (i.toNat + 1) then
        (.ok (), { st with stack := s.push (.cell sl.cell.refs[sl.refPos + i.toNat]!) })
      else (.error .cellUnd, { st with stack := s }) := by
  by_cases h1 : i < 0
  · vm_simp [hs, h1]
  · by_cases h2 : 3 < i.toNat
    · vm_simp [hs, h1, h2]
    · by_cases h : sl.haveRefs (i.toNat + 1) = true
      · have h3 : sl.refPos + i.toNat < sl.cell.refs.size := by
          simp [Slice.haveRefs] at h; omega
        vm_simp [hs, h1, h2, h, h3]
      · vm_simp [hs, h1, h2, h]

/-- `CLEVEL` on the stack `s c`: the level of the cell. -/
@[vm_spec] theorem clevel (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr (.cellOp .clevel)) st =
      (.ok (), { st with stack := s.push (.int (.num (LevelMask.getLevel c.levelMask : Nat))) }) := by
  vm_simp [hs]

/-- `CLEVELMASK` on the stack `s c`: the level mask of the cell. -/
@[vm_spec] theorem clevelMask (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr (.cellOp .clevelMask)) st =
      (.ok (), { st with stack := s.push (.int (.num (c.levelMask : Nat))) }) := by
  vm_simp [hs]

/-- `CDEPTHI i` on the stack `s c`: the depth of the cell at level `i`. -/
@[vm_spec] theorem cdepthI (st : VmState) (s : Stack) (c : Cell) (i : Nat) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr (.cellOp (.cdepthI i))) st =
      match c.computeLevelInfo? with
      | .ok info => (.ok (), { st with stack := s.push (.int (.num (info.getDepth i : Nat))) })
      | .error _ => (.error .cellUnd, { st with stack := s }) := by
  cases h : c.computeLevelInfo? <;> vm_simp [hs, h]

/-- `CDEPTHIX` on the stack `s c i`: the depth of the cell at level `i` (range_chk outside `0..3`). -/
@[vm_spec] theorem cdepthIX (st : VmState) (s : Stack) (c : Cell) (i : Int)
    (hs : st.stack = (s.push (.cell c)).push (.int (.num i))) :
    ExceptT.run (execInstr (.cellOp .cdepthIX)) st =
      if i < 0 then (.error .rangeChk, { st with stack := s.push (.cell c) })
      else if 3 < i.toNat then (.error .rangeChk, { st with stack := s.push (.cell c) })
      else match c.computeLevelInfo? with
        | .ok info => (.ok (), { st with stack := s.push (.int (.num (info.getDepth i.toNat : Nat))) })
        | .error _ => (.error .cellUnd, { st with stack := s }) := by
  by_cases h1 : i < 0
  · vm_simp [hs, h1]
  · by_cases h2 : 3 < i.toNat
    · vm_simp [hs, h1, h2]
    · cases h : c.computeLevelInfo? <;> vm_simp [hs, h1, h2, h]

/-- `CHASHI i` on the stack `s c`: the hash of the cell at level `i`. -/
@[vm_spec] theorem chashI (st : VmState) (s : Stack) (c : Cell) (i : Nat) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr (.cellOp (.chashI i))) st =
      match c.computeLevelInfo? with
      | .ok info =>
          if bytesToNatBE (info.getHash i) < 2 ^ 256 then
            (.ok (), { st with stack := s.push (.int (.num (bytesToNatBE (info.getHash i) : Nat))) })
          else (.error .intOv, { st with stack := s })
      | .error _ => (.error .cellUnd, { st with stack := s }) := by
  cases h : c.computeLevelInfo? with
  | error e => vm_simp [hs, h]
  | ok info =>
    vm_simp [hs, h]
    generalize bytesToNatBE (info.getHash i) = x
    by_cases hx : x < 2 ^ 256
    · rw [if_pos (by omega), if_pos hx]
    · rw [if_neg (by omega), if_neg hx]

/-- `CHASHIX` on the stack `s c i`: the hash of the cell at level `i` (range_chk outside `0..3`). -/
@[vm_spec] theorem chashIX (st : VmState) (s : Stack) (c : Cell) (i : Int)
    (hs : st.stack = (s.push (.cell c)).push (.int (.num i))) :
    ExceptT.run (execInstr (.cellOp .chashIX)) st =
      if i < 0 then (.error .rangeChk, { st with stack := s.push (.cell c) })
      else if 3 < i.toNat then (.error .rangeChk, { st with stack := s.push (.cell c) })
      else match c.computeLevelInfo? with
        | .ok info =>
            if bytesToNatBE (info.getHash i.toNat) < 2 ^ 256 then
              (.ok (), { st with stack := s.push (.int (.num (bytesToNatBE (info.getHash i.toNat) : Nat))) })
            else (.error .intOv, { st with stack := s })
        | .error _ => (.error .cellUnd, { st with stack := s }) := by
  by_cases h1 : i < 0
  · vm_simp [hs, h1]
  · by_cases h2 : 3 < i.toNat
    · vm_simp [hs, h1, h2]
    · cases h : c.computeLevelInfo? with
      | error e => vm_simp [hs, h1, h2, h]
      | ok info =>
        vm_simp [hs, h1, h2, h]
        generalize bytesToNatBE (info.getHash i.toNat) = x
        by_cases hx : x < 2 ^ 256
        · rw [if_pos (by omega), if_pos hx]
        · rw [if_neg (by omega), if_neg hx]

/-- `PLDUZ c` on the stack `s sl`: the slice kept, then its first `32 (c + 1)` bits as an unsigned
integer, the bits past its end zeroes. -/
@[vm_spec] theorem plduz (st : VmState) (s : Stack) (sl : Slice) (c : Nat) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cellExt (.plduz c))) st =
      (.ok (), { st with stack := (s.push (.slice sl)).push (.int (.num
        (bitsToNat (sl.readBits (min (32 * (c + 1)) sl.bitsRemaining)) <<<
          (32 * (c + 1) - min (32 * (c + 1)) sl.bitsRemaining) : Nat))) }) := by
  vm_simp [hs]

/-- `ENDCST` is `STBREFR` (C++ registers it as `exec_store_builder_as_ref_rev`, not quiet). -/
@[vm_spec] theorem endcst (st : VmState) :
    ExceptT.run (execInstr .endcst) st = ExceptT.run (execInstr (.stbRef true false)) st := by
  (simp only [TvmLean.Exec.reduceExecInstrRun]) <;> rfl

/-- `ENDXC` on the stack `s b x`: the creation charged (out of gas at once), then the builder
finished as a cell, exotic if `x ≠ 0` (`Builder.finalizeCopy`, its error otherwise). -/
@[vm_spec] theorem endxc (st : VmState) (s : Stack) (b : Builder) (x : Int)
    (hs : st.stack = (s.push (.builder b)).push (.int (.num x))) :
    ExceptT.run (execInstr (.cellOp .endxc)) st =
      if ({ st with stack := s, gas := st.gas.consume cellCreateGasPrice } : VmState).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s, gas := st.gas.consume cellCreateGasPrice })
      else match b.finalizeCopy (decide (x ≠ 0)) with
        | .ok c => (.ok (), { st with stack := s.push (.cell c), gas := st.gas.consume cellCreateGasPrice })
        | .error e => (.error e, { st with stack := s, gas := st.gas.consume cellCreateGasPrice }) := by
  by_cases hx : x = 0
  · have e : decide (x ≠ 0) = false := by simp [hx]
    rw [e]
    cases h : b.finalizeCopy false <;> vm_simp [hs, hx, h, VmState.consumeGas]
  · have e : decide (x ≠ 0) = true := by simp [hx]
    rw [e]
    cases h : b.finalizeCopy true <;> vm_simp [hs, hx, h, VmState.consumeGas]

/-- The comparison of two bit strings of `SDLEXCMP` (the function of its handler): at the first bit
where they differ, -1 or 1; else by their lengths. -/
def lexCmpBits (b1 b2 : BitString) : Int :=
  let len1 := b1.size
  let len2 := b2.size
  let len := min len1 len2
  let cmp? :=
    (List.range len).foldl
      (fun acc idx =>
        match acc with
        | some v => some v
        | none =>
            let bit1 := b1[idx]!
            let bit2 := b2[idx]!
            if bit1 == bit2 then none else some (if bit1 then 1 else -1))
      none
  match cmp? with
  | some v => v
  | none =>
      if len1 == len2 then 0 else if len1 < len2 then -1 else 1

/-- `SDLEXCMP` on the stack `s s1 s2`: the comparison of the bits of `s1` and `s2`. -/
@[vm_spec] theorem sdLexCmp (st : VmState) (s : Stack) (s1 s2 : Slice)
    (hs : st.stack = (s.push (.slice s1)).push (.slice s2)) :
    ExceptT.run (execInstr .sdLexCmp) st =
      (.ok (), { st with stack := s.push (.int (.num
        (lexCmpBits (s1.readBits s1.bitsRemaining) (s2.readBits s2.bitsRemaining)))) }) := by
  vm_simp [hs, lexCmpBits]
  -- the matches of the handler's function and of `lexCmpBits` are different auxiliary functions
  all_goals rfl

end TvmLean.Spec

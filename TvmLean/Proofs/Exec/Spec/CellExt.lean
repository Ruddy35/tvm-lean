import TvmLean.Proofs.Exec.Eval
import TvmLean.Proofs.Exec.Spec.Cell

/-!
# Specifications: the rest of cells, slices and builders

In the format of `Proofs/Exec/Spec/Stack.lean`. A slice or builder is any (`Slice`, `Builder`);
its conditions stay the model's (`Slice.haveBits`, `Builder.canExtendBy`, ...). A width or count
taken from the stack is an integer `n`, range_chk if it is negative or above the limit of the
instruction (C++ `pop_smallint_range`). The flags of an instruction (prefetch, quiet, signed) are
any; the proofs take their cases and decide the conditions on them first (`cell_pre`).

* `SBITS`, `SREFS`, `SBITREFS`, `SEMPTY`, `SDEMPTY`, `SREMPTY`, `SDEQ`, `SDCNTLEAD0`,
  `SDCNTLEAD1`, `SDCNTTRAIL0`, `SDCNTTRAIL1`, `BBITS`, `BREFS`, `BREMBITS`;
* `SCUTFIRST`, `SSKIPFIRST`, `SCUTLAST`, `SSKIPLAST`;
* `LDSLICE`, `PLDSLICE`, `LDSLICEX`, `PLDSLICEX` and their quiet forms, `LDIX`, `LDUX`, `PLDIX`,
  `PLDUX` and their quiet forms;
* `STI`, the long forms `STI`/`STU`/`STIR`/`STUR` and their quiet forms (`twosBits`,
  `intToBitsTwos_eq`), `STSLICE`, `STSLICER`, `STB`, `STBR`, `STBREF`, `STBREFR` and their quiet
  forms;
* `LDGRAMS`, `LDVARUINT16/32`, `LDVARINT16/32`, `STGRAMS`, `STVARUINT16/32`;
* `LDMSGADDR`, `PARSEMSGADDR` and their quiet forms, given the parse of the address
  (`Slice.skipMessageAddr`, `Slice.parseMessageAddr`).
-/

namespace TvmLean

/-- The `bits`-bit two's complement of `x` (C++ `export_bits` of a signed integer), as the model
makes it (`intToBitsTwos x bits` for an `x` that fits). -/
def twosBits (x : Int) (bits : Nat) : BitString :=
  natToBits (if x ≥ 0 then x.toNat else (1 <<< bits) - (-x).toNat) bits

/-- `intToBitsTwos x bits` for `bits > 0`: `twosBits x bits` if `x` fits `bits` bits signed,
range_chk otherwise. -/
theorem intToBitsTwos_eq (x : Int) (bits : Nat) (hb : 0 < bits) :
    intToBitsTwos x bits =
      if -2 ^ (bits - 1) ≤ x ∧ x < 2 ^ (bits - 1) then .ok (twosBits x bits) else .error .rangeChk := by
  unfold intToBitsTwos
  have hb0 : ¬ bits = 0 := by omega
  simp only [intPow2, hb0, if_false]
  by_cases h : -2 ^ (bits - 1) ≤ x ∧ x < 2 ^ (bits - 1)
  · have h1 : ¬ (x < -2 ^ (bits - 1) ∨ x ≥ 2 ^ (bits - 1)) := by omega
    rw [if_pos h]
    simp only [h1, decide_false, Bool.false_eq_true, if_false]
    by_cases h2 : x ≥ 0
    · simp only [twosBits, h2, if_true]; rfl
    · simp only [twosBits, h2, if_false]; rfl
  · have h1 : x < -2 ^ (bits - 1) ∨ x ≥ 2 ^ (bits - 1) := by omega
    rw [if_neg h]
    simp only [h1, decide_true, if_true]; rfl

namespace Spec

/-- The conditions of the handler on literals (the flags of the instruction, once a case of them)
decided before `vm_simp`, whose contextual `simp` loops on a branch assuming a false literal. -/
local macro "cell_pre" : tactic =>
  `(tactic| try simp only [TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok,
    Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, Bool.or_false,
    Bool.false_or, Bool.or_true, Bool.true_or, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false,
    if_true, reduceIte, Nat.reduceEqDiff, Nat.reduceShiftLeft])

/-! ## Slices and builders: sizes and tests -/

/-- `SBITS` (C++ `exec_slice_bits_refs`, mode 1): the number of bits left in a slice. -/
@[vm_spec] theorem sbits (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .sbits) st = (.ok (), { st with stack := s.push (.int (.num sl.bitsRemaining)) }) := by
  vm_simp [hs]

/-- `SREFS` (C++ `exec_slice_bits_refs`, mode 2): the number of references left. -/
@[vm_spec] theorem srefs (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .srefs) st = (.ok (), { st with stack := s.push (.int (.num sl.refsRemaining)) }) := by
  vm_simp [hs]

/-- `SBITREFS` (C++ `exec_slice_bits_refs`, mode 3): both. -/
@[vm_spec] theorem sbitrefs (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .sbitrefs) st =
      (.ok (), { st with stack := (s.push (.int (.num sl.bitsRemaining))).push (.int (.num sl.refsRemaining)) }) := by
  vm_simp [hs]

/-- `SEMPTY` (C++ `exec_un_cs_cmp`): -1 if no bits and no references are left, else 0. -/
@[vm_spec] theorem sempty (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .sempty) st =
      (.ok (), { st with stack := s.push (.int (.num (if sl.bitsRemaining = 0 ∧ sl.refsRemaining = 0 then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDEMPTY` (C++ `exec_un_cs_cmp`): -1 if no bits are left. -/
@[vm_spec] theorem sdempty (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .sdempty) st =
      (.ok (), { st with stack := s.push (.int (.num (if sl.bitsRemaining = 0 then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SREMPTY` (C++ `exec_un_cs_cmp`): -1 if no references are left. -/
@[vm_spec] theorem srempty (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .srempty) st =
      (.ok (), { st with stack := s.push (.int (.num (if sl.refsRemaining = 0 then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDEQ` (C++ `exec_bin_cs_cmp`, `lex_cmp` = 0): -1 if the bits left in the two slices are the
same (the references are not compared). -/
@[vm_spec] theorem sdEq (st : VmState) (s : Stack) (sl1 sl2 : Slice)
    (hs : st.stack = (s.push (.slice sl1)).push (.slice sl2)) :
    ExceptT.run (execInstr .sdEq) st =
      (.ok (), { st with stack := s.push (.int (.num
        (if sl1.readBits sl1.bitsRemaining = sl2.readBits sl2.bitsRemaining then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SDCNTLEAD0` (C++ `exec_iun_cs_cmp`, `count_leading(0)`): the number of leading zeros of the
bits left. -/
@[vm_spec] theorem sdCntLead0 (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .sdCntLead0) st =
      (.ok (), { st with stack := s.push (.int (.num (sl.countLeading false))) }) := by
  vm_simp [hs, Slice.countLeading, Slice.bitsRemaining]

/-- `SDCNTLEAD1` (C++ `exec_iun_cs_cmp`, `count_leading(1)`): the number of leading ones. -/
@[vm_spec] theorem sdCntLead1 (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cellOp .sdCntLead1)) st =
      (.ok (), { st with stack := s.push (.int (.num (sl.countLeading true))) }) := by
  vm_simp [hs, Slice.countLeading, Slice.bitsRemaining]

/-- `SDCNTTRAIL0` (C++ `exec_iun_cs_cmp`, `count_trailing(0)`): the number of trailing zeros. -/
@[vm_spec] theorem sdCntTrail0 (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr .sdCntTrail0) st =
      (.ok (), { st with stack := s.push (.int (.num
        (countWhile sl.bitsRemaining (fun c => sl.cell.bits[sl.cell.bits.size - 1 - c]! == false) 0))) }) := by
  vm_simp [hs]

/-- `SDCNTTRAIL1` (C++ `exec_iun_cs_cmp`, `count_trailing(1)`): the number of trailing ones of the
bits left. -/
@[vm_spec] theorem sdCntTrail1 (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cellOp .sdCntTrail1)) st =
      (.ok (), { st with stack := s.push (.int (.num (if sl.bitsRemaining = 0 then 0 else
        countWhile sl.bitsRemaining (fun c => sl.cell.bits[sl.bitPos + sl.bitsRemaining - 1 - c]! == true) 0))) }) := by
  vm_simp [hs]
  split <;> rfl

/-- `BBITS` (C++ `exec_int_builder_func`): the number of bits of a builder. -/
@[vm_spec] theorem bbits (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr .bbits) st = (.ok (), { st with stack := s.push (.int (.num b.bits.size)) }) := by
  vm_simp [hs]

/-- `BREFS` (C++ `exec_int_builder_func`): the number of references of a builder. -/
@[vm_spec] theorem brefs (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellOp .brefs)) st = (.ok (), { st with stack := s.push (.int (.num b.refs.size)) }) := by
  vm_simp [hs]

/-- `BREMBITS` (C++ `exec_int_builder_func`): the number of bits a builder can still
take. -/
@[vm_spec] theorem brembits (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellOp .brembits)) st =
      (.ok (), { st with stack := s.push (.int (.num (1023 - b.bits.size : Nat))) }) := by
  vm_simp [hs]

/-! ## Cutting slices -/

/-- `SCUTFIRST` (C++ `exec_slice_op_args2`): the first `b` bits and `r` references
of a slice, as a new slice; `b ≤ 1023`, `r ≤ 4` (range_chk), cell_und if the slice is shorter. -/
@[vm_spec] theorem scutfirst (st : VmState) (s : Stack) (sl : Slice) (b r : Int)
    (hs : st.stack = ((s.push (.slice sl)).push (.int (.num b))).push (.int (.num r))) :
    ExceptT.run (execInstr (.cellOp .scutfirst)) st =
      if r < 0 then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num b)) })
      else if 4 < r.toNat then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num b)) })
      else if b < 0 then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if 1023 < b.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if sl.haveBits b.toNat ∧ sl.haveRefs r.toNat then
        (.ok (), { st with stack := s.push (.slice (Slice.ofCell (Cell.mkOrdinary
          (sl.cell.bits.extract sl.bitPos (sl.bitPos + b.toNat)) (sl.cell.refs.extract sl.refPos (sl.refPos + r.toNat))))) })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

/-- `SSKIPFIRST` (C++ `exec_slice_op_args2`): the slice without its first `b` bits
and `r` references. -/
@[vm_spec] theorem sskipfirst (st : VmState) (s : Stack) (sl : Slice) (b r : Int)
    (hs : st.stack = ((s.push (.slice sl)).push (.int (.num b))).push (.int (.num r))) :
    ExceptT.run (execInstr (.cellOp .sskipfirst)) st =
      if r < 0 then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num b)) })
      else if 4 < r.toNat then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num b)) })
      else if b < 0 then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if 1023 < b.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if sl.haveBits b.toNat ∧ sl.haveRefs r.toNat then
        (.ok (), { st with stack := s.push (.slice { sl with bitPos := sl.bitPos + b.toNat, refPos := sl.refPos + r.toNat }) })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

/-- `SCUTLAST` (C++ `exec_slice_op_args2`): the last `b` bits and `r` references of
a slice, as a new slice. -/
@[vm_spec] theorem scutlast (st : VmState) (s : Stack) (sl : Slice) (b r : Int)
    (hs : st.stack = ((s.push (.slice sl)).push (.int (.num b))).push (.int (.num r))) :
    ExceptT.run (execInstr (.cellOp .scutlast)) st =
      if r < 0 then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num b)) })
      else if 4 < r.toNat then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num b)) })
      else if b < 0 then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if 1023 < b.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if b.toNat ≤ sl.bitsRemaining ∧ r.toNat ≤ sl.refsRemaining then
        (.ok (), { st with stack := s.push (.slice (Slice.ofCell (Cell.mkOrdinary
          (sl.cell.bits.extract (sl.bitPos + (sl.bitsRemaining - b.toNat)) sl.cell.bits.size)
          (sl.cell.refs.extract (sl.refPos + (sl.refsRemaining - r.toNat)) sl.cell.refs.size)))) })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

/-- `SSKIPLAST` (C++ `exec_slice_op_args2`): the slice without its last `b` bits
and `r` references, as a new slice. -/
@[vm_spec] theorem sskiplast (st : VmState) (s : Stack) (sl : Slice) (b r : Int)
    (hs : st.stack = ((s.push (.slice sl)).push (.int (.num b))).push (.int (.num r))) :
    ExceptT.run (execInstr (.cellOp .sskiplast)) st =
      if r < 0 then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num b)) })
      else if 4 < r.toNat then (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num b)) })
      else if b < 0 then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if 1023 < b.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if b.toNat ≤ sl.bitsRemaining ∧ r.toNat ≤ sl.refsRemaining then
        (.ok (), { st with stack := s.push (.slice (Slice.ofCell (Cell.mkOrdinary
          (sl.cell.bits.extract sl.bitPos (sl.bitPos + (sl.bitsRemaining - b.toNat)))
          (sl.cell.refs.extract sl.refPos (sl.refPos + (sl.refsRemaining - r.toNat)))))) })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs]

/-! ## Loading from slices -/

/-- `LDSLICE b`, `PLDSLICE b` and their quiet forms (C++ `exec_load_slice_fixed`,
`exec_load_slice_fixed2`): the first `b` bits of the slice as a new slice, then (unless prefetching) the rest, then (if quiet) -1; if the
slice is shorter, cell_und, or (quiet) the slice back (unless prefetching) and 0. -/
@[vm_spec] theorem loadSliceFixed (st : VmState) (s : Stack) (sl : Slice) (prefetch quiet : Bool) (b : Nat)
    (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.loadSliceFixed prefetch quiet b)) st =
      if sl.haveBits b then
        let s1 := s.push (.slice (Slice.ofCell (Cell.mkOrdinary (sl.readBits b) #[])))
        let s2 := if prefetch then s1 else s1.push (.slice (sl.advanceBits b))
        (.ok (), { st with stack := if quiet then s2.push (.int (.num (-1))) else s2 })
      else if quiet then
        (.ok (), { st with stack := (if prefetch then s else s.push (.slice sl)).push (.int (.num 0)) })
      else (.error .cellUnd, { st with stack := s }) := by
  cases prefetch <;> cases quiet <;> cell_pre <;> vm_simp [hs]

/-- `LDSLICEX`, `PLDSLICEX` and their quiet forms (C++ `exec_load_slice`): as `loadSliceFixed`,
the width `n` on top, `0 ≤ n ≤ 1023` (range_chk). -/
@[vm_spec] theorem loadSliceX (st : VmState) (s : Stack) (sl : Slice) (prefetch quiet : Bool) (n : Int)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num n))) :
    ExceptT.run (execInstr (.loadSliceX prefetch quiet)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if sl.haveBits n.toNat then
        let s1 := s.push (.slice (Slice.ofCell (Cell.mkOrdinary (sl.readBits n.toNat) #[])))
        let s2 := if prefetch then s1 else s1.push (.slice (sl.advanceBits n.toNat))
        (.ok (), { st with stack := if quiet then s2.push (.int (.num (-1))) else s2 })
      else if quiet then
        (.ok (), { st with stack := (if prefetch then s else s.push (.slice sl)).push (.int (.num 0)) })
      else (.error .cellUnd, { st with stack := s }) := by
  cases prefetch <;> cases quiet <;> cell_pre <;> vm_simp [hs]

set_option maxHeartbeats 2000000 in
/-- `LDIX`, `LDUX`, `PLDIX`, `PLDUX` and their quiet forms (C++ `exec_load_int_var`): the width
`n` on top, `0 ≤ n ≤ 257` (256 unsigned; range_chk); the first `n` bits of the slice as an integer
(signed: `bitsToIntSignedTwos`), then the rest unless prefetching, then -1 if quiet; if the slice
is shorter, cell_und, or (quiet) the slice back and 0. -/
@[vm_spec] theorem loadIntVar (st : VmState) (s : Stack) (sl : Slice) (unsigned prefetch quiet : Bool) (n : Int)
    (hs : st.stack = (s.push (.slice sl)).push (.int (.num n))) :
    ExceptT.run (execInstr (.loadIntVar unsigned prefetch quiet)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if (if unsigned then 256 else 257) < n.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else if sl.haveBits n.toNat then
        let x : Int := if unsigned then bitsToNat (sl.readBits n.toNat) else bitsToIntSignedTwos (sl.readBits n.toNat)
        if -2 ^ 256 ≤ x ∧ x < 2 ^ 256 then
          let s1 := s.push (.int (.num x))
          let s2 := if prefetch then s1 else s1.push (.slice (sl.advanceBits n.toNat))
          (.ok (), { st with stack := if quiet then s2.push (.int (.num (-1))) else s2 })
        else (.error .intOv, { st with stack := s })
      else if quiet then
        (.ok (), { st with stack := (if prefetch then s else s.push (.slice sl)).push (.int (.num 0)) })
      else (.error .cellUnd, { st with stack := s }) := by
  cases unsigned <;> cases prefetch <;> cases quiet <;> cell_pre <;> vm_simp [hs]

/-! ## Storing into builders -/

/-- `STI b` (C++ `exec_store_int`, signed, `1 ≤ b ≤ 256`): the integer below the builder is
stored in `b` bits, two's complement; cell_ov if the builder has no room, range_chk if it does not
fit. -/
@[vm_spec] theorem sti (st : VmState) (s : Stack) (x : Int) (b : Builder) (n : Nat) (hn : 0 < n)
    (hs : st.stack = (s.push (.int (.num x))).push (.builder b)) :
    ExceptT.run (execInstr (.sti n)) st =
      if b.canExtendBy n then
        if -2 ^ (n - 1) ≤ x ∧ x < 2 ^ (n - 1) then
          (.ok (), { st with stack := s.push (.builder (b.storeBits (twosBits x n))) })
        else (.error .rangeChk, { st with stack := s })
      else (.error .cellOv, { st with stack := s }) := by
  have hn' : (n == 0) = false := by simp; omega
  by_cases hx : -2 ^ (n - 1) ≤ x ∧ x < 2 ^ (n - 1) <;> vm_simp [hs, hn', intToBitsTwos_eq x n hn, hx]

/-- `STI b`, `STU b` in their long forms, quiet or not (C++ `exec_store_int_fixed`, `1 ≤ b ≤
256`): the integer below the builder stored in `b` bits (unsigned: `natToBits`, signed:
`twosBits`), then 0 if quiet; if the builder has no room, cell_ov, or (quiet) both back and -1; if
the integer does not fit, range_chk, or (quiet) both back and 1. -/
@[vm_spec] theorem stIntFixed (st : VmState) (s : Stack) (x : Int) (b : Builder) (unsigned quiet : Bool) (n : Nat)
    (hn : 0 < n) (hs : st.stack = (s.push (.int (.num x))).push (.builder b)) :
    ExceptT.run (execInstr (.stIntFixed unsigned false quiet n)) st =
      if b.canExtendBy n then
        if (if unsigned then 0 ≤ x ∧ x < 2 ^ n else -2 ^ (n - 1) ≤ x ∧ x < 2 ^ (n - 1)) then
          let s1 := s.push (.builder (b.storeBits (if unsigned then natToBits x.toNat n else twosBits x n)))
          (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1 })
        else if quiet then
          (.ok (), { st with stack := ((s.push (.int (.num x))).push (.builder b)).push (.int (.num 1)) })
        else (.error .rangeChk, { st with stack := s })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.int (.num x))).push (.builder b)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  have hn0 : ¬ n = 0 := by omega
  have hn' : (n == 0) = false := by simp; omega
  cases unsigned <;> cases quiet <;> cell_pre <;>
    vm_simp [hs, hn0, hn', intSignedFitsBits, intToBitsTwos_eq x n hn]

/-- `STIR b`, `STUR b` and their quiet forms (C++ `exec_store_int_fixed`, reversed): as
`stIntFixed`, the integer on top of the builder. -/
@[vm_spec] theorem stIntFixed_rev (st : VmState) (s : Stack) (x : Int) (b : Builder) (unsigned quiet : Bool) (n : Nat)
    (hn : 0 < n) (hs : st.stack = (s.push (.builder b)).push (.int (.num x))) :
    ExceptT.run (execInstr (.stIntFixed unsigned true quiet n)) st =
      if b.canExtendBy n then
        if (if unsigned then 0 ≤ x ∧ x < 2 ^ n else -2 ^ (n - 1) ≤ x ∧ x < 2 ^ (n - 1)) then
          let s1 := s.push (.builder (b.storeBits (if unsigned then natToBits x.toNat n else twosBits x n)))
          (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1 })
        else if quiet then
          (.ok (), { st with stack := ((s.push (.builder b)).push (.int (.num x))).push (.int (.num 1)) })
        else (.error .rangeChk, { st with stack := s })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.builder b)).push (.int (.num x))).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  have hn0 : ¬ n = 0 := by omega
  have hn' : (n == 0) = false := by simp; omega
  cases unsigned <;> cases quiet <;> cell_pre <;>
    vm_simp [hs, hn0, hn', intSignedFitsBits, intToBitsTwos_eq x n hn]

/-- `STSLICE` and `STSLICEQ` (C++ `exec_store_slice`): the bits and references left in the slice
below the builder are appended to it, then 0 if quiet; if it has no room, cell_ov, or (quiet) both
back and -1. -/
@[vm_spec] theorem stSlice (st : VmState) (s : Stack) (sl : Slice) (b : Builder) (quiet : Bool)
    (hs : st.stack = (s.push (.slice sl)).push (.builder b)) :
    ExceptT.run (execInstr (.stSlice false quiet)) st =
      let c := sl.toCellRemaining
      if b.canExtendBy c.bits.size c.refs.size then
        let s1 := s.push (.builder { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs })
        (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1 })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.slice sl)).push (.builder b)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs]

/-- `STSLICER` and `STSLICERQ` (C++ `exec_store_slice_rev`): as `stSlice`, the slice on top
of the builder. -/
@[vm_spec] theorem stSlice_rev (st : VmState) (s : Stack) (sl : Slice) (b : Builder) (quiet : Bool)
    (hs : st.stack = (s.push (.builder b)).push (.slice sl)) :
    ExceptT.run (execInstr (.stSlice true quiet)) st =
      let c := sl.toCellRemaining
      if b.canExtendBy c.bits.size c.refs.size then
        let s1 := s.push (.builder { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs })
        (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1 })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.builder b)).push (.slice sl)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs]

/-- `STB` and `STBQ` (C++ `exec_store_builder`): the builder `b2` below the builder `b` is
appended to it. -/
@[vm_spec] theorem stb (st : VmState) (s : Stack) (b2 b : Builder) (quiet : Bool)
    (hs : st.stack = (s.push (.builder b2)).push (.builder b)) :
    ExceptT.run (execInstr (.stb false quiet)) st =
      if b.canExtendBy b2.bits.size b2.refs.size then
        let s1 := s.push (.builder { bits := b.bits ++ b2.bits, refs := b.refs ++ b2.refs })
        (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1 })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.builder b2)).push (.builder b)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs]

/-- `STBR` and `STBRQ` (C++ `exec_store_builder_rev`): the builder `b2` on top is appended to the
builder `b` below it. -/
@[vm_spec] theorem stb_rev (st : VmState) (s : Stack) (b b2 : Builder) (quiet : Bool)
    (hs : st.stack = (s.push (.builder b)).push (.builder b2)) :
    ExceptT.run (execInstr (.stb true quiet)) st =
      if b.canExtendBy b2.bits.size b2.refs.size then
        let s1 := s.push (.builder { bits := b.bits ++ b2.bits, refs := b.refs ++ b2.refs })
        (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1 })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.builder b)).push (.builder b2)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs]

/-- `STBREF` and `STBREFQ` (C++ `exec_store_builder_as_ref`): the builder `b2` below the builder
`b` becomes a cell (its creation charged; cell_ov if too deep), the next reference of `b`. -/
@[vm_spec] theorem stbRef (st : VmState) (s : Stack) (b2 b : Builder) (quiet : Bool)
    (hs : st.stack = (s.push (.builder b2)).push (.builder b)) :
    ExceptT.run (execInstr (.stbRef false quiet)) st =
      if b.canExtendBy 0 1 then
        if Cell.refsDepthOk b2.refs then
          let s1 := s.push (.builder { b with refs := b.refs.push b2.finalize })
          (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1,
                             gas := st.gas.consume cellCreateGasPrice })
        else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.builder b2)).push (.builder b)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs, VmState.consumeGas]

/-- `STBREFR` and `STBREFRQ` (C++ `exec_store_builder_as_ref_rev`): as `stbRef`, the builder `b2`
on top. -/
@[vm_spec] theorem stbRef_rev (st : VmState) (s : Stack) (b b2 : Builder) (quiet : Bool)
    (hs : st.stack = (s.push (.builder b)).push (.builder b2)) :
    ExceptT.run (execInstr (.stbRef true quiet)) st =
      if b.canExtendBy 0 1 then
        if Cell.refsDepthOk b2.refs then
          let s1 := s.push (.builder { b with refs := b.refs.push b2.finalize })
          (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1,
                             gas := st.gas.consume cellCreateGasPrice })
        else (.error .cellOv, { st with stack := s, gas := st.gas.consume cellCreateGasPrice })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.builder b)).push (.builder b2)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs, VmState.consumeGas]

/-! ## Variable-length integers and addresses -/

/-- The read of an `n`-bit unsigned length (`Slice.takeBitsAsNatCellUnd`) in the VM: the length
and the rest, or cell_und. -/
theorem run_takeBitsAsNatCellUnd (sl : Slice) (n : Nat) (st : VmState) :
    ExceptT.run (liftM (sl.takeBitsAsNatCellUnd n) : VM (Nat × Slice)) st =
      if sl.haveBits n then (.ok (bitsToNat (sl.readBits n), sl.advanceBits n), st) else (.error .cellUnd, st) := by
  unfold Slice.takeBitsAsNatCellUnd
  split <;> rfl

/-- A bind of `Except` on a value (the parse of an address, then the check of its rest). -/
theorem except_bind_ok {α β : Type} (a : α) (f : α → Except Excno β) : (Except.ok a >>= f) = f a := rfl

/-- A bind of `Except` on an error. -/
theorem except_bind_error {α β : Type} (e : Excno) (f : α → Except Excno β) : (Except.error e >>= f) = .error e := rfl

/-- `pure` of `Except`. -/
theorem except_pure {α : Type} (a : α) : (pure a : Except Excno α) = .ok a := rfl

/-- `LDGRAMS` = `LDVARUINT16` (C++ `exec_load_var_integer`, 4-bit length): a length `l` in 4 bits,
then an `8 l`-bit unsigned integer, then the rest of the slice; cell_und if the slice is shorter. -/
@[vm_spec] theorem ldGrams (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.tonEnvOp .ldGrams)) st =
      let l := bitsToNat (sl.readBits 4)
      let sl1 := sl.advanceBits 4
      let x : Int := bitsToNat (sl1.readBits (l * 8))
      if sl.haveBits 4 then
        if sl1.haveBits (l * 8) then
          if -2 ^ 256 ≤ x ∧ x < 2 ^ 256 then
            (.ok (), { st with stack := (s.push (.int (.num x))).push (.slice (sl1.advanceBits (l * 8))) })
          else (.error .intOv, { st with stack := s })
        else (.error .cellUnd, { st with stack := s })
      else (.error .cellUnd, { st with stack := s }) := by
  vm_simp [hs, run_takeBitsAsNatCellUnd]

/-- `LDVARUINT16`, `LDVARINT16` (`k = 16`, a 4-bit length) and `LDVARUINT32`, `LDVARINT32`
(`k = 32`, 5 bits) (C++ `exec_load_var_integer`): a length `l`, then an `8 l`-bit integer
(signed: `bitsToIntSignedTwos`), then the rest; cell_und if the slice is shorter. -/
@[vm_spec] theorem ldVarInt (st : VmState) (s : Stack) (sl : Slice) (signed : Bool) (k : Nat) (hk : k = 16 ∨ k = 32)
    (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cellExt (.ldVarInt signed k))) st =
      let lb := if k = 16 then 4 else 5
      let l := bitsToNat (sl.readBits lb)
      let sl1 := sl.advanceBits lb
      let bs := sl1.readBits (l * 8)
      if sl.haveBits lb then
        if sl1.haveBits (l * 8) then
          (.ok (), { st with stack := (s.push (.int (.num (if signed then bitsToIntSignedTwos bs else bitsToNat bs)))).push
                                        (.slice (sl1.advanceBits (l * 8))) })
        else (.error .cellUnd, { st with stack := s })
      else (.error .cellUnd, { st with stack := s }) := by
  rcases hk with rfl | rfl <;> cell_pre <;> vm_simp [hs, run_takeBitsAsNatCellUnd]

/-- `STGRAMS` = `STVARUINT16` (C++ `exec_store_var_integer`, 4-bit length, unsigned): `x ≥ 0` in
`l = ⌈bits(x)/8⌉ < 16` bytes, after `l` in 4 bits; range_chk for a negative or too long `x`,
cell_ov if the builder has no room. -/
@[vm_spec] theorem stGrams (st : VmState) (s : Stack) (b : Builder) (x : Int)
    (hs : st.stack = (s.push (.builder b)).push (.int (.num x))) :
    ExceptT.run (execInstr (.tonEnvOp .stGrams)) st =
      let l := (natLenBits x.toNat + 7) / 8
      if x < 0 then (.error .rangeChk, { st with stack := s })
      else if 16 ≤ l then (.error .rangeChk, { st with stack := s })
      else if b.canExtendBy (4 + l * 8) then
        (.ok (), { st with stack := s.push (.builder (b.storeBits (natToBits l 4 ++ natToBits x.toNat (l * 8)))) })
      else (.error .cellOv, { st with stack := s }) := by
  vm_simp [hs]

set_option maxHeartbeats 2000000 in
/-- `STVARUINT16` (`k = 16`) and `STVARUINT32` (`k = 32`) (C++ `exec_store_var_integer`,
unsigned): as `stGrams`, the length in 4 or 5 bits, below 16 or 32. -/
@[vm_spec] theorem stVarUInt (st : VmState) (s : Stack) (b : Builder) (x : Int) (k : Nat) (hk : k = 16 ∨ k = 32)
    (hs : st.stack = (s.push (.builder b)).push (.int (.num x))) :
    ExceptT.run (execInstr (.cellExt (.stVarInt false k))) st =
      let lb := if k = 16 then 4 else 5
      let l := (natLenBits x.toNat + 7) / 8
      if x < 0 then (.error .rangeChk, { st with stack := s })
      else if 2 ^ lb ≤ l then (.error .rangeChk, { st with stack := s })
      else if b.canExtendBy (lb + l * 8) then
        (.ok (), { st with stack := s.push (.builder (b.storeBits (natToBits l lb ++ natToBits x.toNat (l * 8)))) })
      else (.error .cellOv, { st with stack := s }) := by
  rcases hk with rfl | rfl <;> cell_pre <;> vm_simp [hs, Nat.reduceShiftLeft]

/-- `LDMSGADDR`, `LDMSGADDRQ` (C++ `exec_load_message_addr`) when the slice starts with an
address (`Slice.skipMessageAddr` at the global version gives the rest): the address as a slice,
then the rest, then -1 if quiet. -/
@[vm_spec] theorem ldMsgAddr (st : VmState) (s : Stack) (sl rest : Slice) (quiet : Bool)
    (hs : st.stack = s.push (.slice sl)) (h : sl.skipMessageAddr st.globalVersion = .ok rest) :
    ExceptT.run (execInstr (.tonEnvOp (.ldMsgAddr quiet))) st =
      let s1 := (s.push (.slice (Slice.ofCell (sl.prefixCell rest)))).push (.slice rest)
      (.ok (), { st with stack := if quiet then s1.push (.int (.num (-1))) else s1 }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs, h]

/-- `LDMSGADDR`, `LDMSGADDRQ` when the slice does not start with an address: the error, or
(quiet) the slice back and 0. -/
@[vm_spec] theorem ldMsgAddr_error (st : VmState) (s : Stack) (sl : Slice) (e : Excno) (quiet : Bool)
    (hs : st.stack = s.push (.slice sl)) (h : sl.skipMessageAddr st.globalVersion = .error e) :
    ExceptT.run (execInstr (.tonEnvOp (.ldMsgAddr quiet))) st =
      if quiet then (.ok (), { st with stack := (s.push (.slice sl)).push (.int (.num 0)) })
      else (.error e, { st with stack := s }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs, h]

/-- `PARSEMSGADDR`, `PARSEMSGADDRQ` (C++ `exec_parse_message_addr`) when the slice is an address
and nothing more (`Slice.parseMessageAddr` gives its tuple and an empty rest): the tuple, then -1
if quiet. -/
@[vm_spec] theorem parseMsgAddr (st : VmState) (s : Stack) (sl rest : Slice) (t : Array Value) (quiet : Bool)
    (hs : st.stack = s.push (.slice sl)) (h : sl.parseMessageAddr st.globalVersion = .ok (t, rest))
    (hr : rest.bitsRemaining = 0 ∧ rest.refsRemaining = 0) :
    ExceptT.run (execInstr (.tonEnvOp (.parseMsgAddr quiet))) st =
      (.ok (), { st with stack := if quiet then (s.push (.tuple t)).push (.int (.num (-1))) else s.push (.tuple t) }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs, h, hr, except_bind_ok, except_pure, bne_iff_ne, not_true_eq_false, or_false]

/-- `PARSEMSGADDR`, `PARSEMSGADDRQ` when the slice is not an address: the error, or (quiet) 0. -/
@[vm_spec] theorem parseMsgAddr_error (st : VmState) (s : Stack) (sl : Slice) (e : Excno) (quiet : Bool)
    (hs : st.stack = s.push (.slice sl)) (h : sl.parseMessageAddr st.globalVersion = .error e) :
    ExceptT.run (execInstr (.tonEnvOp (.parseMsgAddr quiet))) st =
      if quiet then (.ok (), { st with stack := s.push (.int (.num 0)) })
      else (.error e, { st with stack := s }) := by
  cases quiet <;> cell_pre <;> vm_simp [hs, h, except_bind_error]

end Spec

end TvmLean

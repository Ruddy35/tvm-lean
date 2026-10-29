import TvmLean.Proofs.Exec.Spec.CellExt

/-!
# Specifications: room checks of builders, the depth of a builder, `SUBSLICE`

In the format of `Proofs/Exec/Spec/CellExt.lean` (a builder or slice is any, its conditions the
model's: `Builder.canExtendBy`, `Slice.haveBits`, `Slice.haveRefs`; a count from the stack is an
integer, range_chk if it is negative or above the limit, C++ `pop_smallint_range`):

* `BCHKBITS` (the count on the stack), `BCHKREFS`, `BCHKBITREFS` and their quiet forms (C++
  `exec_builder_chk_bits_refs`, cellops.cpp:738): `bchkBits`, `bchkRefs`, `bchkBitRefs`;
* `BDEPTH` (C++ `exec_int_builder_func`, `CellBuilder::get_depth`, cellops.cpp:844): `bdepth`, the
  maximum of the depths of the references plus one (`Builder.refsDepth`);
* `SUBSLICE` (C++ `exec_subslice`, cellops.cpp:1247): `subslice`.
-/

namespace TvmLean

/-- The depth of a builder (C++ `CellBuilder::get_depth`): the maximum over its references of
their depth plus one, 0 without references. -/
def Builder.refsDepth (b : Builder) : Nat :=
  b.refs.foldl (fun d r => Nat.max d (r.depth + 1)) 0

namespace Spec

/-- The conditions of the handler on the literals of the instruction decided before `vm_simp`
(`cell_pre` of `Spec/CellExt.lean`; the handlers of `CellInstr` are reached by `unfoldModelRun`,
their dispatchers not being `execInstr*`). -/
local macro "cell_check_pre" : tactic =>
  `(tactic| try simp only [TvmLean.Exec.reduceExecInstrRun, TvmLean.Exec.unfoldModelRun, VM.run_bind, VM.run_get,
    VM.bindRes_ok, Nat.reduceBEq, Nat.reduceBNe, Nat.reduceAdd, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and,
    Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    if_false, if_true, reduceIte])

/-- `BCHKBITS` and `BCHKBITSQ` with the number of bits on the stack (C++
`exec_builder_chk_bits_refs`, cellops.cpp:738-751, mode 1 and 5, opcodes `CF39`, `CF3D`): `n`,
`0 ≤ n ≤ 1023` (range_chk), then the builder; whether it can take `n` more bits: if quiet -1 or 0,
else nothing or cell_ov. -/
@[vm_spec] theorem bchkBits (st : VmState) (s : Stack) (b : Builder) (n : Int) (quiet : Bool)
    (hs : st.stack = (s.push (.builder b)).push (.int (.num n))) :
    ExceptT.run (execInstr (.cellOp (.bchk true false quiet))) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.builder b) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.builder b) })
      else if quiet then (.ok (), { st with stack := s.push (.int (.num (if b.canExtendBy n.toNat then -1 else 0))) })
      else if b.canExtendBy n.toNat then (.ok (), { st with stack := s })
      else (.error .cellOv, { st with stack := s }) := by
  cases quiet <;> cell_check_pre <;> vm_simp [hs]

/-- `BCHKREFS` and `BCHKREFSQ` (C++ `exec_builder_chk_bits_refs`, cellops.cpp:738-751, mode 2 and
6, opcodes `CF3A`, `CF3E`): `r`, `0 ≤ r ≤ 7` (range_chk), then the builder; whether it can take `r`
more references. -/
@[vm_spec] theorem bchkRefs (st : VmState) (s : Stack) (b : Builder) (r : Int) (quiet : Bool)
    (hs : st.stack = (s.push (.builder b)).push (.int (.num r))) :
    ExceptT.run (execInstr (.cellOp (.bchk false true quiet))) st =
      if r < 0 then (.error .rangeChk, { st with stack := s.push (.builder b) })
      else if 7 < r.toNat then (.error .rangeChk, { st with stack := s.push (.builder b) })
      else if quiet then
        (.ok (), { st with stack := s.push (.int (.num (if b.canExtendBy 0 r.toNat then -1 else 0))) })
      else if b.canExtendBy 0 r.toNat then (.ok (), { st with stack := s })
      else (.error .cellOv, { st with stack := s }) := by
  cases quiet <;> cell_check_pre <;> vm_simp [hs]

/-- `BCHKBITREFS` and `BCHKBITREFSQ` (C++ `exec_builder_chk_bits_refs`, cellops.cpp:738-751, mode 3
and 7, opcodes `CF3B`, `CF3F`): `r` on top, `0 ≤ r ≤ 7`, then `n`, `0 ≤ n ≤ 1023` (range_chk), then
the builder; whether it can take `n` more bits and `r` more references. -/
@[vm_spec] theorem bchkBitRefs (st : VmState) (s : Stack) (b : Builder) (n r : Int) (quiet : Bool)
    (hs : st.stack = ((s.push (.builder b)).push (.int (.num n))).push (.int (.num r))) :
    ExceptT.run (execInstr (.cellOp (.bchk true true quiet))) st =
      if r < 0 then (.error .rangeChk, { st with stack := (s.push (.builder b)).push (.int (.num n)) })
      else if 7 < r.toNat then (.error .rangeChk, { st with stack := (s.push (.builder b)).push (.int (.num n)) })
      else if n < 0 then (.error .rangeChk, { st with stack := s.push (.builder b) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.builder b) })
      else if quiet then
        (.ok (), { st with stack := s.push (.int (.num (if b.canExtendBy n.toNat r.toNat then -1 else 0))) })
      else if b.canExtendBy n.toNat r.toNat then (.ok (), { st with stack := s })
      else (.error .cellOv, { st with stack := s }) := by
  cases quiet <;> cell_check_pre <;> vm_simp [hs]

/-- `BDEPTH` (C++ `exec_int_builder_func` with `CellBuilder::get_depth`, cellops.cpp:844-845,
opcode `CF30`): the depth of the builder (`Builder.refsDepth`). -/
@[vm_spec] theorem bdepth (st : VmState) (s : Stack) (b : Builder) (hs : st.stack = s.push (.builder b)) :
    ExceptT.run (execInstr (.cellOp .bdepth)) st =
      (.ok (), { st with stack := s.push (.int (.num b.refsDepth)) }) := by
  vm_simp [hs, Builder.refsDepth, pure_bind, Array.forIn_pure_yield_eq_foldl]

/-- The handler of `SUBSLICE` run with its conditions decided by the hypotheses, before `vm_simp`
(whose contextual `simp` on the handler as written runs out of heartbeats). -/
local macro "subslice_pre" : tactic =>
  `(tactic| simp only [TvmLean.Exec.reduceExecInstrRun, TvmLean.Exec.unfoldModelRun, VM.run_bind, VM.run_get,
    VM.run_pure, VM.run_throw, VM.run_popInt, VM.run_popSlice, VM.run_checkUnderflow, Array.size_push,
    Nat.zero_lt_succ, dite_true, VM.back_push, Array.pop_push, VM.bindRes_ok, VM.bindRes_error, Bool.not_true,
    Bool.not_false, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, if_true, if_false, Bool.false_eq_true,
    true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, *])

/-- `SUBSLICE` (C++ `exec_subslice`, cellops.cpp:1247-1259, opcode `D734`): `r2` on top
(`0 ≤ r2 ≤ 4`), `l2` (`≤ 1023`), `r1` (`≤ 4`), `l1` (`≤ 1023`), each range_chk with the operands
below it left, then the slice: `l1` bits and `r1` references skipped, the next `l2` bits and `r2`
references as a new slice (`Slice.prefixCell`); cell_und if the slice is shorter. -/
@[vm_spec] theorem subslice (st : VmState) (s : Stack) (sl : Slice) (l1 r1 l2 r2 : Int)
    (hs : st.stack =
      ((((s.push (.slice sl)).push (.int (.num l1))).push (.int (.num r1))).push (.int (.num l2))).push
        (.int (.num r2))) :
    ExceptT.run (execInstr (.cellOp .subslice)) st =
      if r2 < 0 ∨ 4 < r2.toNat then
        (.error .rangeChk, { st with stack :=
          (((s.push (.slice sl)).push (.int (.num l1))).push (.int (.num r1))).push (.int (.num l2)) })
      else if l2 < 0 ∨ 1023 < l2.toNat then
        (.error .rangeChk, { st with stack := ((s.push (.slice sl)).push (.int (.num l1))).push (.int (.num r1)) })
      else if r1 < 0 ∨ 4 < r1.toNat then
        (.error .rangeChk, { st with stack := (s.push (.slice sl)).push (.int (.num l1)) })
      else if l1 < 0 ∨ 1023 < l1.toNat then (.error .rangeChk, { st with stack := s.push (.slice sl) })
      else
        let s1 : Slice := { sl with bitPos := sl.bitPos + l1.toNat, refPos := sl.refPos + r1.toNat }
        if sl.haveBits l1.toNat ∧ sl.haveRefs r1.toNat ∧ s1.haveBits l2.toNat ∧ s1.haveRefs r2.toNat then
          (.ok (), { st with stack := s.push (.slice (Slice.ofCell (Slice.prefixCell s1
            { s1 with bitPos := s1.bitPos + l2.toNat, refPos := s1.refPos + r2.toNat }))) })
        else (.error .cellUnd, { st with stack := s }) := by
  have hsz : ¬ s.size + 1 + 1 + 1 + 1 + 1 < 5 := by omega
  by_cases a1 : r2 < 0
  · subslice_pre
  by_cases a2 : 4 < r2.toNat
  · subslice_pre
  by_cases a3 : l2 < 0
  · subslice_pre
  by_cases a4 : 1023 < l2.toNat
  · subslice_pre
  by_cases a5 : r1 < 0
  · subslice_pre
  by_cases a6 : 4 < r1.toNat
  · subslice_pre
  by_cases a7 : l1 < 0
  · subslice_pre
  by_cases a8 : 1023 < l1.toNat
  · subslice_pre
  by_cases c1 : sl.haveBits l1.toNat = true <;> by_cases c2 : sl.haveRefs r1.toNat = true <;>
    by_cases c3 : ({ sl with bitPos := sl.bitPos + l1.toNat, refPos := sl.refPos + r1.toNat } : Slice).haveBits
      l2.toNat = true <;>
    by_cases c4 : ({ sl with bitPos := sl.bitPos + l1.toNat, refPos := sl.refPos + r1.toNat } : Slice).haveRefs
      r2.toNat = true <;>
    subslice_pre <;> vm_simp

end Spec

end TvmLean

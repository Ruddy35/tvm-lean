import TvmLean.Proofs.Exec.Closure
import TvmLean.Proofs.Exec.Spec.Stack

/-!
# Specifications: counts taken from the stack (`REVX`, `BLESSVARARGS`, `CALLXVARARGS`, `RETVARARGS`,
`RETURNARGS`, `RETURNVARARGS`)

The instructions whose counts the stack gives (C++ `pop_smallint_range`: range_chk for a count out
of its range, NaN included), written as the model's handlers run them:

* `REVX`: the counts `x` and `y` (range_chk if negative or above the limit of the global version,
  `2^30 - 1` from version 4, 255 before); the `x` values below the top `y` reversed, the values over
  255 charged one gas each;
* `BLESSVARARGS`: `more` in `-1..255`, `copy` in `0..255`; the slice becomes an ordinary
  continuation whose closure data are the `copy` values under it and `more` (`VM.blessArgsCommon`);
* `CALLXVARARGS`, `RETVARARGS`: the counts in `-1..254`, then the call (`VM.call k params retVals`)
  or the return (`VM.ret n`) with them, which the lemmas of `vm_run` on calls and jumps take on;
* `RETURNARGS p` (`p & 15`), `RETURNVARARGS` (`p` in `0..255`): `VM.returnArgsCommon p`, the values
  under the top `p` moved into the closure data of `c0`, for `c0` an ordinary continuation without
  closure data (`VM.run_returnArgsCommon_ord`, the return continuation of a call) or `quit`
  (`VM.run_returnArgsCommon_quit`, made an envelope with that closure data).
-/

namespace TvmLean

/-- **A jump to an envelope continuation with closure data** (C++ `VmState::jump`,
`adjust_jump_cont`), as `VM.run_jump_ordinary_cdata`: stk_und if it takes more arguments than the
stack has, else the closure data applied to the stack (`VmState.closureStack`) and the envelope,
without it, current (the `c0` that `RETURNARGS` makes of `quit`). -/
@[vm_run low] theorem VM.run_jump_envelope_cdata (st : VmState) (ext : Continuation) (cregs : OrdCregs)
    (cdata : OrdCdata) :
    ExceptT.run (VM.jump (.envelope ext cregs cdata)) st =
      if 0 ≤ cdata.nargs ∧ st.stack.size < cdata.nargs.toNat then (.error .stkUnd, st)
      else (.ok (), { st.closureStack cdata with cc := .envelope ext cregs OrdCdata.empty }) := by
  rcases cdata with ⟨cs, n⟩
  unfold VM.jump VmState.closureStack
  simp only [VM.run_bind, VM.run_get, VM.bindRes_ok]
  by_cases h1 : 0 ≤ n
  · by_cases h2 : st.stack.size < n.toNat
    · simp [h1, h2, VM.run_throw]
    · simp only [h1, h2, and_false, if_false, decide_true, if_true, ge_iff_le, decide_eq_true_eq]
      by_cases h3 : cs.isEmpty = true
      · by_cases h4 : n.toNat < st.stack.size
        · simp [h3, h4, VM.run_bind, VM.run_set, VM.run_modify, VM.bindRes_ok]
        · simp [h3, h4, VM.run_modify]
      · by_cases h4 : n.toNat < st.stack.size
        · simp [h3, h4, VM.run_bind, VM.run_set, VM.run_modify, VM.bindRes_ok]
          done
        · have h5 : n.toNat = st.stack.size := by omega
          simp [h3, h5, VM.run_bind, VM.run_set, VM.run_modify, VM.bindRes_ok]
  · by_cases h3 : cs.isEmpty = true <;> simp [h1, h3, VM.run_bind, VM.run_set, VM.run_modify, VM.bindRes_ok]

set_option maxHeartbeats 4000000 in
/-- **`VM.returnArgsCommon p`** (C++ `exec_return_args_common`) with `c0` an ordinary continuation
without closure data (the return continuation of a call): range_chk above 255, stk_und if the stack
has fewer than `p` values; with exactly `p` nothing; else the stack its top `p`, the values under
them the closure stack of `c0` (their stack gas charged), which then takes any number of arguments. -/
theorem VM.run_returnArgsCommon_ord (st : VmState) (p : Nat) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (hc0 : st.regs.c0 = .ordinary code saved cregs OrdCdata.empty) :
    ExceptT.run (VM.returnArgsCommon p) st =
      if p > 255 then (.error .rangeChk, st)
      else if p > st.stack.size then (.error .stkUnd, st)
      else if st.stack.size = p then (.ok (), st)
      else (.ok (), { ({ st with stack := st.stack.extract (st.stack.size - p) st.stack.size }.consumeStackGas
          (st.stack.size - p)) with
        regs := { st.regs with c0 := (.ordinary code saved cregs
          { stack := st.stack.take (st.stack.size - p), nargs := -1 }) } }) := by
  have hsz : (st.stack.take (st.stack.size - p)).size = st.stack.size - p := by
    simp only [Array.take_eq_extract, Array.size_extract]; omega
  unfold VM.returnArgsCommon
  vm_simp [hc0, Continuation.forceCdata, hsz, Array.empty_append, VmState.consumeStackGas, VmState.consumeGas]

set_option maxHeartbeats 4000000 in
/-- `VM.run_returnArgsCommon_ord` with `c0` the continuation `quit n` (the `c0` the compute phase
starts with): the values are moved into an envelope of it (`Continuation.forceCdata`). -/
theorem VM.run_returnArgsCommon_quit (st : VmState) (p : Nat) (n : Int) (hc0 : st.regs.c0 = .quit n) :
    ExceptT.run (VM.returnArgsCommon p) st =
      if p > 255 then (.error .rangeChk, st)
      else if p > st.stack.size then (.error .stkUnd, st)
      else if st.stack.size = p then (.ok (), st)
      else (.ok (), { ({ st with stack := st.stack.extract (st.stack.size - p) st.stack.size }.consumeStackGas
          (st.stack.size - p)) with
        regs := { st.regs with c0 := (.envelope (.quit n) OrdCregs.empty
          { stack := st.stack.take (st.stack.size - p), nargs := -1 }) } }) := by
  have hsz : (st.stack.take (st.stack.size - p)).size = st.stack.size - p := by
    simp only [Array.take_eq_extract, Array.size_extract]; omega
  unfold VM.returnArgsCommon
  vm_simp [hc0, Continuation.forceCdata, hsz, Array.empty_append, VmState.consumeStackGas, VmState.consumeGas]

-- entering a continuation that a jump has stripped of its closure data (the envelope `RETURNARGS`
-- makes of `quit`, reached by the implicit `RET`; `VmState.stepOnceWith` of an envelope): no data
attribute [vm_run] VmState.enteredCdata_empty OrdCdata.empty_needsMoreArgs

namespace Spec

set_option maxHeartbeats 4000000 in
/-- `REVX` (C++ `exec_reverse_x`, stackops.cpp:452-462) on the stack `s x y`: the `x` values of `s`
below its top `y` reversed; stk_und if `s` has fewer than `x + y` values. -/
@[vm_spec] theorem reverseX (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .reverseX) st =
      if y < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < y.toNat then
        (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if x < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < x.toNat then
        (.error .rangeChk, { st with stack := s })
      else if x.toNat + y.toNat ≤ s.size then
        if 255 < x.toNat then
          (.ok (), { st with
            stack := s.take (s.size - (x.toNat + y.toNat)) ++
              (s.extract (s.size - (x.toNat + y.toNat)) (s.size - y.toNat)).reverse ++
              s.extract (s.size - y.toNat) s.size
            gas := st.gas.consume (x.toNat - 255 : Nat) })
        else
          (.ok (), { st with
            stack := s.take (s.size - (x.toNat + y.toNat)) ++
              (s.extract (s.size - (x.toNat + y.toNat)) (s.size - y.toNat)).reverse ++
              s.extract (s.size - y.toNat) s.size })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Nat.shiftLeft_eq, VmState.consumeGas]

set_option maxHeartbeats 4000000 in
/-- `BLESSVARARGS` (C++ `exec_bless_varargs`, contops.cpp) on the stack `s cs copy more`: `more` in
`-1..255` and `copy` in `0..255` (range_chk); the slice `cs` becomes an ordinary continuation whose
closure stack is the top `copy` values of `s` (their stack gas charged) and which takes `more`
arguments; stk_und if `s` has fewer. -/
@[vm_spec] theorem blessVarArgs (st : VmState) (s : Stack) (cs : Slice) (copy more : Int)
    (hs : st.stack = ((s.push (.slice cs)).push (.int (.num copy))).push (.int (.num more))) :
    ExceptT.run (execInstr .blessVarArgs) st =
      if more < -1 ∨ 255 < more then
        (.error .rangeChk, { st with stack := (s.push (.slice cs)).push (.int (.num copy)) })
      else if copy < 0 then (.error .rangeChk, { st with stack := s.push (.slice cs) })
      else if 255 < copy.toNat then (.error .rangeChk, { st with stack := s.push (.slice cs) })
      else if copy.toNat ≤ s.size then
        (.ok (), { ({ st with stack := s.take (s.size - copy.toNat) }.consumeStackGas copy.toNat) with
          stack := (s.take (s.size - copy.toNat)).push (.cont (.ordinary cs (.quit 0) OrdCregs.empty
            { stack := s.extract (s.size - copy.toNat) s.size, nargs := more })) })
      else (.error .stkUnd, { st with stack := s.push (.slice cs) }) := by
  vm_simp [hs, VM.blessArgsCommon, VmState.consumeStackGas, VmState.consumeGas]
  by_cases h1 : more < -1 ∨ 255 < more
  · simp only [h1, if_true]
  · simp only [h1, if_false]
    by_cases h2 : copy < 0
    · simp only [h2, if_true]
    · simp only [h2, if_false]
      by_cases h3 : 255 < copy.toNat
      · simp only [h3, if_true]
      · simp only [h3, if_false]
        by_cases h4 : copy.toNat ≤ s.size
        · have h4' : ¬ s.size + 1 < copy.toNat + 1 := by omega
          have h5 : (s.extract (s.size - copy.toNat) s.size).size = copy.toNat := by
            simp only [Array.size_extract]; omega
          simp only [h4, h4', h5, if_true, if_false]
        · have h4' : s.size + 1 < copy.toNat + 1 := by omega
          simp only [h4, h4', if_true, if_false]

set_option maxHeartbeats 4000000 in
/-- `CALLXVARARGS` (C++ `exec_callx_varargs`, contops.cpp) on the stack `s k params retVals`: both
counts in `-1..254` (range_chk), then the call of `k` with them (`VM.call`). -/
@[vm_spec] theorem callxVarArgs (st : VmState) (s : Stack) (k : Continuation) (p r : Int)
    (hs : st.stack = ((s.push (.cont k)).push (.int (.num p))).push (.int (.num r))) :
    ExceptT.run (execInstr .callxVarArgs) st =
      if r < -1 ∨ r > 254 then (.error .rangeChk, { st with stack := (s.push (.cont k)).push (.int (.num p)) })
      else if p < -1 ∨ p > 254 then (.error .rangeChk, { st with stack := s.push (.cont k) })
      else ExceptT.run (VM.call k p r) { st with stack := s } := by
  vm_simp [hs]

set_option maxHeartbeats 4000000 in
/-- `RETVARARGS` (C++ `exec_ret_varargs`) on the stack `s n`: `n` in `-1..254` (range_chk), then the
return with `n` values passed (`VM.ret n`). -/
@[vm_spec] theorem retVarArgs (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .retVarArgs) st =
      if n < -1 ∨ n > 254 then (.error .rangeChk, { st with stack := s })
      else ExceptT.run (VM.ret n) { st with stack := s } := by
  vm_simp [hs]

/-- `RETURNARGS p` (C++ `exec_return_args`) is `VM.returnArgsCommon (p & 15)`. -/
theorem execInstr_returnArgs (st : VmState) (p : Nat) :
    ExceptT.run (execInstr (.returnArgs p)) st = ExceptT.run (VM.returnArgsCommon (p &&& 15)) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]

theorem and15_le_255 (p : Nat) : ¬ (p &&& 15) > 255 := by
  have := Nat.and_le_right (n := p) (m := 15); omega

/-- `RETURNARGS p` (C++ `exec_return_args`) with `c0` an ordinary continuation without closure
data: the values under the top `p & 15` become its closure stack (`VM.run_returnArgsCommon_ord`). -/
@[vm_spec] theorem returnArgs_ord (st : VmState) (p : Nat) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (hc0 : st.regs.c0 = .ordinary code saved cregs OrdCdata.empty) :
    ExceptT.run (execInstr (.returnArgs p)) st =
      if (p &&& 15) > st.stack.size then (.error .stkUnd, st)
      else if st.stack.size = (p &&& 15) then (.ok (), st)
      else (.ok (), { ({ st with stack := st.stack.extract (st.stack.size - (p &&& 15)) st.stack.size }.consumeStackGas
          (st.stack.size - (p &&& 15))) with
        regs := { st.regs with c0 := (.ordinary code saved cregs
          { stack := st.stack.take (st.stack.size - (p &&& 15)), nargs := -1 }) } }) := by
  rw [execInstr_returnArgs, VM.run_returnArgsCommon_ord st _ code saved cregs hc0, if_neg (and15_le_255 p)]

/-- `RETURNARGS p` with `c0` the continuation `quit n` (`VM.run_returnArgsCommon_quit`). -/
@[vm_spec] theorem returnArgs_quit (st : VmState) (p : Nat) (n : Int) (hc0 : st.regs.c0 = .quit n) :
    ExceptT.run (execInstr (.returnArgs p)) st =
      if (p &&& 15) > st.stack.size then (.error .stkUnd, st)
      else if st.stack.size = (p &&& 15) then (.ok (), st)
      else (.ok (), { ({ st with stack := st.stack.extract (st.stack.size - (p &&& 15)) st.stack.size }.consumeStackGas
          (st.stack.size - (p &&& 15))) with
        regs := { st.regs with c0 := (.envelope (.quit n) OrdCregs.empty
          { stack := st.stack.take (st.stack.size - (p &&& 15)), nargs := -1 }) } }) := by
  rw [execInstr_returnArgs, VM.run_returnArgsCommon_quit st _ n hc0, if_neg (and15_le_255 p)]

set_option maxHeartbeats 4000000 in
/-- `RETURNVARARGS` (C++ `exec_return_varargs`) on the stack `s p`: `p` in `0..255` (range_chk),
then `VM.returnArgsCommon p`. -/
theorem execInstr_returnVarArgs (st : VmState) (s : Stack) (p : Int) (hs : st.stack = s.push (.int (.num p))) :
    ExceptT.run (execInstr .returnVarArgs) st =
      if p < 0 then (.error .rangeChk, { st with stack := s })
      else if 255 < p.toNat then (.error .rangeChk, { st with stack := s })
      else ExceptT.run (VM.returnArgsCommon p.toNat) { st with stack := s } := by
  vm_simp [hs]

/-- `RETURNVARARGS` with `c0` an ordinary continuation without closure data. -/
@[vm_spec] theorem returnVarArgs_ord (st : VmState) (s : Stack) (p : Int) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (hs : st.stack = s.push (.int (.num p)))
    (hc0 : st.regs.c0 = .ordinary code saved cregs OrdCdata.empty) :
    ExceptT.run (execInstr .returnVarArgs) st =
      if p < 0 then (.error .rangeChk, { st with stack := s })
      else if 255 < p.toNat then (.error .rangeChk, { st with stack := s })
      else if p.toNat > s.size then (.error .stkUnd, { st with stack := s })
      else if s.size = p.toNat then (.ok (), { st with stack := s })
      else (.ok (), { ({ st with stack := s.extract (s.size - p.toNat) s.size }.consumeStackGas
          (s.size - p.toNat)) with
        regs := { st.regs with c0 := (.ordinary code saved cregs
          { stack := s.take (s.size - p.toNat), nargs := -1 }) } }) := by
  rw [execInstr_returnVarArgs st s p hs]
  by_cases h1 : p < 0
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : 255 < p.toNat
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, VM.run_returnArgsCommon_ord { st with stack := s } p.toNat code saved cregs hc0,
        if_neg h2]
      try rfl

/-- `RETURNVARARGS` with `c0` the continuation `quit n`. -/
@[vm_spec] theorem returnVarArgs_quit (st : VmState) (s : Stack) (p : Int) (n : Int)
    (hs : st.stack = s.push (.int (.num p))) (hc0 : st.regs.c0 = .quit n) :
    ExceptT.run (execInstr .returnVarArgs) st =
      if p < 0 then (.error .rangeChk, { st with stack := s })
      else if 255 < p.toNat then (.error .rangeChk, { st with stack := s })
      else if p.toNat > s.size then (.error .stkUnd, { st with stack := s })
      else if s.size = p.toNat then (.ok (), { st with stack := s })
      else (.ok (), { ({ st with stack := s.extract (s.size - p.toNat) s.size }.consumeStackGas
          (s.size - p.toNat)) with
        regs := { st.regs with c0 := (.envelope (.quit n) OrdCregs.empty
          { stack := s.take (s.size - p.toNat), nargs := -1 }) } }) := by
  rw [execInstr_returnVarArgs st s p hs]
  by_cases h1 : p < 0
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : 255 < p.toNat
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, VM.run_returnArgsCommon_quit { st with stack := s } p.toNat n hc0,
        if_neg h2]
      try rfl

end Spec

end TvmLean

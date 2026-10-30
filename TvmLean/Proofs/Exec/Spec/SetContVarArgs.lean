import TvmLean.Proofs.Exec.Closure
import TvmLean.Proofs.Exec.Spec.Runvm

/-!
# Specification: `SETCONTVARARGS`

`SETCONTVARARGS` (C++ `exec_setcont_varargs` with `exec_setcontargs_common`, contops.cpp) takes
`more` (`-1..255`) and `copy` (`0..255`) from the stack, then as `SETCONTARGS copy,more`. The model's
handler (TvmLean/Semantics/Exec/Cont/SetContVarArgs.lean) is written again with its branches named
(`VarArgsTail.setContVarArgs`, the same code: `vm_simp` through the handler exceeds its steps, its
join points copied into every branch), and specified for an ordinary continuation without closure
data (the continuations `PUSHCONT` makes): the top `copy` values under it become its closure stack
(their stack gas charged) and `more` the number of arguments it takes; with `copy = 0` and
`more = -1` the continuation is pushed back as it was.
-/

namespace VarArgsTail

open TvmLean

/-- The counts of `SETCONTVARARGS` (C++ `pop_smallint_range(hi, lo)`, the model's
`popSetContVarArgBounded`): range_chk out of `lo..hi`, NaN included. -/
def popBounded (lo hi : Int) : VM Int := do
  let v ← VM.popInt
  let n ←
    match v with
    | .nan => throw .rangeChk
    | .num n => pure n
  if decide (n < lo ∨ n > hi) then
    throw .rangeChk
  pure n

/-- The branch of an ordinary continuation. -/
def ordArgs (code : Slice) (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) (copyN : Nat)
    (copy more : Int) : VM Unit := do
  let mut cdata := cdata
  if copyN > 0 then
    if decide (0 ≤ cdata.nargs ∧ cdata.nargs < copy) then
      throw .stkOv
    let st0 ← get
    let depth : Nat := st0.stack.size
    let start : Nat := depth - copyN
    let captured : Array Value := st0.stack.extract start depth
    let remaining : Stack := st0.stack.take start
    set { st0 with stack := remaining }
    cdata := { cdata with stack := cdata.stack ++ captured }
    modify fun st => st.consumeStackGas cdata.stack.size
    if decide (0 ≤ cdata.nargs) then
      cdata := { cdata with nargs := cdata.nargs - copy }
  if decide (more ≥ 0) then
    if decide (cdata.nargs > more) then
      cdata := { cdata with nargs := 0x40000000 }
    else if decide (cdata.nargs < 0) then
      cdata := { cdata with nargs := more }
  VM.push (.cont (.ordinary code saved cregs cdata))

/-- The branch of an envelope continuation. -/
def envArgs (ext : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) (copyN : Nat) (copy more : Int) :
    VM Unit := do
  let mut cdata := cdata
  if copyN > 0 then
    if decide (0 ≤ cdata.nargs ∧ cdata.nargs < copy) then
      throw .stkOv
    let st0 ← get
    let depth : Nat := st0.stack.size
    let start : Nat := depth - copyN
    let captured : Array Value := st0.stack.extract start depth
    let remaining : Stack := st0.stack.take start
    set { st0 with stack := remaining }
    cdata := { cdata with stack := cdata.stack ++ captured }
    modify fun st => st.consumeStackGas cdata.stack.size
    if decide (0 ≤ cdata.nargs) then
      cdata := { cdata with nargs := cdata.nargs - copy }
  if decide (more ≥ 0) then
    if decide (cdata.nargs > more) then
      cdata := { cdata with nargs := 0x40000000 }
    else if decide (cdata.nargs < 0) then
      cdata := { cdata with nargs := more }
  VM.push (.cont (.envelope ext cregs cdata))

/-- The handler of `SETCONTVARARGS` with the branches named. -/
def setContVarArgs : VM Unit := do
  VM.checkUnderflow 2
  let more ← popBounded (-1) 255
  let copy ← popBounded 0 255
  let copyN : Nat := copy.toNat
  let st ← get
  if copyN + 1 > st.stack.size then
    throw .stkUnd
  let cont ← VM.popCont
  if copyN = 0 ∧ more = -1 then
    VM.push (.cont cont)
  else
    match cont.forceCdata with
    | .ordinary code saved cregs cdata => ordArgs code saved cregs cdata copyN copy more
    | .envelope ext cregs cdata => envArgs ext cregs cdata copyN copy more
    | _ => throw .typeChk

end VarArgsTail

namespace TvmLean

/-- `SETCONTVARARGS` runs as `VarArgsTail.setContVarArgs` (the same code). -/
theorem VarArgsTail.handler_eq (st : VmState) :
    ExceptT.run (execInstr .setContVarArgs) st = ExceptT.run VarArgsTail.setContVarArgs st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

/-- `VarArgsTail.popBounded` on a stack with an integer on top. -/
theorem VarArgsTail.run_popBounded_of (st : VmState) (t : Stack) (n lo hi : Int)
    (h : st.stack = t.push (.int (.num n))) :
    ExceptT.run (VarArgsTail.popBounded lo hi) st =
      if n < lo ∨ n > hi then (.error .rangeChk, { st with stack := t }) else (.ok n, { st with stack := t }) := by
  unfold VarArgsTail.popBounded
  rw [VM.run_bind, Runvm.run_popInt_of st t _ h, VM.bindRes_ok]
  by_cases hn : n < lo ∨ n > hi
  · simp [hn, VM.run_throw]
  · simp [hn, VM.run_pure]

/-- The ordinary branch for a continuation without closure data, `0 < copyN`, `copy = copyN`,
`-1 ≤ more`: the top `copyN` values captured, their stack gas charged, `nargs` set to `more`. -/
theorem VarArgsTail.run_ordArgs_empty (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (copyN : Nat) (copy more : Int) (h0 : 0 < copyN) (hc : copy = copyN) (hm : -1 ≤ more)
    (hd : copyN ≤ st.stack.size) :
    ExceptT.run (VarArgsTail.ordArgs code saved cregs OrdCdata.empty copyN copy more) st =
      ExceptT.run (VM.push (.cont (.ordinary code saved cregs
          { stack := st.stack.extract (st.stack.size - copyN) st.stack.size, nargs := more })))
        ({ st with stack := st.stack.take (st.stack.size - copyN) }.consumeStackGas copyN) := by
  subst hc
  unfold VarArgsTail.ordArgs
  have hn : ¬ (0 : Int) ≤ -1 := by omega
  simp only [OrdCdata.empty, h0, if_true, hn, false_and, decide_false, Bool.false_eq_true, if_false,
    VM.run_bind, VM.run_get, VM.run_set, VM.run_modify, VM.bindRes_ok, VM.run_pure, Array.empty_append]
  by_cases hm0 : 0 ≤ more
  · have h1 : ¬ (-1 : Int) > more := by omega
    have h2 : (-1 : Int) < 0 := by omega
    simp [hm0, h1, Array.size_extract, Nat.sub_sub_self hd]
  · have hm1 : more = -1 := by omega
    subst hm1
    simp [Array.size_extract, Nat.sub_sub_self hd]

/-- The ordinary branch for a continuation without closure data with `copyN = 0`: `nargs` set to
`more` (the stack unchanged). -/
theorem VarArgsTail.run_ordArgs_empty_zero (st : VmState) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (copy more : Int) (hm : -1 ≤ more) :
    ExceptT.run (VarArgsTail.ordArgs code saved cregs OrdCdata.empty 0 copy more) st =
      ExceptT.run (VM.push (.cont (.ordinary code saved cregs { nargs := more }))) st := by
  unfold VarArgsTail.ordArgs
  simp only [OrdCdata.empty, Nat.lt_irrefl, if_false, VM.run_bind, VM.run_pure, VM.bindRes_ok]
  by_cases hm0 : 0 ≤ more
  · have h1 : ¬ (-1 : Int) > more := by omega
    simp [hm0, h1]
  · have hm1 : more = -1 := by omega
    subst hm1
    simp

namespace Spec

set_option maxHeartbeats 4000000 in
/-- **`SETCONTVARARGS`** (C++ `exec_setcont_varargs`, contops.cpp) of an ordinary continuation
without closure data on the stack `s k copy more`. -/
@[vm_spec] theorem setContVarArgs_ord (st : VmState) (s : Stack) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (copy more : Int)
    (hs : st.stack = ((s.push (.cont (.ordinary code saved cregs OrdCdata.empty))).push (.int (.num copy))).push
      (.int (.num more))) :
    ExceptT.run (execInstr .setContVarArgs) st =
      if more < -1 ∨ more > 255 then
        (.error .rangeChk, { st with
          stack := ((s.push (.cont (.ordinary code saved cregs OrdCdata.empty))).push (.int (.num copy))) })
      else if copy < 0 ∨ copy > 255 then
        (.error .rangeChk, { st with stack := (s.push (.cont (.ordinary code saved cregs OrdCdata.empty))) })
      else if s.size < copy.toNat then
        (.error .stkUnd, { st with stack := (s.push (.cont (.ordinary code saved cregs OrdCdata.empty))) })
      else if copy.toNat = 0 ∧ more = -1 then
        (.ok (), { st with stack := (s.push (.cont (.ordinary code saved cregs OrdCdata.empty))) })
      else if copy.toNat = 0 then
        (.ok (), { st with stack := (s.push (.cont (.ordinary code saved cregs { nargs := more }))) })
      else
        (.ok (), { ({ st with stack := s.take (s.size - copy.toNat) }.consumeStackGas copy.toNat) with
          stack := ((s.take (s.size - copy.toNat)).push (.cont (.ordinary code saved cregs
            { stack := s.extract (s.size - copy.toNat) s.size, nargs := more }))) }) := by
  rw [VarArgsTail.handler_eq]
  unfold VarArgsTail.setContVarArgs
  have hsz : 2 ≤ st.stack.size := by rw [hs]; simp
  rw [VM.run_bind, VM.run_checkUnderflow, if_neg (by omega), VM.bindRes_ok]
  rw [VM.run_bind, VarArgsTail.run_popBounded_of st _ more _ _ hs]
  by_cases h1 : more < -1 ∨ more > 255
  · rw [if_pos h1, if_pos h1, VM.bindRes_error]
  rw [if_neg h1, if_neg h1, VM.bindRes_ok, VM.run_bind, VarArgsTail.run_popBounded_of _ _ copy _ _ rfl]
  by_cases h2 : copy < 0 ∨ copy > 255
  · rw [if_pos (by simpa using h2), if_pos h2, VM.bindRes_error]
  rw [if_neg (by simpa using h2), if_neg h2, VM.bindRes_ok]
  simp only [VM.run_bind, VM.run_get, VM.bindRes_ok]
  by_cases h3 : s.size < copy.toNat
  · rw [if_pos (by simp; omega), VM.run_bind, VM.run_throw, VM.bindRes_error, if_pos h3]
  rw [if_neg (by simp; omega), if_neg h3, VM.run_bind, VM.run_pure, VM.bindRes_ok]
  rw [VM.run_bind, VM.run_popCont, dif_pos (by simp)]
  simp only [VM.back_push, Array.pop_push, VM.bindRes_ok]
  by_cases h4 : copy.toNat = 0 ∧ more = -1
  · rw [if_pos h4, if_pos h4]
    rfl
  rw [if_neg h4, if_neg h4]
  simp only [Continuation.forceCdata]
  by_cases h5 : copy.toNat = 0
  · rw [if_pos h5, h5, VarArgsTail.run_ordArgs_empty_zero _ _ _ _ _ _ (by omega)]
    rfl
  rw [if_neg h5, VarArgsTail.run_ordArgs_empty _ _ _ _ copy.toNat copy more (by omega) (by omega) (by omega)
    (by simp; omega)]
  rfl

end Spec

end TvmLean

import TvmLean.Proofs.Exec.FoldRun
import TvmLean.Proofs.Exec.Cont
import TvmLean.Proofs.Exec.Spec.Stack

/-!
# Specifications: `SETCONTCTRMANY`, `SETCONTCTRMANYX`

As the model's handler runs them (TvmLean/Semantics/Exec/Cont/ChangeExt.lean): range_chk if the
mask has the bit of `c6`; the registers of the mask saved in the continuation from `c0` up, each by
`VmState.getCtr` and `Continuation.defineCtr` (from version 14 a register it already saves is
kept), the first exception ending it (`setContCtrManyLoop`, `setContCtrManyStep`: the loop of the
handler over the registers `0..7`). `SETCONTCTRMANYX` takes the mask from the stack (`0..255`).

In a run (a numeral mask, a continuation `PUSHCONT` wrote out) the loop is computed: its steps,
the registers read (`VmState.getCtr_*`) and saved (`Continuation.defineCtr_ordinary`,
`OrdCregs.defineFromValue_*`) are lemmas of `vm_run`. A call of the continuation it makes, which
saves `c0`, is a jump (`VM.run_call_ordinary_cdata`, TvmLean/Proofs/Exec/Closure.lean).
-/

namespace TvmLean

/-- One register `i` of `SETCONTCTRMANY mask` in the state `st`: saved in `k` if the mask has its
bit (`mask &&& 1 <<< i` of the handler written `mask &&& 2 ^ i`, which a run decides for a numeral
mask). -/
def setContCtrManyStep (st : VmState) (mask : Nat) (k : Continuation) (i : Nat) : Except Excno Continuation :=
  if mask &&& 2 ^ i = 0 then .ok k
  else
    match st.getCtr i with
    | .ok v => k.defineCtr i v (decide (14 ≤ st.globalVersion))
    | .error e => .error e

/-- The registers `i .. i + n - 1` of `SETCONTCTRMANY mask` saved in `k`, the first exception ending
it. -/
def setContCtrManyLoop (st : VmState) (mask : Nat) : Nat → Nat → Continuation → Except Excno Continuation
  | 0, _, k => .ok k
  | n + 1, i, k =>
    match setContCtrManyStep st mask k i with
    | .ok k' => setContCtrManyLoop st mask n (i + 1) k'
    | .error e => .error e

/-- The fold of the handler's loop is `setContCtrManyLoop`. -/
theorem setContCtrManyLoop_eq (st : VmState) (mask : Nat) :
    ∀ n i k, (List.range' i n).foldlM (fun x i => setContCtrManyStep st mask x i) k = setContCtrManyLoop st mask n i k
  | 0, _, _ => rfl
  | n + 1, i, k => by
    rw [List.range'_succ, List.foldlM_cons]
    unfold setContCtrManyLoop
    generalize setContCtrManyStep st mask k i = r
    rcases r with e | k'
    · rfl
    · exact setContCtrManyLoop_eq st mask n (i + 1) k'

namespace Spec

set_option maxHeartbeats 4000000 in
/-- `SETCONTCTRMANY mask` (C++ `exec_setcont_ctr_many`, contops.cpp) on the stack `s k`. -/
@[vm_spec] theorem setContCtrMany (st : VmState) (s : Stack) (k : Continuation) (mask : Nat)
    (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr (.contExt (.setContCtrMany mask))) st =
      if mask &&& 64 = 0 then
        match setContCtrManyLoop { st with stack := s } mask 8 0 k with
        | .ok k' => (.ok (), { st with stack := s.push (.cont k') })
        | .error e => (.error e, { st with stack := s })
      else (.error .rangeChk, st) := by
  vm_simp [hs, Nat.shiftLeft_eq, Nat.one_mul]
  by_cases hm : mask &&& 64 = 0
  · simp only [hm, if_true]
    rw [Std.Range.forIn_eq_forIn_range', VM.run_forIn_except _ _ _
      (fun i k => setContCtrManyStep { st with stack := s } mask k i)]
    · simp only [Std.Range.size, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv]
      rw [setContCtrManyLoop_eq]
      generalize setContCtrManyLoop { st with stack := s } mask 8 0 k = r
      rcases r with e | k'
      · rfl
      · simp only [VM.bindRes_ok, VM.run_push]
    · intro i _ x
      unfold setContCtrManyStep
      by_cases hc : mask &&& 2 ^ i = 0
      · simp only [hc, if_true, VM.run_bind, VM.run_pure, VM.bindRes_ok]
      · simp only [hc, if_false]
        generalize VmState.getCtr { st with stack := s } i = gc
        rcases gc with e | v
        · simp only [VM.run_bind, VM.run_throw, VM.bindRes_error]
        · simp only [VM.run_bind, VM.run_get, VM.bindRes_ok]
          generalize x.defineCtr i v (decide (14 ≤ st.globalVersion)) = dk
          rcases dk with e | k'
          · simp only [VM.run_bind, VM.run_throw, VM.bindRes_error]
          · simp only [VM.run_bind, VM.run_pure, VM.bindRes_ok]
  · simp only [hm, if_false]

set_option maxHeartbeats 4000000 in
/-- `SETCONTCTRMANYX` (C++ `exec_setcont_ctr_many_var`) on the stack `s k m`: the mask `m` in
`0..255` (range_chk), then as `SETCONTCTRMANY m`. -/
@[vm_spec] theorem setContCtrManyX (st : VmState) (s : Stack) (k : Continuation) (m : Int)
    (hs : st.stack = (s.push (.cont k)).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .setContCtrManyX)) st =
      if m < 0 then (.error .rangeChk, { st with stack := s.push (.cont k) })
      else if 255 < m.toNat then (.error .rangeChk, { st with stack := s.push (.cont k) })
      else if m.toNat &&& 64 = 0 then
        match setContCtrManyLoop { st with stack := s } m.toNat 8 0 k with
        | .ok k' => (.ok (), { st with stack := s.push (.cont k') })
        | .error e => (.error e, { st with stack := s })
      else (.error .rangeChk, { st with stack := s.push (.cont k) }) := by
  vm_simp [hs, Nat.shiftLeft_eq, Nat.one_mul]
  by_cases h1 : m < 0
  · simp only [h1, if_true]
  · simp only [h1, if_false]
    by_cases h2 : 255 < m.toNat
    · simp only [h2, if_true]
    · simp only [h2, if_false]
      by_cases hm : m.toNat &&& 64 = 0
      · simp only [hm, if_true]
        rw [Std.Range.forIn_eq_forIn_range', VM.run_forIn_except _ _ _
          (fun i k => setContCtrManyStep { st with stack := s } m.toNat k i)]
        · simp only [Std.Range.size, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv]
          rw [setContCtrManyLoop_eq]
          generalize setContCtrManyLoop { st with stack := s } m.toNat 8 0 k = r
          rcases r with e | k'
          · rfl
          · simp only [VM.bindRes_ok, VM.run_push]
        · intro i _ x
          unfold setContCtrManyStep
          by_cases hc : m.toNat &&& 2 ^ i = 0
          · simp only [hc, if_true, VM.run_bind, VM.run_pure, VM.bindRes_ok]
          · simp only [hc, if_false]
            generalize VmState.getCtr { st with stack := s } i = gc
            rcases gc with e | v
            · simp only [VM.run_bind, VM.run_throw, VM.bindRes_error]
            · simp only [VM.run_bind, VM.run_get, VM.bindRes_ok]
              generalize x.defineCtr i v (decide (14 ≤ st.globalVersion)) = dk
              rcases dk with e | k'
              · simp only [VM.run_bind, VM.run_throw, VM.bindRes_error]
              · simp only [VM.run_bind, VM.run_pure, VM.bindRes_ok]
      · simp only [hm, if_false]

end Spec

/-! ## The loop in a run

A numeral mask and a continuation written out (`PUSHCONT`): the loop unfolds, each register is read
(`VmState.getCtr` of a numeral) and saved in the continuation (`Continuation.defineCtr`,
`OrdCregs.defineFromValue`; the registers of `OrdCregs.empty` are none, Proofs/Exec/Cont.lean), the
continuation written out again. -/

theorem VmState.getCtr_0 (st : VmState) : st.getCtr 0 = .ok (.cont st.regs.c0) := rfl
theorem VmState.getCtr_1 (st : VmState) : st.getCtr 1 = .ok (.cont st.regs.c1) := rfl
theorem VmState.getCtr_2 (st : VmState) : st.getCtr 2 = .ok (.cont st.regs.c2) := rfl
theorem VmState.getCtr_3 (st : VmState) : st.getCtr 3 = .ok (.cont st.regs.c3) := rfl
theorem VmState.getCtr_4 (st : VmState) : st.getCtr 4 = .ok (.cell st.regs.c4) := rfl
theorem VmState.getCtr_5 (st : VmState) : st.getCtr 5 = .ok (.cell st.regs.c5) := rfl
theorem VmState.getCtr_6 (st : VmState) : st.getCtr 6 = .error .rangeChk := rfl
theorem VmState.getCtr_7 (st : VmState) : st.getCtr 7 = .ok (.tuple st.regs.c7) := rfl

/-- `Continuation.defineCtr` of an ordinary continuation: `OrdCregs.defineFromValue` of its saved
registers. -/
theorem Continuation.defineCtr_ordinary (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (cdata : OrdCdata) (idx : Nat) (v : Value) (silent : Bool) :
    (Continuation.ordinary code saved cregs cdata).defineCtr idx v silent =
      match cregs.defineFromValue idx v silent with
      | .ok c => .ok (.ordinary code saved c cdata)
      | .error e => .error e := by
  show (do let c ← cregs.defineFromValue idx v silent; pure (Continuation.ordinary code saved c cdata) :
    Except Excno Continuation) = _
  cases cregs.defineFromValue idx v silent <;> rfl

/-- `Continuation.defineCtr` of an envelope: `OrdCregs.defineFromValue` of its saved registers. -/
theorem Continuation.defineCtr_envelope (ext : Continuation) (cregs : OrdCregs) (cdata : OrdCdata)
    (idx : Nat) (v : Value) (silent : Bool) :
    (Continuation.envelope ext cregs cdata).defineCtr idx v silent =
      match cregs.defineFromValue idx v silent with
      | .ok c => .ok (.envelope ext c cdata)
      | .error e => .error e := by
  show (do let c ← cregs.defineFromValue idx v silent; pure (Continuation.envelope ext c cdata) :
    Except Excno Continuation) = _
  cases cregs.defineFromValue idx v silent <;> rfl

theorem OrdCregs.defineFromValue_c0 (cregs : OrdCregs) (k : Continuation) (silent : Bool) :
    cregs.defineFromValue 0 (.cont k) silent =
      match cregs.c0 with
      | none => .ok { cregs with c0 := some k }
      | some _ => if silent then .ok cregs else .error .typeChk := rfl
theorem OrdCregs.defineFromValue_c1 (cregs : OrdCregs) (k : Continuation) (silent : Bool) :
    cregs.defineFromValue 1 (.cont k) silent =
      match cregs.c1 with
      | none => .ok { cregs with c1 := some k }
      | some _ => if silent then .ok cregs else .error .typeChk := rfl
theorem OrdCregs.defineFromValue_c2 (cregs : OrdCregs) (k : Continuation) (silent : Bool) :
    cregs.defineFromValue 2 (.cont k) silent =
      match cregs.c2 with
      | none => .ok { cregs with c2 := some k }
      | some _ => if silent then .ok cregs else .error .typeChk := rfl
theorem OrdCregs.defineFromValue_c3 (cregs : OrdCregs) (k : Continuation) (silent : Bool) :
    cregs.defineFromValue 3 (.cont k) silent =
      match cregs.c3 with
      | none => .ok { cregs with c3 := some k }
      | some _ => if silent then .ok cregs else .error .typeChk := rfl
theorem OrdCregs.defineFromValue_c4 (cregs : OrdCregs) (c : Cell) (silent : Bool) :
    cregs.defineFromValue 4 (.cell c) silent =
      match cregs.c4 with
      | none => .ok { cregs with c4 := some c }
      | some _ => if silent then .ok cregs else .error .typeChk := rfl
theorem OrdCregs.defineFromValue_c5 (cregs : OrdCregs) (c : Cell) (silent : Bool) :
    cregs.defineFromValue 5 (.cell c) silent =
      match cregs.c5 with
      | none => .ok { cregs with c5 := some c }
      | some _ => if silent then .ok cregs else .error .typeChk := rfl

-- the loop computed in a run (a numeral mask, a continuation written out)
attribute [vm_run] setContCtrManyStep setContCtrManyLoop VmState.getCtr_0 VmState.getCtr_1
  VmState.getCtr_2 VmState.getCtr_3 VmState.getCtr_4 VmState.getCtr_5 VmState.getCtr_6
  VmState.getCtr_7 Continuation.defineCtr_ordinary Continuation.defineCtr_envelope
  OrdCregs.defineFromValue_c0 OrdCregs.defineFromValue_c1 OrdCregs.defineFromValue_c2
  OrdCregs.defineFromValue_c3 OrdCregs.defineFromValue_c4 OrdCregs.defineFromValue_c5

end TvmLean

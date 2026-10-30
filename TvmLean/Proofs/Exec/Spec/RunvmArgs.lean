import TvmLean.Proofs.Exec.Spec.RunvmX

/-!
# Specifications: `RUNVM` with the arguments of its flags

`RUNVM mode` (C++ `exec_runvm_common`, contops.cpp; `run_child_vm`, `restore_parent_vm`, vm.cpp)
pops, above the code and the values, the arguments its flags ask for: from the top the maximum gas (64),
the gas limit (8), `c7` (16), the data (4) and the number of values to return (256). Their values
are `Runvm.Args` (`none` for a flag not set; `Args.push` puts them on a stack).

* `Runvm.runArgs exec st s n code mode a`: the result of `runChildVm` with the arguments `a` (that
  of `Runvm.run`, TvmLean/Proofs/Exec/Spec/Runvm.lean, for none): range_chk for a gas argument out
  of `0 .. GasLimits.infty` or a count above `2 ^ 30`; the child's `c7` and data those passed, its gas
  limit and maximum the arguments (the maximum at least the limit) clamped by the gas the parent has
  left; with a count `k` on exit code 0 or 1, `k` values if the child left as many, else none, the
  exit code of stk_und and a 0 before it (`Runvm.retCountArgs`, `Runvm.retShort`); after the exit
  code the child's committed data (4), action list (32) and the gas it consumed (8)
  (`Runvm.flagsTail`).
* `Runvm.runChildVm_args`: `runChildVm` with the arguments of its flags on the stack is
  `Runvm.runArgs`.
* `Spec.runvm_*`: `RUNVM mode` for each set of the flags 4, 8, 16, 64, 256 (the letters `d`, `l`,
  `c`, `m`, `r`), the arguments on the stack written out (`vm_spec`); `Spec.runvm` is the case of
  none.
* `Spec.runvmx_*`: `RUNVMX` likewise (`Runvm.runxArgs`, `Runvm.execInstr_runvmx_args`: the mode
  popped, range_chk out of `0..4095`), the arguments written `Runvm.Args.push a ...`, which is
  reducible; `Spec.runvmx` (TvmLean/Proofs/Exec/Spec/RunvmX.lean) is the case of none.
-/

namespace TvmLean
namespace Runvm

/-- The arguments `RUNVM` pops above the code, by its flags (C++ `exec_runvm_common`, contops.cpp):
the maximum gas (64), the gas limit (8), `c7` (16), the data (4), the number of values to return
(256); `none` for a flag not set. -/
structure Args where
  gasMax : Option Int := none
  gasLimit : Option Int := none
  c7 : Option (Array Value) := none
  data : Option Cell := none
  retVals : Option Int := none

/-- `t` with the integer `o` pushed, if any. -/
@[reducible] def pushInt? (o : Option Int) (t : Stack) : Stack :=
  match o with
  | some g => t.push (.int (.num g))
  | none => t

/-- `t` with the tuple `o` pushed, if any. -/
@[reducible] def pushTuple? (o : Option (Array Value)) (t : Stack) : Stack :=
  match o with
  | some c => t.push (.tuple c)
  | none => t

/-- `t` with the cell `o` pushed, if any. -/
@[reducible] def pushCell? (o : Option Cell) (t : Stack) : Stack :=
  match o with
  | some c => t.push (.cell c)
  | none => t

/-- The stack `t` with the arguments `a` on it, as `RUNVM` pops them (the maximum gas on top).
Reducible, with the functions it calls: a specification whose stack is `Args.push a t` with `a`
written out unifies with the stack written out (`Spec.runvmx_*`). -/
@[reducible] def Args.push (a : Args) (t : Stack) : Stack :=
  pushInt? a.gasMax (pushInt? a.gasLimit (pushTuple? a.c7 (pushCell? a.data (pushInt? a.retVals t))))

/-- A gas argument out of `0 .. GasLimits.infty` (`popGasRange`: range_chk; the bound written out,
`infty_eq`). -/
@[vm_run] def badGas : Option Int → Bool
  | some g => decide (g < 0 ∨ g > 9223372036854775807)
  | none => false

/-- `GasLimits.infty` written out. -/
theorem infty_eq : GasLimits.infty = 9223372036854775807 := by decide

/-- A count of values to return out of `0 .. 2 ^ 30` (`VM.popNatUpTo`: range_chk). -/
@[vm_run] def badCount : Option Int → Bool
  | some r => decide (r < 0 ∨ r.toNat > 1073741824)
  | none => false

/-- An argument given (`Option.isSome` of `some`, for a run). -/
@[vm_run] theorem isSome_some_int (g : Int) : (some g).isSome = true := rfl

/-- `popGasRange` of a gas argument `g` on top of `t`. -/
theorem run_popGasRange_of (st : VmState) (t : Stack) (g : Int)
    (h : st.stack = t.push (.int (.num g))) :
    ExceptT.run popGasRange st =
      if g < 0 ∨ g > GasLimits.infty then (.error .rangeChk, { st with stack := t })
      else (.ok g, { st with stack := t }) := by
  unfold popGasRange
  rw [VM.run_bind, Runvm.run_popInt_of _ _ _ h, VM.bindRes_ok]
  by_cases hg : g < 0 ∨ g > GasLimits.infty
  · simp only [hg, if_true]
    rfl
  · simp only [hg, if_false]
    rfl

/-- The gas argument of a flag: popped if the flag is set (`b`, with the argument `o`). -/
theorem run_popGasOpt (st : VmState) (t : Stack) (o : Option Int) (b : Bool) (hb : b = o.isSome)
    (h : st.stack = pushInt? o t) :
    ExceptT.run (if b = true then popGasRange else pure GasLimits.infty) st =
      if badGas o then (.error .rangeChk, { st with stack := t })
      else (.ok (o.getD GasLimits.infty), { st with stack := t }) := by
  cases o with
  | none =>
    subst hb
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, badGas, VM.run_pure, Option.getD_none]
    simp only [pushInt?] at h
    obtain ⟨⟩ := st
    simp only at h
    subst h
    rfl
  | some g =>
    subst hb
    simp only [Option.isSome_some, if_true, badGas, Option.getD_some]
    rw [run_popGasRange_of st t g h, infty_eq]
    by_cases hg : g < 0 ∨ g > 9223372036854775807
    · simp [hg]
    · simp [hg]

/-- `VM.popTuple` of the argument `c7` of a flag, if it is set. -/
theorem run_popTupleOpt (st : VmState) (t : Stack) (o : Option (Array Value)) (b : Bool)
    (hb : b = o.isSome)
    (h : st.stack = pushTuple? o t) :
    ExceptT.run (if b = true then some <$> VM.popTuple else pure none) st =
      (.ok o, { st with stack := t }) := by
  cases o with
  | none =>
    subst hb
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, VM.run_pure]
    obtain ⟨⟩ := st
    simp only [pushTuple?] at h
    subst h
    rfl
  | some c =>
    subst hb
    simp only [Option.isSome_some, if_true]
    simp only [pushTuple?] at h
    rw [VM.run_map]
    unfold VM.popTuple
    rw [VM.run_bind, VM.run_pop]
    simp only [h, Array.size_push, Nat.zero_lt_succ, dite_true, VM.back_push, Array.pop_push, VM.bindRes_ok,
      VM.run_pure]

/-- `VM.popCell` of the argument data of a flag, if it is set. -/
theorem run_popCellOpt (st : VmState) (t : Stack) (o : Option Cell) (b : Bool) (hb : b = o.isSome)
    (h : st.stack = pushCell? o t) :
    ExceptT.run (if b = true then some <$> VM.popCell else pure none) st =
      (.ok o, { st with stack := t }) := by
  cases o with
  | none =>
    subst hb
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, VM.run_pure]
    obtain ⟨⟩ := st
    simp only [pushCell?] at h
    subst h
    rfl
  | some c =>
    subst hb
    simp only [Option.isSome_some, if_true]
    simp only [pushCell?] at h
    rw [VM.run_map, VM.run_popCell]
    simp only [h, Array.size_push, Nat.zero_lt_succ, dite_true, VM.back_push, Array.pop_push, VM.bindRes_ok,
      VM.run_pure]

/-- `VM.popNatUpTo (1 <<< 30)` of the count of values to return, if the flag is set. -/
theorem run_popCountOpt (st : VmState) (t : Stack) (o : Option Int) (b : Bool) (hb : b = o.isSome)
    (h : st.stack = pushInt? o t) :
    ExceptT.run (if b = true then some <$> VM.popNatUpTo (1 <<< 30) else pure none) st =
      if badCount o then (.error .rangeChk, { st with stack := t })
      else (.ok (o.map Int.toNat), { st with stack := t }) := by
  cases o with
  | none =>
    subst hb
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, VM.run_pure, badCount, Option.map_none]
    obtain ⟨⟩ := st
    simp only [pushInt?] at h
    subst h
    rfl
  | some r =>
    subst hb
    simp only [Option.isSome_some, if_true, badCount, Option.map_some]
    simp only [pushInt?] at h
    rw [VM.run_map, Runvm.run_popNatUpTo_of st t r _ h]
    have hk : (1 <<< 30 : Nat) = 1073741824 := by decide
    simp only [hk]
    by_cases h1 : r < 0
    · rw [if_pos h1, VM.bindRes_error, if_pos (by simp only [decide_eq_true_eq]; omega)]
    · rw [if_neg h1]
      by_cases h2 : r.toNat > 1073741824
      · rw [if_pos h2, VM.bindRes_error, if_pos (by simp only [decide_eq_true_eq]; omega)]
      · rw [if_neg h2, VM.bindRes_ok, if_neg (by simp only [decide_eq_true_eq]; omega)]
        rfl

/-- The number of values the child returns (C++ `restore_parent_vm`): with the count `k` of
`RUNVM 256` on exit code 0 or 1, `k` if the child left as many values, else none; without it as
`retCount` (all of its stack on exit code 0 or 1, else at most one value). -/
@[vm_run] def retCountArgs (rv : Option Int) (r : Int × VmState) : Nat :=
  match rv with
  | none => retCount r
  | some k =>
    if ~~~r.1 = 0 ∨ ~~~r.1 = 1 then (if r.2.stack.size ≥ k.toNat then k.toNat else 0)
    else min r.2.stack.size 1

/-- Whether the child left fewer values than the count `k` of `RUNVM 256` asks for, on exit code 0
or 1: then the exit code is that of stk_und and a 0 is pushed before it. -/
@[vm_run] def retShort (rv : Option Int) (r : Int × VmState) : Bool :=
  match rv with
  | none => false
  | some k => decide ((~~~r.1 = 0 ∨ ~~~r.1 = 1) ∧ r.2.stack.size < k.toNat)

/-- The exit code `RUNVM` pushes: `~~~ec`, or that of stk_und when the count is not met. -/
@[vm_run] def retCodeArgs (rv : Option Int) (r : Int × VmState) : Int :=
  if retShort rv r then ~~~Excno.stkUnd.toInt else ~~~r.1

/-- What `RUNVM` pushes after the exit code (C++ `restore_parent_vm`): with `return_data` (4) the
child's committed data, with `return_actions` (32) its committed action list (null if it did not
commit: `null` from version 11, before a null cell), with `return_gas` (8) the gas it consumed. -/
@[vm_run] def flagsTail (stk : Stack) (cf : VmState) (withData retActs retGas : Bool) (gv : Nat) :
    Stack :=
  let unc : Value := if gv ≥ 11 then .null else .nullCell
  let stk := if withData then stk.push (if cf.cstate.committed then .cell cf.cstate.c4 else unc) else stk
  let stk := if retActs then stk.push (if cf.cstate.committed then .cell cf.cstate.c5 else unc) else stk
  if retGas then stk.push (.int (.num cf.gas.gasConsumed)) else stk

/-- The parent's stack after `RUNVM` (`results` with the flags): `base` (and the 0 of a count not
met), the values returned, the exit code, then what the flags push (`flagsTail`). -/
@[vm_run] def resultsArgs (base : Stack) (r : Int × VmState) (cnt : Nat) (code : Int) (short : Bool)
    (withData retActs retGas : Bool) (gv : Nat) : Stack :=
  let base := if short then base.push (.int (.num 0)) else base
  flagsTail ((base ++ r.2.stack.extract (r.2.stack.size - cnt) r.2.stack.size).push (.int (.num code)))
    r.2 withData retActs retGas gv

/-- The end of `runChildVm` after the exit code, as the model writes it (the proof of
`runChildVm_args`). -/
def tailProg (parentAfter0 childFinal : VmState) (withData returnActions returnGas : Bool)
    (childConsumed : Int) : VM VmState := do
  let mut parentAfter := parentAfter0
  let uncommitted : Value := if parentAfter.globalVersion ≥ 11 then .null else .nullCell
  if withData then
    if childFinal.cstate.committed then
      parentAfter := { parentAfter with stack := parentAfter.stack.push (.cell childFinal.cstate.c4) }
    else
      parentAfter := { parentAfter with stack := parentAfter.stack.push uncommitted }
  if returnActions then
    if childFinal.cstate.committed then
      parentAfter := { parentAfter with stack := parentAfter.stack.push (.cell childFinal.cstate.c5) }
    else
      parentAfter := { parentAfter with stack := parentAfter.stack.push uncommitted }
  if returnGas then
    parentAfter := { parentAfter with stack := parentAfter.stack.push (.int (.num childConsumed)) }
  return parentAfter

theorem run_tailProg (p cf : VmState) (wd ra rg : Bool) (st : VmState) :
    ExceptT.run (tailProg p cf wd ra rg cf.gas.gasConsumed) st =
      (.ok { p with stack := flagsTail p.stack cf wd ra rg p.globalVersion }, st) := by
  unfold tailProg flagsTail
  cases wd <;> cases ra <;> cases rg <;> cases cf.cstate.committed <;>
    simp only [VM.run_bind, VM.run_pure, VM.bindRes_ok, Bool.false_eq_true, if_false, if_true] <;> rfl

/-- **The result of `runChildVm` with the arguments `a` of its flags** (`Args`), on the stack
`s n code` with `a` above: see the module doc. -/
@[vm_run] def runArgs (exec : Instr → VM Unit) (st : VmState) (s : Stack) (n : Int) (code : Slice)
    (mode : Nat) (a : Args) : Except Excno VmState × VmState :=
  let sameC3 : Bool := mode &&& 1 = 1
  let push0 : Bool := mode &&& 2 = 2
  let retActs : Bool := mode &&& 32 = 32
  let isolate : Bool := mode &&& 128 = 128
  let t0 : Stack := (s.push (.int (.num n))).push (.slice code)
  if (st.consumeGas runvmGasPrice).gas.remaining < 0 then
    (.error .outOfGas, st.consumeGas runvmGasPrice)
  else if badGas a.gasMax then
    (.error .rangeChk,
      { (st.consumeGas runvmGasPrice) with stack := Args.push { a with gasMax := none } t0 })
  else if badGas a.gasLimit then
    (.error .rangeChk,
      { (st.consumeGas runvmGasPrice) with
        stack := Args.push { a with gasMax := none, gasLimit := none } t0 })
  else if badCount a.retVals then
    (.error .rangeChk, { (st.consumeGas runvmGasPrice) with stack := t0 })
  else if n < 0 ∨ s.size < n.toNat then
    (.error .rangeChk, { (st.consumeGas runvmGasPrice) with stack := s })
  else if (popped st s n.toNat).gas.remaining < 0 then (.error .outOfGas, popped st s n.toNat)
  else if isolate = true ∧
      ((popped st s n.toNat).consumeGas (popped st s n.toNat).freeGasConsumed).gasExhaustedNow = true then
    (.error .outOfGas, (popped st s n.toNat).consumeGas (popped st s n.toNat).freeGasConsumed)
  else
    let gl0 : Int := a.gasLimit.getD GasLimits.infty
    let gm1 : Int := if a.gasMax.isSome = true then max (a.gasMax.getD GasLimits.infty) gl0 else gl0
    let q := popped st s n.toNat
    let p := parent q isolate
    let vals := s.extract (s.size - n.toNat) s.size
    let rem : Int := if st.globalVersion ≥ 10 then p.gas.remaining else q.gas.remaining
    let r := childRun exec (child p code (if sameC3 && push0 then vals.push (.int (.num 0)) else vals)
      sameC3 isolate a.c7 a.data (min gl0 rem) (min gm1 rem))
    let cnt := retCountArgs a.retVals r
    let pb := back p isolate r.2
    if pb.gas.remaining < 0 then (.error .outOfGas, pb)
    else if (pb.consumeStackGas cnt).gas.remaining < 0 then
      (.error .outOfGas, { pb.consumeStackGas cnt with
        stack := if retShort a.retVals r then pb.stack.push (.int (.num 0)) else pb.stack })
    else
      (.ok { pb.consumeStackGas cnt with
        stack := resultsArgs (s.take (s.size - n.toNat)) r cnt (retCodeArgs a.retVals r)
          (retShort a.retVals r) (mode &&& 4 = 4) retActs (mode &&& 8 = 8)
          st.globalVersion }, p)

set_option hygiene false in
/-- The end of `runvm_args_tail`: the values returned and what the flags push after them. -/
local macro "runvm_args_rest" : tactic => `(tactic| (
    unfold jp15
    extract_lets -underBinder +onlyGivenNames parentAfter2 jp16
    -- their stack gas
    split
    · rename_i hL
      rw [VM.run_bind, VM.run_set, VM.bindRes_ok, VM.run_bind, VM.run_throw, VM.bindRes_error]
      split
      · rfl
      · rename_i hR
        exact absurd (of_decide_eq_true hL) hR
    rename_i hL
    rw [VM.run_bind, VM.run_pure, VM.bindRes_ok]
    split
    · rename_i hR
      exact absurd (decide_eq_true hR) hL
    rename_i hR6
    unfold jp16
    -- the values returned
    rw [VM.run_bind]
    show VM.bindRes (ExceptT.run (forIn (List.range _).reverse parentAfter2
      (fun i r => pure (ForInStep.yield { r with stack := r.stack.push (cf.stack[depth - 1 - i]!) })) :
        VM VmState) _) _ = _
    rw [List.forIn_pure_yield_eq_foldl, VM.run_pure, VM.bindRes_ok, Runvm.push_foldl]
    unfold depth at *
    rw [Runvm.map_range_reverse_toArray cf.stack _ ?_]
    rotate_left
    · first
        | exact Nat.le_refl _
        | exact Nat.zero_le _
        | exact Nat.min_le_left _ _
        | omega
    extract_lets -underBinder +onlyGivenNames parentAfter3 parentAfter4 uncommitted jp17
    unfold jp17
    show ExceptT.run (tailProg parentAfter4 cf dt.isSome returnActions gl.isSome cf.gas.gasConsumed) _ =
      _
    rw [run_tailProg]
    rfl))

set_option hygiene false in
/-- The end of the proof of `runChildVm_args`, the same with and without `isolate_gas`. -/
local macro "runvm_args_tail" : tactic => `(tactic| (
    unfold jp13
    rw [VM.run_bind, VM.run_get, VM.bindRes_ok]
    extract_lets -underBinder +onlyGivenNames parentRem gasMax gasLimit childGas src child
    split
    rename_i x ce cf heq
    runvm_generalize_child R hR
    have hRe : R = (ce, cf) := by rw [← hR]; exact heq
    subst hRe
    extract_lets -underBinder +onlyGivenNames resCode childConsumed pay parentAfter0 parentAfter1 jp14
    -- the child's gas paid
    split
    · rename_i hL
      rw [VM.run_bind, VM.run_set, VM.bindRes_ok, VM.run_bind, VM.run_throw, VM.bindRes_error]
      split
      · rfl
      · rename_i hR
        exact absurd (of_decide_eq_true hL) hR
    rename_i hL
    rw [VM.run_bind, VM.run_pure, VM.bindRes_ok]
    split
    · rename_i hR
      exact absurd (decide_eq_true hR) hL
    rename_i hR5
    unfold jp14
    extract_lets -underBinder +onlyGivenNames depth retCnt0 jp15
    unfold resCode
    by_cases hc01 : ~~~ce = 0 ∨ ~~~ce = 1
    · rw [if_pos hc01]
      rcases rv with _ | k
      · simp only [Option.map_none, retCountArgs, retShort, retCodeArgs, retCount, hc01, if_true,
          Prod.snd, Prod.fst, Bool.false_eq_true, if_false, reduceIte]
        rw [VM.run_bind, VM.run_pure, VM.bindRes_ok]
        runvm_args_rest
      · simp only [Option.map_some]
        by_cases hk : depth ≥ k.toNat
        · rw [if_pos hk]
          simp only [retCountArgs, retShort, retCodeArgs, hc01, if_true, Prod.snd, Prod.fst,
            Bool.false_eq_true, if_false, reduceIte, show cf.stack.size ≥ k.toNat from hk,
            show ¬ cf.stack.size < k.toNat by omega, and_false, true_and, decide_false]
          rw [VM.run_bind, VM.run_pure, VM.bindRes_ok]
          runvm_args_rest
        · rw [if_neg hk]
          simp only [retCountArgs, retShort, retCodeArgs, hc01, if_true, Prod.snd, Prod.fst,
            Bool.false_eq_true, if_false, reduceIte, show ¬ cf.stack.size ≥ k.toNat from hk,
            show cf.stack.size < k.toNat by omega, and_self, true_and, decide_true]
          rw [VM.run_bind, VM.run_pure, VM.bindRes_ok]
          runvm_args_rest
    · rw [if_neg hc01]
      cases rv <;> simp only [retCountArgs, retShort, retCodeArgs, retCount, hc01, if_false, Prod.snd,
        Prod.fst, Bool.false_eq_true, reduceIte, false_and, decide_false] <;>
      rw [VM.run_bind, VM.run_pure, VM.bindRes_ok] <;>
      runvm_args_rest))

set_option maxHeartbeats 8000000 in
/-- **`runChildVm` with the arguments of its flags** (`a`, on the stack above `s n code`) is
`Runvm.runArgs`. -/
theorem runChildVm_args (exec : Instr → VM Unit) (st : VmState) (s : Stack) (n : Int) (code : Slice)
    (mode : Nat) (a : Args) (hlt : mode < 512)
    (h4 : decide (mode &&& 4 = 4) = a.data.isSome)
    (h8 : decide (mode &&& 8 = 8) = a.gasLimit.isSome)
    (h16 : decide (mode &&& 16 = 16) = a.c7.isSome)
    (h64 : decide (mode &&& 64 = 64) = a.gasMax.isSome)
    (h256 : decide (mode &&& 256 = 256) = a.retVals.isSome)
    (hs : st.stack = a.push ((s.push (.int (.num n))).push (.slice code))) :
    ExceptT.run (runChildVm exec st mode) st = runArgs exec st s n code mode a := by
  rcases a with ⟨gm, gl, c7, dt, rv⟩
  simp only at h4 h8 h16 h64 h256
  unfold runArgs
  simp only []
  unfold runChildVm
  extract_lets -underBinder +onlyGivenNames jp1
  rw [if_neg (by omega), VM.run_bind, VM.run_pure, VM.bindRes_ok]
  unfold jp1
  rw [VM.run_bind, VM.run_set, VM.bindRes_ok, VM.run_bind, VM.run_get, VM.bindRes_ok]
  extract_lets -underBinder +onlyGivenNames jp2
  by_cases h1 : (st.consumeGas runvmGasPrice).gas.remaining < 0
  · rw [if_pos (by simpa using h1), if_pos h1, VM.run_bind, VM.run_throw, VM.bindRes_error]
  rw [if_neg (by simpa using h1), if_neg h1, VM.run_bind, VM.run_pure, VM.bindRes_ok]
  unfold jp2
  extract_lets -underBinder +onlyGivenNames sameC3 push0 withData returnGas loadC7 returnActions hasHardMax
    isolateGas hasRetVals jp3
  have hWD : withData = dt.isSome := h4
  have hRG : returnGas = gl.isSome := h8
  have hC7 : loadC7 = c7.isSome := h16
  have hHM : hasHardMax = gm.isSome := h64
  have hRV : hasRetVals = rv.isSome := h256
  have hS : sameC3 = decide (mode &&& 1 = 1) := rfl
  have hP : push0 = decide (mode &&& 2 = 2) := rfl
  have hA : returnActions = decide (mode &&& 32 = 32) := rfl
  have hI : isolateGas = decide (mode &&& 128 = 128) := rfl
  have hWD' : withData = decide (mode &&& 4 = 4) := rfl
  have hRG' : returnGas = decide (mode &&& 8 = 8) := rfl
  rw [← hS, ← hP, ← hA, ← hI, ← hWD', ← hRG']
  clear_value sameC3 push0 withData returnGas loadC7 returnActions hasHardMax isolateGas hasRetVals
  subst hWD hRG hC7 hHM hRV
  -- the stacks under each argument
  have hs5 : (st.consumeGas runvmGasPrice).stack = pushInt? gm
      (Args.push { gasLimit := gl, c7 := c7, data := dt, retVals := rv }
        ((s.push (.int (.num n))).push (.slice code))) := by
    show st.stack = _
    exact hs.trans rfl
  -- the maximum gas
  rw [show (if gm.isSome = true then popGasRange >>= jp3 else pure GasLimits.infty >>= jp3) =
      ((if gm.isSome = true then popGasRange else pure GasLimits.infty) >>= jp3) from by split <;> rfl]
  rw [VM.run_bind, run_popGasOpt _ _ gm _ rfl hs5]
  by_cases hg1 : badGas gm = true
  · rw [if_pos hg1, if_pos hg1, VM.bindRes_error]
  rw [if_neg hg1, if_neg hg1, VM.bindRes_ok]
  unfold jp3
  extract_lets -underBinder +onlyGivenNames jp4
  -- the gas limit
  rw [show (if gl.isSome = true then popGasRange >>= jp4 else pure GasLimits.infty >>= jp4) =
      ((if gl.isSome = true then popGasRange else pure GasLimits.infty) >>= jp4) from by split <;> rfl]
  rw [VM.run_bind, run_popGasOpt _ (Args.push { c7 := c7, data := dt, retVals := rv }
    ((s.push (.int (.num n))).push (.slice code))) gl _ rfl rfl]
  by_cases hg2 : badGas gl = true
  · rw [if_pos hg2, if_pos hg2, VM.bindRes_error]
  rw [if_neg hg2, if_neg hg2, VM.bindRes_ok]
  unfold jp4
  extract_lets -underBinder +onlyGivenNames gasMax1 jp5
  -- `c7`
  rw [show (if c7.isSome = true then (some <$> VM.popTuple) >>= jp5 else pure none >>= jp5) =
      ((if c7.isSome = true then some <$> VM.popTuple else pure none) >>= jp5) from by split <;> rfl]
  rw [VM.run_bind, run_popTupleOpt _ (Args.push { data := dt, retVals := rv }
    ((s.push (.int (.num n))).push (.slice code))) c7 _ rfl rfl, VM.bindRes_ok]
  unfold jp5
  extract_lets -underBinder +onlyGivenNames jp6
  -- the data
  rw [show (if dt.isSome = true then (some <$> VM.popCell) >>= jp6 else pure none >>= jp6) =
      ((if dt.isSome = true then some <$> VM.popCell else pure none) >>= jp6) from by split <;> rfl]
  rw [VM.run_bind, run_popCellOpt _ (Args.push { retVals := rv }
    ((s.push (.int (.num n))).push (.slice code))) dt _ rfl rfl, VM.bindRes_ok]
  unfold jp6
  extract_lets -underBinder +onlyGivenNames jp7
  -- the count of values to return
  rw [show (if rv.isSome = true then (some <$> VM.popNatUpTo (1 <<< 30)) >>= jp7 else pure none >>= jp7) =
      ((if rv.isSome = true then some <$> VM.popNatUpTo (1 <<< 30) else pure none) >>= jp7) from by
        split <;> rfl]
  rw [VM.run_bind, run_popCountOpt _ ((s.push (.int (.num n))).push (.slice code)) rv _ rfl rfl]
  by_cases hg3 : badCount rv = true
  · rw [if_pos hg3, if_pos hg3, VM.bindRes_error]
  rw [if_neg hg3, if_neg hg3, VM.bindRes_ok]
  unfold jp7
  rw [VM.run_bind, Runvm.run_popSlice_of _ _ _ rfl, VM.bindRes_ok, VM.run_bind, VM.run_get, VM.bindRes_ok]
  extract_lets -underBinder +onlyGivenNames jp8
  rw [if_neg (by simp), VM.run_bind, VM.run_pure, VM.bindRes_ok]
  unfold jp8
  rw [VM.run_bind, Runvm.run_popInt_of _ s _ rfl, VM.bindRes_ok]
  extract_lets -underBinder +onlyGivenNames jp9
  dsimp only
  by_cases hn : n < 0
  · rw [if_pos hn, VM.run_bind, VM.run_throw, VM.bindRes_error, if_pos (Or.inl hn)]
  rw [if_neg hn, VM.run_bind, VM.run_pure, VM.bindRes_ok]
  unfold jp9
  rw [VM.run_bind, VM.run_get, VM.bindRes_ok]
  extract_lets -underBinder +onlyGivenNames jp10
  by_cases hsz : s.size < n.toNat
  · rw [if_pos (by exact hsz), VM.run_bind, VM.run_throw, VM.bindRes_error, if_pos (Or.inr hsz)]
  rw [if_neg (by exact hsz), VM.run_bind, VM.run_pure, VM.bindRes_ok, if_neg (by omega)]
  unfold jp10
  extract_lets -underBinder +onlyGivenNames childStack0
  unfold childStack0
  rw [VM.run_bind]
  show VM.bindRes (ExceptT.run (forIn [:n.toNat] (Array.replicate n.toNat Value.null)
    (fun i r => VM.pop >>= fun v => pure (ForInStep.yield (r.set! (n.toNat - 1 - i) v)))) _) _ = _
  rw [Runvm.run_forIn_range_pop _ _ _ _ (by simp; omega), Runvm.popFold_values _ _ (by simp; omega),
    VM.bindRes_ok]
  rw [VM.run_bind, VM.run_modify, VM.bindRes_ok, VM.run_bind, VM.run_get, VM.bindRes_ok]
  extract_lets -underBinder +onlyGivenNames jp11
  -- the stack gas
  split
  · rename_i hL
    rw [VM.run_bind, VM.run_throw, VM.bindRes_error]
    split
    · rfl
    · rename_i hR
      exact absurd (of_decide_eq_true hL) hR
  rename_i hL
  rw [VM.run_bind, VM.run_pure, VM.bindRes_ok]
  split
  · rename_i hR
    exact absurd (decide_eq_true hR) hL
  unfold jp11
  extract_lets -underBinder +onlyGivenNames jp12
  -- `push_0`
  rw [VM.run_ite, VM.run_bind (pure PUnit.unit), VM.run_pure, VM.bindRes_ok, VM.run_bind (pure PUnit.unit),
    VM.run_pure, VM.bindRes_ok]
  rw [← apply_ite (fun cs => ExceptT.run (jp12 cs PUnit.unit) _)]
  unfold jp12
  extract_lets -underBinder +onlyGivenNames childCc childRegs0 childRegs1 childRegs2 childRegs3
  rw [VM.run_bind, VM.run_get, VM.bindRes_ok]
  extract_lets -underBinder +onlyGivenNames parentRem0 jp13
  -- `isolate_gas`
  cases isolateGas
  all_goals simp only [Bool.false_eq_true, false_and, true_and, if_false, if_true]
  · rw [VM.run_bind (pure PUnit.unit), VM.run_pure, VM.bindRes_ok]
    runvm_args_tail
  · rw [VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_bind, VM.run_consumeGas, VM.bindRes_ite]
    split
    · rename_i hL
      rw [VM.bindRes_error]
      split
      · rfl
      · rename_i hR
        exact absurd hL hR
    rename_i hL
    rw [VM.bindRes_ok, VM.run_bind, VM.run_modify, VM.bindRes_ok]
    split
    · rename_i hR
      exact absurd hR hL
    runvm_args_tail

/-- A flag `b` of a mode whose flags that pop arguments are `bits` (`m &&& 0x15c = bits`): set in
`m &&& 4095` as in `bits`. -/
theorem flag_of {m bits : Nat} (h : m &&& 0x15c = bits) (b : Nat)
    (hb : b &&& 0x15c = b ∧ 4095 &&& b = b) :
    decide ((m &&& 4095) &&& b = b) = decide (bits &&& b = b) := by
  have e1 : (m &&& 4095) &&& b = m &&& b := by rw [Nat.and_assoc, hb.2]
  have e2 : bits &&& b = m &&& b := by rw [← h, Nat.and_assoc, Nat.and_comm 0x15c b, hb.1]
  rw [e1, e2]

/-- `flag_of` for `RUNVMX`: its mode `m` below 512, `m &&& 4095` is `m`. -/
theorem flag_of_x {m bits : Nat} (h : m &&& 0x15c = bits) (b : Nat) (hb : b &&& 0x15c = b) :
    decide (m &&& b = b) = decide (bits &&& b = b) := by
  have e : bits &&& b = m &&& b := by rw [← h, Nat.and_assoc, Nat.and_comm 0x15c b, hb]
  rw [e]

/-- **The result of `RUNVMX`** with the mode `m` and the arguments `a` of its flags, on the stack
`s n code` with `a` and `m` above: range_chk for a mode out of `0..4095` (the mode popped), else
`runArgs`, its result set as the parent's state. -/
@[vm_run] def runxArgs (exec : Instr → VM Unit) (st : VmState) (s : Stack) (n : Int) (code : Slice)
    (m : Int) (a : Args) : Except Excno Unit × VmState :=
  if m < 0 then (.error .rangeChk, { st with stack := a.push ((s.push (.int (.num n))).push (.slice code)) })
  else if 4095 < m.toNat then
    (.error .rangeChk, { st with stack := a.push ((s.push (.int (.num n))).push (.slice code)) })
  else VM.bindRes (runArgs exec { st with stack := a.push ((s.push (.int (.num n))).push (.slice code)) }
    s n code m.toNat a) (fun st' => set st')

/-- `RUNVMX` with the arguments `a` of the flags of its mode on the stack is `runxArgs`
(`execInstr_runvmx`, `runChildVm_args`). -/
theorem execInstr_runvmx_args (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int) (a : Args)
    (hlt : m.toNat < 512)
    (h4 : decide (m.toNat &&& 4 = 4) = a.data.isSome)
    (h8 : decide (m.toNat &&& 8 = 8) = a.gasLimit.isSome)
    (h16 : decide (m.toNat &&& 16 = 16) = a.c7.isSome)
    (h64 : decide (m.toNat &&& 64 = 64) = a.gasMax.isSome)
    (h256 : decide (m.toNat &&& 256 = 256) = a.retVals.isSome)
    (hs : st.stack = (a.push ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1)) st s n code m a := by
  unfold runxArgs
  rw [execInstr_runvmx, popNatUpToSigned, Runvm.run_popNatUpTo_of st _ m 4095 hs]
  by_cases h1 : m < 0
  · rw [if_pos h1, if_pos h1]; rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : 4095 < m.toNat
    · rw [if_pos (show m.toNat > 4095 from h2), if_pos h2]; rfl
    · rw [if_neg (show ¬ m.toNat > 4095 from h2), if_neg h2, VM.bindRes_ok, VM.run_bind, VM.run_get,
        VM.bindRes_ok, VM.run_bind, runChildVm_args _ _ s n code _ a hlt h4 h8 h16 h64 h256 rfl]

end Runvm

namespace Spec

/-- `RUNVM mode` whose flags pop the count of values to return (256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_r (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (rv : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 256)
    (hs : st.stack = ((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { retVals := some rv }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_d (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (d : Cell)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 4)
    (hs : st.stack = ((s.push (.int (.num n))).push (.slice code)).push (.cell d)) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { data := some d }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { data := some d } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop `c7` (16) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_c (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (c7 : Array Value)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 16)
    (hs : st.stack = ((s.push (.int (.num n))).push (.slice code)).push (.tuple c7)) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { c7 := some c7 }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { c7 := some c7 } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the gas limit (8) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_l (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (gl : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 8)
    (hs : st.stack = ((s.push (.int (.num n))).push (.slice code)).push (.int (.num gl))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { gasLimit := some gl }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { gasLimit := some gl } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the maximum gas (64) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_m (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 64)
    (hs : st.stack = ((s.push (.int (.num n))).push (.slice code)).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { gasMax := some gm }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the count of values to return (256)
(`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_dr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (rv : Int)
    (d : Cell)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 260)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.cell d)) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { retVals := some rv, data := some d }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, data := some d } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop `c7` (16), the count of values to return (256) (`Runvm.runArgs`).
-/
@[vm_spec] theorem runvm_cr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (rv : Int)
    (c7 : Array Value)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 272)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.tuple c7)) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { retVals := some rv, c7 := some c7 }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, c7 := some c7 } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the gas limit (8), the count of values to return (256)
(`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_lr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (rv : Int)
    (gl : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 264)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.int (.num gl))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, gasLimit := some gl })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, gasLimit := some gl } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the maximum gas (64), the count of values to return (256)
(`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_mr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (rv : Int)
    (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 320)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), `c7` (16) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cd (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (d : Cell)
    (c7 : Array Value)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 20)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.cell d)).push
      (.tuple c7)) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { data := some d, c7 := some c7 }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { data := some d, c7 := some c7 } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the gas limit (8) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_dl (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (d : Cell)
    (gl : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 12)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.cell d)).push
      (.int (.num gl))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { data := some d, gasLimit := some gl }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { data := some d, gasLimit := some gl } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the maximum gas (64) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_dm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (d : Cell)
    (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 68)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.cell d)).push
      (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { data := some d, gasMax := some gm }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { data := some d, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the gas limit (8), `c7` (16) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cl (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (c7 : Array Value) (gl : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 24)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.tuple c7)).push
      (.int (.num gl))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { c7 := some c7, gasLimit := some gl }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { c7 := some c7, gasLimit := some gl } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop `c7` (16), the maximum gas (64) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (c7 : Array Value) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 80)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.tuple c7)).push
      (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095) { c7 := some c7, gasMax := some gm }) (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { c7 := some c7, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the gas limit (8), the maximum gas (64) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_lm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat) (gl : Int)
    (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 72)
    (hs : st.stack = (((s.push (.int (.num n))).push (.slice code)).push (.int (.num gl))).push
      (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { gasLimit := some gl, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { gasLimit := some gl, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), `c7` (16), the count of values to return (256)
(`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cdr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (d : Cell) (c7 : Array Value)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 276)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.cell d)).push (.tuple c7)) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, data := some d, c7 := some c7 })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, data := some d, c7 := some c7 } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the gas limit (8), the count of values to return
(256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_dlr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (d : Cell) (gl : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 268)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.cell d)).push (.int (.num gl))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, data := some d, gasLimit := some gl })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, data := some d, gasLimit := some gl } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the maximum gas (64), the count of values to return
(256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_dmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (d : Cell) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 324)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.cell d)).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, data := some d, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, data := some d, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the gas limit (8), `c7` (16), the count of values to return (256)
(`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_clr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (c7 : Array Value) (gl : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 280)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.tuple c7)).push (.int (.num gl))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, c7 := some c7, gasLimit := some gl })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, c7 := some c7, gasLimit := some gl } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop `c7` (16), the maximum gas (64), the count of values to return
(256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (c7 : Array Value) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 336)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.tuple c7)).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, c7 := some c7, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, c7 := some c7, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the gas limit (8), the maximum gas (64), the count of values to
return (256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_lmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (gl : Int) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 328)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.int (.num gl))).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, gasLimit := some gl, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, gasLimit := some gl, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the gas limit (8), `c7` (16) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cdl (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (d : Cell) (c7 : Array Value) (gl : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 28)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.cell d)).push
      (.tuple c7)).push (.int (.num gl))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { data := some d, c7 := some c7, gasLimit := some gl })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { data := some d, c7 := some c7, gasLimit := some gl } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), `c7` (16), the maximum gas (64) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cdm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (d : Cell) (c7 : Array Value) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 84)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.cell d)).push
      (.tuple c7)).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { data := some d, c7 := some c7, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { data := some d, c7 := some c7, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the gas limit (8), the maximum gas (64)
(`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_dlm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (d : Cell) (gl : Int) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 76)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.cell d)).push
      (.int (.num gl))).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { data := some d, gasLimit := some gl, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { data := some d, gasLimit := some gl, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the gas limit (8), `c7` (16), the maximum gas (64)
(`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_clm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (c7 : Array Value) (gl : Int) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 88)
    (hs : st.stack = ((((s.push (.int (.num n))).push (.slice code)).push (.tuple c7)).push
      (.int (.num gl))).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { c7 := some c7, gasLimit := some gl, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { c7 := some c7, gasLimit := some gl, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the gas limit (8), `c7` (16), the count of values to
return (256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cdlr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (d : Cell) (c7 : Array Value) (gl : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 284)
    (hs : st.stack = (((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.cell d)).push (.tuple c7)).push (.int (.num gl))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, data := some d, c7 := some c7, gasLimit := some gl })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, data := some d, c7 := some c7, gasLimit := some gl } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), `c7` (16), the maximum gas (64), the count of values
to return (256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cdmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (d : Cell) (c7 : Array Value) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 340)
    (hs : st.stack = (((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.cell d)).push (.tuple c7)).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, data := some d, c7 := some c7, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, data := some d, c7 := some c7, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the gas limit (8), the maximum gas (64), the count of
values to return (256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_dlmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (d : Cell) (gl : Int) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 332)
    (hs : st.stack = (((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.cell d)).push (.int (.num gl))).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, data := some d, gasLimit := some gl, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, data := some d, gasLimit := some gl, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the gas limit (8), `c7` (16), the maximum gas (64), the count of
values to return (256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_clmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (c7 : Array Value) (gl : Int) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 344)
    (hs : st.stack = (((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.tuple c7)).push (.int (.num gl))).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, c7 := some c7, gasLimit := some gl, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, c7 := some c7, gasLimit := some gl, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the gas limit (8), `c7` (16), the maximum gas (64)
(`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cdlm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (d : Cell) (c7 : Array Value) (gl : Int) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 92)
    (hs : st.stack = (((((s.push (.int (.num n))).push (.slice code)).push (.cell d)).push
      (.tuple c7)).push (.int (.num gl))).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { data := some d, c7 := some c7, gasLimit := some gl, gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { data := some d, c7 := some c7, gasLimit := some gl, gasMax := some gm } hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVM mode` whose flags pop the data (4), the gas limit (8), `c7` (16), the maximum gas (64),
the count of values to return (256) (`Runvm.runArgs`). -/
@[vm_spec] theorem runvm_cdlmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (rv : Int) (d : Cell) (c7 : Array Value) (gl : Int) (gm : Int)
    (hm : m &&& 4095 < 512 ∧ m &&& 0x15c = 348)
    (hs : st.stack = ((((((s.push (.int (.num n))).push (.slice code)).push (.int (.num rv))).push
      (.cell d)).push (.tuple c7)).push (.int (.num gl))).push (.int (.num gm))) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.runArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code (m &&& 4095)
        { retVals := some rv, data := some d, c7 := some c7, gasLimit := some gl,
          gasMax := some gm })
        (fun st' => set st') := by
  rw [execInstr_runvm, Runvm.runChildVm_args _ st s n code _
    { retVals := some rv, data := some d, c7 := some c7, gasLimit := some gl, gasMax := some gm }
    hm.1
    (Runvm.flag_of hm.2 4 (by decide)) (Runvm.flag_of hm.2 8 (by decide))
    (Runvm.flag_of hm.2 16 (by decide)) (Runvm.flag_of hm.2 64 (by decide))
    (Runvm.flag_of hm.2 256 (by decide)) (hs.trans rfl)]

/-- `RUNVMX` with a mode whose flags pop the count of values to return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_r (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int) (rv : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 256)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_d (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int) (d : Cell)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 4)
    (hs : st.stack = (Runvm.Args.push
      { data := some d }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { data := some d } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop `c7` (16) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_c (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (c7 : Array Value)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 16)
    (hs : st.stack = (Runvm.Args.push
      { c7 := some c7 }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { c7 := some c7 } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the gas limit (8) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_l (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int) (gl : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 8)
    (hs : st.stack = (Runvm.Args.push
      { gasLimit := some gl }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { gasLimit := some gl } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the maximum gas (64) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_m (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 64)
    (hs : st.stack = (Runvm.Args.push
      { gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the count of values to return (256)
(`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_dr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (d : Cell)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 260)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, data := some d }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, data := some d } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop `c7` (16), the count of values to return (256)
(`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (c7 : Array Value)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 272)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, c7 := some c7 }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, c7 := some c7 } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the gas limit (8), the count of values to return (256)
(`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_lr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (gl : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 264)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, gasLimit := some gl }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, gasLimit := some gl } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the maximum gas (64), the count of values to return (256)
(`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_mr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 320)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), `c7` (16) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cd (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (d : Cell) (c7 : Array Value)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 20)
    (hs : st.stack = (Runvm.Args.push
      { data := some d, c7 := some c7 }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { data := some d, c7 := some c7 } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the gas limit (8) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_dl (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (d : Cell) (gl : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 12)
    (hs : st.stack = (Runvm.Args.push
      { data := some d, gasLimit := some gl }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { data := some d, gasLimit := some gl } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the maximum gas (64) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_dm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (d : Cell) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 68)
    (hs : st.stack = (Runvm.Args.push
      { data := some d, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { data := some d, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the gas limit (8), `c7` (16) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cl (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (c7 : Array Value) (gl : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 24)
    (hs : st.stack = (Runvm.Args.push
      { c7 := some c7, gasLimit := some gl }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { c7 := some c7, gasLimit := some gl } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop `c7` (16), the maximum gas (64) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (c7 : Array Value) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 80)
    (hs : st.stack = (Runvm.Args.push
      { c7 := some c7, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { c7 := some c7, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the gas limit (8), the maximum gas (64) (`Runvm.runxArgs`).
-/
@[vm_spec] theorem runvmx_lm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (gl : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 72)
    (hs : st.stack = (Runvm.Args.push
      { gasLimit := some gl, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { gasLimit := some gl, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), `c7` (16), the count of values to return
(256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cdr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (d : Cell) (c7 : Array Value)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 276)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, data := some d, c7 := some c7 }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, data := some d, c7 := some c7 } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the gas limit (8), the count of values to
return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_dlr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (d : Cell) (gl : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 268)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, data := some d, gasLimit := some gl }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, data := some d, gasLimit := some gl } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the maximum gas (64), the count of values to
return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_dmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (d : Cell) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 324)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, data := some d, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, data := some d, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the gas limit (8), `c7` (16), the count of values to return
(256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_clr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (c7 : Array Value) (gl : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 280)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, c7 := some c7, gasLimit := some gl }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, c7 := some c7, gasLimit := some gl } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop `c7` (16), the maximum gas (64), the count of values to
return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (c7 : Array Value) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 336)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, c7 := some c7, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, c7 := some c7, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the gas limit (8), the maximum gas (64), the count of
values to return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_lmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (gl : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 328)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, gasLimit := some gl, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, gasLimit := some gl, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the gas limit (8), `c7` (16)
(`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cdl (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (d : Cell) (c7 : Array Value) (gl : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 28)
    (hs : st.stack = (Runvm.Args.push
      { data := some d, c7 := some c7, gasLimit := some gl }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { data := some d, c7 := some c7, gasLimit := some gl } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), `c7` (16), the maximum gas (64)
(`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cdm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (d : Cell) (c7 : Array Value) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 84)
    (hs : st.stack = (Runvm.Args.push
      { data := some d, c7 := some c7, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { data := some d, c7 := some c7, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the gas limit (8), the maximum gas (64)
(`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_dlm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (d : Cell) (gl : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 76)
    (hs : st.stack = (Runvm.Args.push
      { data := some d, gasLimit := some gl, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { data := some d, gasLimit := some gl, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the gas limit (8), `c7` (16), the maximum gas (64)
(`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_clm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (c7 : Array Value) (gl : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 88)
    (hs : st.stack = (Runvm.Args.push
      { c7 := some c7, gasLimit := some gl, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { c7 := some c7, gasLimit := some gl, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the gas limit (8), `c7` (16), the count of
values to return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cdlr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (d : Cell) (c7 : Array Value) (gl : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 284)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, data := some d, c7 := some c7, gasLimit := some gl }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, data := some d, c7 := some c7, gasLimit := some gl } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), `c7` (16), the maximum gas (64), the count of
values to return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cdmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (d : Cell) (c7 : Array Value) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 340)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, data := some d, c7 := some c7, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { retVals := some rv, data := some d, c7 := some c7, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the gas limit (8), the maximum gas (64), the
count of values to return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_dlmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (d : Cell) (gl : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 332)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, data := some d, gasLimit := some gl, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m
        { retVals := some rv, data := some d, gasLimit := some gl, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the gas limit (8), `c7` (16), the maximum gas (64), the
count of values to return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_clmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (c7 : Array Value) (gl : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 344)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, c7 := some c7, gasLimit := some gl, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m
        { retVals := some rv, c7 := some c7, gasLimit := some gl, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the gas limit (8), `c7` (16), the maximum gas
(64) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cdlm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (d : Cell) (c7 : Array Value) (gl : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 92)
    (hs : st.stack = (Runvm.Args.push
      { data := some d, c7 := some c7, gasLimit := some gl, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m { data := some d, c7 := some c7, gasLimit := some gl, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

/-- `RUNVMX` with a mode whose flags pop the data (4), the gas limit (8), `c7` (16), the maximum gas
(64), the count of values to return (256) (`Runvm.runxArgs`). -/
@[vm_spec] theorem runvmx_cdlmr (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Int)
    (rv : Int) (d : Cell) (c7 : Array Value) (gl : Int) (gm : Int)
    (hm : m.toNat < 512 ∧ m.toNat &&& 0x15c = 348)
    (hs : st.stack = (Runvm.Args.push
      { retVals := some rv, data := some d, c7 := some c7, gasLimit := some gl, gasMax := some gm }
      ((s.push (.int (.num n))).push (.slice code))).push (.int (.num m))) :
    ExceptT.run (execInstr (.contExt .runvmx)) st =
      Runvm.runxArgs (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st s n code m
        { retVals := some rv, data := some d, c7 := some c7, gasLimit := some gl, gasMax := some gm } :=
  Runvm.execInstr_runvmx_args st s n code m _ hm.1 (Runvm.flag_of_x hm.2 4 (by decide))
    (Runvm.flag_of_x hm.2 8 (by decide)) (Runvm.flag_of_x hm.2 16 (by decide))
    (Runvm.flag_of_x hm.2 64 (by decide)) (Runvm.flag_of_x hm.2 256 (by decide)) hs

end Spec
end TvmLean

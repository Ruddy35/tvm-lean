import TvmLean.Proofs.Exec.Eval

/-!
# Specification: `RUNVM`

`RUNVM mode` (C++ `exec_runvm`, contops.cpp, with `exec_runvm_common` and `VmState::run_child_vm`,
`restore_parent_vm`, vm.cpp) runs a child VM on code and values the parent passes, then gives the
parent the values the child returns, its exit code and, with the flags, its data, actions and gas.
In the model (`runChildVm`, TvmLean/Semantics/Exec/Flow/Runvm.lean) the child runs to its end with
`childRun exec child`, `exec` the instructions of the child (`execInstrNested`, at the depth the gas
bounds); here that run stays a term: `childRun exec (Runvm.child ...)`, the child state written out
as the model builds it, so that what the parent does after it is known whatever the child does.

* `Runvm.run exec st s n code mode`: the result of `runChildVm` for a mode without arguments
  beyond the code and the values (`Runvm.Plain mode`: no data, gas limits, `c7` or count of return
  values to pop; `same_c3`, `push_0`, `return_actions` and `isolate_gas` may be set), on the stack
  `s n code` with an integer `n`: the charge of `RUNVM`, the `n` values popped and charged as stack
  entries, the child run, its gas paid by the parent (`Runvm.back`), the values it returns (all on
  exit code 0 or 1, else at most one) charged and pushed, the exit code `~~~ec`, its committed
  action list or null with `return_actions`; out of gas or range_chk where the model raises them.
* `Spec.runvm`: `RUNVM mode` in such a mode is `Runvm.run` (`vm_spec`), its result set as the
  parent's state.

The loops of the handler are written out: popping the values (`Runvm.run_forIn_pop`, the values
in order, `Runvm.popFold_set`) and pushing those returned (`Runvm.push_foldl`,
`Runvm.map_range_reverse_toArray`).
-/

namespace TvmLean

namespace Runvm

/-! ## The loops -/

/-- The values a loop collects that pops the stack `S` once per element `i` of `l`, folding each
popped value into the accumulator with `f i`. -/
def popFold {β : Type} (f : Nat → β → Value → β) : List Nat → β → Array Value → β
  | [], acc, _ => acc
  | i :: l, acc, S => popFold f l (f i acc S.back!) S.pop

/-- **The pop loop of `RUNVM`** (C++ `exec_runvm_common`, contops.cpp: the `stack_size` values
passed to the child): a `for` loop whose body pops the stack and folds the value in, run on a stack
with at least as many values as the loop has elements, pops them all. -/
theorem run_forIn_pop {β : Type} (f : Nat → β → Value → β) :
    ∀ (l : List Nat) (init : β) (st : VmState), l.length ≤ st.stack.size →
      ExceptT.run (forIn l init (fun i r => VM.pop >>= fun v => pure (ForInStep.yield (f i r v))) : VM β) st =
        (.ok (popFold f l init st.stack), { st with stack := st.stack.take (st.stack.size - l.length) }) := by
  intro l
  induction l with
  | nil =>
    intro init st _
    simp only [List.forIn_nil, VM.run_pure, popFold, List.length_nil, Nat.sub_zero, Array.take_eq_extract,
      Array.extract_size]
  | cons i l ih =>
    intro init st h
    simp only [List.length_cons] at h
    have h0 : 0 < st.stack.size := by omega
    rw [List.forIn_cons, VM.run_bind, VM.run_bind, VM.run_pop, dif_pos h0, VM.bindRes_ok, VM.run_pure,
      VM.bindRes_ok]
    rw [ih _ _ (by simp only [Array.size_pop]; omega)]
    have hb : st.stack.back h0 = st.stack.back! := by
      rw [Array.back_eq_getElem, Array.back!_eq_back?, Array.back?_eq_getElem?,
        Array.getElem?_eq_getElem (by omega), Option.getD_some]
    simp only [popFold, List.length_cons, hb]
    congr 2
    apply Array.ext
    · simp; omega
    · intro p h1 h2
      simp [Array.take_eq_extract, Array.getElem_extract, Array.getElem_pop]

/-- `run_forIn_pop` for the loop over `[:k]` of the model. -/
theorem run_forIn_range_pop {β : Type} (f : Nat → β → Value → β) (k : Nat) (init : β) (st : VmState)
    (hk : k ≤ st.stack.size) :
    ExceptT.run (forIn [:k] init (fun i r => VM.pop >>= fun v => pure (ForInStep.yield (f i r v))) : VM β) st =
      (.ok (popFold f (List.range' 0 k) init st.stack), { st with stack := st.stack.take (st.stack.size - k) }) := by
  rw [Std.Range.forIn_eq_forIn_range', run_forIn_pop f _ init st (by simp; omega)]
  simp

/-- The values of `RUNVM`'s pop loop (`Array.set!` of each value at its place in an array of
`null`s): the top `k` values of the stack `S`, in order. A step of the induction: the loop over the
indices `j .. j + m - 1` on the stack `T`. -/
theorem popFold_set (k : Nat) :
    ∀ (m j : Nat) (acc T : Array Value), j + m = k → m ≤ T.size → acc.size = k →
      popFold (fun i r v => r.set! (k - 1 - i) v) (List.range' j m) acc T =
        T.extract (T.size - m) T.size ++ acc.extract m k := by
  intro m
  induction m with
  | zero =>
    intro j acc T _ _ hacc
    simp [popFold, ← hacc]
  | succ m ih =>
    intro j acc T hjk hm hacc
    rw [List.range'_succ, popFold, ih (j + 1) _ _ (by omega) (by simp; omega) (by simp [hacc])]
    have hk : k - 1 - j = m := by omega
    rw [hk]
    apply Array.ext
    · simp [hacc]; omega
    · intro p h1 h2
      simp only [Array.size_append, Array.size_extract, Array.size_pop, Array.set!_eq_setIfInBounds,
        Array.size_setIfInBounds, Nat.min_self, hacc] at h1 h2
      simp only [Array.getElem_append, Array.getElem_extract, Array.size_extract, Array.size_pop,
        Array.getElem_pop, Array.set!_eq_setIfInBounds, Nat.min_self]
      by_cases hp : p < m
      · rw [dif_pos (by omega), dif_pos (by omega)]
        congr 1
        omega
      · rw [dif_neg (by omega)]
        have hidx : m + (p - (T.size - 1 - (T.size - 1 - m))) = p := by omega
        simp only [hidx]
        rw [Array.getElem_setIfInBounds (by omega)]
        by_cases hpm : p = m
        · subst hpm
          rw [if_pos rfl, dif_pos (by omega), Array.back!_eq_back?, Array.back?_eq_getElem?]
          simp only [Array.getElem?_eq_getElem (show T.size - 1 < T.size by omega), Option.getD_some]
          congr 1
          omega
        · rw [if_neg (by omega), dif_neg (by omega)]
          congr 1
          omega

/-- The values `RUNVM` passes to the child: the top `k` values of `S`, in order. -/
theorem popFold_values (S : Array Value) (k : Nat) (h : k ≤ S.size) :
    popFold (fun i r v => r.set! (k - 1 - i) v) (List.range' 0 k) (Array.replicate k .null) S =
      S.extract (S.size - k) S.size := by
  rw [popFold_set k k 0 _ _ (by omega) h (by simp)]
  simp

theorem extract_push_eq {α : Type} [Inhabited α] (cs : Array α) (n : Nat) (h : n + 1 ≤ cs.size) :
    #[cs[cs.size - 1 - n]!] ++ cs.extract (cs.size - n) cs.size = cs.extract (cs.size - (n + 1)) cs.size := by
  apply Array.ext
  · simp; omega
  · intro p h1 h2
    simp only [Array.getElem_append, Array.getElem_extract, List.size_toArray, List.length_singleton]
    by_cases hp : p < 1
    · rw [dif_pos hp]
      simp only [show p = 0 by omega, List.getElem_toArray, List.getElem_singleton]
      rw [getElem!_pos cs _ (by omega)]
      congr 1
      omega
    · rw [dif_neg hp]
      congr 1
      omega

/-- The values `RUNVM` gives back, pushed for `i` from `n - 1` down to `0` (`cs[size - 1 - i]`): the
top `n` values of the child's stack `cs`, in order. -/
theorem map_range_reverse_toArray {α : Type} [Inhabited α] (cs : Array α) :
    ∀ n, n ≤ cs.size →
      ((List.range n).reverse.map (fun i => cs[cs.size - 1 - i]!)).toArray = cs.extract (cs.size - n) cs.size := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.map_cons, ← extract_push_eq cs n h, ← ih (by omega)]
    apply Array.ext <;> simp

/-- The push loop of `RUNVM` (`restore_parent_vm`): pushing a value per element of `l` appends them. -/
theorem push_foldl (g : Nat → Value) :
    ∀ (l : List Nat) (st : VmState),
      l.foldl (fun b a => { b with stack := b.stack.push (g a) }) st =
        { st with stack := st.stack ++ (l.map g).toArray } := by
  intro l
  induction l with
  | nil => intro st; simp
  | cons a l ih =>
    intro st
    rw [List.foldl_cons, ih]
    have hs : st.stack.push (g a) ++ (l.map g).toArray = st.stack ++ ((a :: l).map g).toArray := by simp
    simp only [hs]

/-! ## The child and the parent after it -/

/-- The child state of `RUNVM` (C++ `run_child_vm`, vm.cpp, as `runChildVm` builds it): the code
`code` as current continuation (returning to `quit 0`), the stack `vals`, the registers of a new VM
with `c3` the code if `same_c3`, `c7` and `c4` if passed, the gas `GasLimits.ofLimits gasLimit gasMax 0`,
the parent's counters, libraries (those loaded too), limits and version, its loaded cells unless
`isolate_gas`. -/
def child (p : VmState) (code : Slice) (vals : Array Value) (sameC3 isolateGas : Bool)
    (c7 : Option (Array Value)) (data : Option Cell) (gasLimit gasMax : Int) : VmState :=
  let cc : Continuation := .ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty
  let regs1 : Regs := if sameC3 then { Regs.initial with c3 := cc } else Regs.initial
  let regs2 : Regs := match c7 with
    | none => regs1
    | some t => { regs1 with c7 := t }
  let regs3 : Regs := match data with
    | none => regs2
    | some c => { regs2 with c4 := c }
  { (VmState.initial code.cell) with
    stack := vals
    regs := regs3
    cc := cc
    gas := GasLimits.ofLimits gasLimit gasMax 0
    loadedCells := if isolateGas then #[] else p.loadedCells
    chksgnCounter := p.chksgnCounter
    getExtraBalanceCounter := p.getExtraBalanceCounter
    freeGasConsumed := p.freeGasConsumed
    libraries := p.libraries
    loadedLibraries := p.loadedLibraries
    maxLibraryLoads := p.maxLibraryLoads
    maxDataDepth := p.maxDataDepth
    globalVersion := p.globalVersion }

/-- The parent `p` after the child ended in `cf` (C++ `restore_parent_vm`, vm.cpp): it pays the
child's gas (`min(gas consumed, gas limit + 1)`, as a `long long`), counts its steps, takes back its
libraries, counters and, unless `isolate_gas`, its loaded cells. -/
@[vm_run] def back (p : VmState) (isolateGas : Bool) (cf : VmState) : VmState :=
  { (p.consumeGas (min cf.gas.gasConsumed (int64Wrap (cf.gas.gasLimit + 1)))) with
    steps := p.steps + cf.steps
    libraries := cf.libraries
    loadedLibraries := cf.loadedLibraries
    chksgnCounter := cf.chksgnCounter
    getExtraBalanceCounter := cf.getExtraBalanceCounter
    freeGasConsumed := cf.freeGasConsumed
    loadedCells := if isolateGas then p.loadedCells else cf.loadedCells }

/-- A mode of `RUNVM` that pops no argument but the code and the values: below 512 (else range_chk),
none of the flags 4 (data), 8 (gas limit), 16 (`c7`), 64 (gas maximum), 256 (count of return values). -/
abbrev Plain (mode : Nat) : Prop := mode < 512 ∧ mode &&& 0x15c = 0

/-- The parent once `RUNVM` took its arguments from the stack `s ... code`: `RUNVM` charged, the `k`
values popped (`s` without its top `k`) and charged as stack entries (`consume_stack_gas`). -/
@[vm_run] def popped (st : VmState) (s : Stack) (k : Nat) : VmState :=
  ({ (st.consumeGas runvmGasPrice) with stack := s.take (s.size - k) } : VmState).consumeStackGas k

/-- The parent when the child starts: with `isolate_gas` it has paid its free gas and its counters
start again (C++ `run_child_vm`, vm.cpp). -/
@[vm_run] def parent (p : VmState) (isolate : Bool) : VmState :=
  if isolate then
    { (p.consumeGas p.freeGasConsumed) with
      chksgnCounter := 0
      getExtraBalanceCounter := 0
      freeGasConsumed := 0 }
  else p

/-- The gas the child may use: what the parent has left, after the free gas it paid with
`isolate_gas` from version 10 (`p`), before it (`q`) earlier (vm.cpp; contops.cpp). -/
@[vm_run] def gasLeft (gv : Nat) (q p : VmState) : Int :=
  min GasLimits.infty (if gv ≥ 10 then p.gas.remaining else q.gas.remaining)

/-- The number of values the child returns: all of its stack on exit code 0 or 1 (`~~~ec`), else at
most one (C++ `restore_parent_vm`). -/
@[vm_run] def retCount (r : Int × VmState) : Nat :=
  if ~~~r.1 = 0 ∨ ~~~r.1 = 1 then r.2.stack.size else min r.2.stack.size 1

/-- The parent's stack after `RUNVM`: `base`, the top `cnt` values of the child's stack, the exit
code `~~~ec`, and with `return_actions` the child's committed action list (null if it did not commit:
`null` from version 11, before a null cell). -/
@[vm_run] def results (base : Stack) (r : Int × VmState) (cnt : Nat) (retActs : Bool) (gv : Nat) : Stack :=
  let stk := (base ++ r.2.stack.extract (r.2.stack.size - cnt) r.2.stack.size).push (.int (.num (~~~r.1)))
  if retActs then
    stk.push (if r.2.cstate.committed then .cell r.2.cstate.c5 else if gv ≥ 11 then .null else .nullCell)
  else stk

/-- **The result of `runChildVm` in a plain mode** (`Plain`), on the stack `s n code` (`n` an
integer): see the module doc. The child runs `exec` (`childRun`, the term of its run). -/
@[vm_run] def run (exec : Instr → VM Unit) (st : VmState) (s : Stack) (n : Int) (code : Slice) (mode : Nat) :
    Except Excno VmState × VmState :=
  let sameC3 : Bool := mode &&& 1 = 1
  let push0 : Bool := mode &&& 2 = 2
  let retActs : Bool := mode &&& 32 = 32
  let isolate : Bool := mode &&& 128 = 128
  if (st.consumeGas runvmGasPrice).gas.remaining < 0 then (.error .outOfGas, st.consumeGas runvmGasPrice)
  else if n < 0 ∨ s.size < n.toNat then (.error .rangeChk, { (st.consumeGas runvmGasPrice) with stack := s })
  else if (popped st s n.toNat).gas.remaining < 0 then (.error .outOfGas, popped st s n.toNat)
  else if isolate = true ∧
      ((popped st s n.toNat).consumeGas (popped st s n.toNat).freeGasConsumed).gasExhaustedNow = true then
    (.error .outOfGas, (popped st s n.toNat).consumeGas (popped st s n.toNat).freeGasConsumed)
  else
    let p := parent (popped st s n.toNat) isolate
    let vals := s.extract (s.size - n.toNat) s.size
    let g := gasLeft st.globalVersion (popped st s n.toNat) p
    let r := childRun exec (child p code (if sameC3 && push0 then vals.push (.int (.num 0)) else vals)
      sameC3 isolate none none g g)
    if (back p isolate r.2).gas.remaining < 0 then (.error .outOfGas, back p isolate r.2)
    else if ((back p isolate r.2).consumeStackGas (retCount r)).gas.remaining < 0 then
      (.error .outOfGas, (back p isolate r.2).consumeStackGas (retCount r))
    else
      (.ok { (back p isolate r.2).consumeStackGas (retCount r) with
        stack := results (s.take (s.size - n.toNat)) r (retCount r) retActs st.globalVersion }, p)

end Runvm

/-- The handler of `RUNVM mode`: `runChildVm` with the child's instructions at the depth the gas
bounds, its state set (the dispatch of `execInstr`, `execInstrFlowRunvm`). -/
theorem execInstr_runvm (m : Nat) (st : VmState) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (ExceptT.run (runChildVm (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1))
        st (m &&& 0xfff)) st) (fun st' => set st') := by
  simp only [TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok]

/-- `VM.popSlice` on a stack with a slice on top. -/
theorem Runvm.run_popSlice_of (st : VmState) (t : Stack) (c : Slice) (h : st.stack = t.push (.slice c)) :
    ExceptT.run VM.popSlice st = (.ok c, { st with stack := t }) := by
  simp only [VM.run_popSlice, h, Array.size_push, Nat.zero_lt_succ, dite_true, VM.back_push, Array.pop_push]

/-- `VM.popInt` on a stack with an integer on top. -/
theorem Runvm.run_popInt_of (st : VmState) (t : Stack) (i : IntVal) (h : st.stack = t.push (.int i)) :
    ExceptT.run VM.popInt st = (.ok i, { st with stack := t }) := by
  simp only [VM.run_popInt, h, Array.size_push, Nat.zero_lt_succ, dite_true, VM.back_push, Array.pop_push]

open Lean Meta Elab Tactic in
/-- Generalizes the run of the child in the goal, `childRun exec (Runvm.child ...)`, to a variable
`r` with the equation `h` (the proof of `runChildVm_plain`). -/
elab "runvm_generalize_child " r:ident h:ident : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (fun x => x.isAppOfArity ``childRun 2 && (x.getArg! 1).isAppOf ``Runvm.child &&
      !x.hasLooseBVars)
    | throwError "runvm_generalize_child: no run of the child"
  let (_, g') ← g.generalize #[{ expr := e, xName? := r.getId, hName? := h.getId }]
  replaceMainGoal [g']

theorem Runvm.and_eq_zero {m b mask : Nat} (hb : b &&& mask = b) (h : m &&& mask = 0) : m &&& b = 0 := by
  have : m &&& b = (m &&& mask) &&& b := by rw [Nat.and_assoc, Nat.and_comm mask b, hb]
  rw [this, h, Nat.zero_and]

set_option hygiene false in
/-- The end of the proof of `runChildVm_plain`, the same with and without `isolate_gas`: from the
start of the child to the values it returns. -/
local macro "runvm_tail" : tactic => `(tactic| (
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
    -- the number of values returned
    rw [VM.run_ite]
    simp only [VM.run_bind, VM.run_pure, VM.bindRes_ok]
    rw [← apply_ite (fun k => ExceptT.run (jp15 parentAfter1 resCode k PUnit.unit) _)]
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
    have hcnt : (if resCode = 0 ∨ resCode = 1 then depth else Nat.min depth 1) ≤ cf.stack.size := by
      unfold depth
      split
      · exact Nat.le_refl _
      · exact Nat.min_le_left _ _
    rw [VM.run_bind]
    show VM.bindRes (ExceptT.run (forIn (List.range _).reverse parentAfter2
      (fun i r => pure (ForInStep.yield { r with stack := r.stack.push (cf.stack[depth - 1 - i]!) })) : VM VmState) _)
      _ = _
    rw [List.forIn_pure_yield_eq_foldl, VM.run_pure, VM.bindRes_ok, Runvm.push_foldl]
    unfold depth at hcnt ⊢
    rw [Runvm.map_range_reverse_toArray cf.stack _ hcnt]
    extract_lets -underBinder +onlyGivenNames parentAfter3 parentAfter4 uncommitted jp17
    rw [if_neg (by simp), VM.run_bind, VM.run_pure, VM.bindRes_ok]
    unfold jp17
    simp only [VM.run_ite, VM.run_bind, VM.run_pure, VM.bindRes_ok, Bool.false_eq_true, if_false, reduceIte]
    cases returnActions
    · simp only [Bool.false_eq_true, if_false, reduceIte]
      rfl
    · simp only [if_true, reduceIte]
      split
      · rename_i hc
        simp only [Runvm.results, hc, reduceIte] <;> rfl
      · rename_i hc
        simp only [Runvm.results, hc, reduceIte, Bool.false_eq_true] <;> rfl))

set_option maxHeartbeats 4000000 in
/-- **`runChildVm` in a plain mode** is `Runvm.run`. -/
theorem runChildVm_plain (exec : Instr → VM Unit) (st : VmState) (s : Stack) (n : Int) (code : Slice)
    (mode : Nat) (hm : Runvm.Plain mode)
    (hs : st.stack = (s.push (.int (.num n))).push (.slice code)) :
    ExceptT.run (runChildVm exec st mode) st = Runvm.run exec st s n code mode := by
  obtain ⟨hlt, hpl⟩ := hm
  have h4 : mode &&& 4 = 0 := Runvm.and_eq_zero (by decide) hpl
  have h8 : mode &&& 8 = 0 := Runvm.and_eq_zero (by decide) hpl
  have h16 : mode &&& 16 = 0 := Runvm.and_eq_zero (by decide) hpl
  have h64 : mode &&& 64 = 0 := Runvm.and_eq_zero (by decide) hpl
  have h256 : mode &&& 256 = 0 := Runvm.and_eq_zero (by decide) hpl
  unfold Runvm.run
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
  have hWD : withData = false := by simp [withData, h4]
  have hRG : returnGas = false := by simp [returnGas, h8]
  have hC7 : loadC7 = false := by simp [loadC7, h16]
  have hHM : hasHardMax = false := by simp [hasHardMax, h64]
  have hRV : hasRetVals = false := by simp [hasRetVals, h256]
  have hS : sameC3 = decide (mode &&& 1 = 1) := rfl
  have hP : push0 = decide (mode &&& 2 = 2) := rfl
  have hA : returnActions = decide (mode &&& 32 = 32) := rfl
  have hI : isolateGas = decide (mode &&& 128 = 128) := rfl
  rw [← hS, ← hP, ← hA, ← hI]
  clear_value sameC3 push0 withData returnGas loadC7 returnActions hasHardMax isolateGas hasRetVals
  subst hWD hRG hC7 hHM hRV
  rw [if_neg (by simp), VM.run_bind, VM.run_pure, VM.bindRes_ok]
  unfold jp3
  extract_lets -underBinder +onlyGivenNames jp4
  rw [if_neg (by simp), VM.run_bind, VM.run_pure, VM.bindRes_ok]
  unfold jp4
  extract_lets -underBinder +onlyGivenNames gasMax1 jp5
  rw [if_neg (by simp), VM.run_bind, VM.run_pure, VM.bindRes_ok]
  unfold jp5
  extract_lets -underBinder +onlyGivenNames jp6
  rw [if_neg (by simp), VM.run_bind, VM.run_pure, VM.bindRes_ok]
  unfold jp6
  extract_lets -underBinder +onlyGivenNames jp7
  rw [if_neg (by simp), VM.run_bind, VM.run_pure, VM.bindRes_ok]
  unfold jp7
  rw [VM.run_bind, Runvm.run_popSlice_of _ _ _ (by exact hs), VM.bindRes_ok, VM.run_bind, VM.run_get, VM.bindRes_ok]
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
    runvm_tail
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
    runvm_tail

namespace Spec

/-- **`RUNVM mode`** (C++ `exec_runvm`, contops.cpp, `exec_runvm_common`; vm.cpp `run_child_vm`,
`restore_parent_vm`) in a plain mode (`Runvm.Plain`: no argument popped but the code and the values),
on the stack `s n code`: `Runvm.run`, the child running the instructions of `execInstrNested` at the
depth the gas bounds (`execInstrFlowRunvm`), its result set as the parent's state. -/
@[vm_spec] theorem runvm (st : VmState) (s : Stack) (n : Int) (code : Slice) (m : Nat)
    (hm : Runvm.Plain (m &&& 4095))
    (hs : st.stack = (s.push (.int (.num n))).push (.slice code)) :
    ExceptT.run (execInstr (.contExt (.runvm m))) st =
      VM.bindRes (Runvm.run (execInstrNested (st.gas.remaining.toNat / runvmGasPrice.toNat + 1)) st s n code
        (m &&& 4095)) (fun st' => set st') := by
  rw [execInstr_runvm, runChildVm_plain _ st s n code _ hm hs]

end Spec

end TvmLean

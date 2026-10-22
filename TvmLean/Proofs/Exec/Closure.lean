import TvmLean.Proofs.Exec.Cont

/-!
# Jumps to and calls of continuations with closure data

A continuation with closure data (C++ `ControlData::stack` and `nargs`, made by `SETCONTARGS`,
`BLESSARGS` and the like) shapes the stack when it is entered: it takes the top `nargs` values
(all if `nargs < 0`, stk_und if the stack has fewer) and puts its captured stack under them. A
call also saves the values under the arguments in the return continuation, which puts them back
when it is entered. The lemmas here state the model's `VM.jump` and `VM.call` on such
continuations in closed form, for `vm_run`:

* `VM.run_jump_ordinary_cdata`: a jump (C++ `VmState::jump`, `adjust_jump_cont`): the stack
  `VmState.closureStack`, the continuation entered without its closure data;
* `VM.run_call_ordinary_cdata`: a call (C++ `VmState::call`): if the continuation saved `c0`, the
  jump; else the stack `VmState.callClosure` (captured stack and arguments, their gas), the values
  under the arguments saved in the return continuation (`VmState.callSaved`,
  `VmState.retContWith`), which becomes `c0`;
* `VM.run_callComputeStacks`: the stacks a call computes, in closed form;
* `Spec.setContArgs_ord`: `SETCONTARGS` of a continuation without closure data (the handler
  written again with its branches named, `ContTail.setContArgs`: `vm_simp` through the model's
  handler overflowed the stack).

Both are of low priority: the lemmas of `Proofs/Exec/VM.lean` on continuations without closure
data apply first.
-/

namespace ContTail

open TvmLean

/-- The `SETCONTARGS` of an ordinary continuation (the branch of the model's handler,
`TvmLean/Semantics/Exec/Cont/SetContArgs.lean`). -/
def ordArgs (code : Slice) (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) (copyN : Nat)
    (more : Int) : VM Unit := do
  let mut cont : Continuation := .ordinary code saved cregs cdata
  let mut cdata := cdata
  if copyN > 0 then
    if decide (0 ≤ cdata.nargs ∧ cdata.nargs < Int.ofNat copyN) then
      throw .stkOv
    let st0 ← get
    let depth : Nat := st0.stack.size
    let start : Nat := depth - copyN
    let captured : Array Value := st0.stack.extract start depth
    let remaining : Stack := st0.stack.take start
    set { st0 with stack := remaining }
    cdata := { cdata with stack := cdata.stack ++ captured }
    -- C++ charges stack gas based on the closure stack depth.
    modify fun st => st.consumeStackGas cdata.stack.size
    if decide (0 ≤ cdata.nargs) then
      cdata := { cdata with nargs := cdata.nargs - Int.ofNat copyN }
  if decide (more ≥ 0) then
    if decide (cdata.nargs > more) then
      cdata := { cdata with nargs := 0x40000000 }
    else if decide (cdata.nargs < 0) then
      cdata := { cdata with nargs := more }
  cont := .ordinary code saved cregs cdata
  VM.push (.cont cont)

/-- The `SETCONTARGS` of an envelope continuation. -/
def envArgs (ext : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) (copyN : Nat) (more : Int) : VM Unit := do
  let mut cont : Continuation := .envelope ext cregs cdata
  let mut cdata := cdata
  if copyN > 0 then
    if decide (0 ≤ cdata.nargs ∧ cdata.nargs < Int.ofNat copyN) then
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
      cdata := { cdata with nargs := cdata.nargs - Int.ofNat copyN }
  if decide (more ≥ 0) then
    if decide (cdata.nargs > more) then
      cdata := { cdata with nargs := 0x40000000 }
    else if decide (cdata.nargs < 0) then
      cdata := { cdata with nargs := more }
  cont := .envelope ext cregs cdata
  VM.push (.cont cont)

/-- The handler of `SETCONTARGS` with the branches named. -/
def setContArgs (copy : Nat) (more : Int) : VM Unit := do
  if copy > 15 then
    throw .rangeChk
  if decide (more < -1 ∨ more > 14) then
    throw .rangeChk
  let copyN : Nat := copy
  let st ← get
  if copyN + 1 > st.stack.size then
    throw .stkUnd
  let cont ← VM.popCont
  if copyN = 0 ∧ more = -1 then
    VM.push (.cont cont)
  else
    let cont := cont.forceCdata
    match cont with
    | .ordinary code saved cregs cdata => ordArgs code saved cregs cdata copyN more
    | .envelope ext cregs cdata => envArgs ext cregs cdata copyN more
    | _ =>
        throw .typeChk

end ContTail

namespace TvmLean

/-- A slice of a stack written with `push` (the captured values of a closure, its arguments). -/
@[vm_run] theorem VM.extract_push {α : Type} (s : Array α) (v : α) (i j : Nat) :
    (s.push v).extract i j =
      if j ≤ s.size then s.extract i j else if i ≤ s.size then (s.extract i s.size).push v else #[] := by
  apply Array.ext_getElem?
  intro k
  simp only [Array.getElem?_extract, Array.size_push]
  by_cases hj : j ≤ s.size
  · simp only [hj, if_true, Array.getElem?_extract]
    by_cases hk : k < min j (s.size + 1) - i
    · have hk' : k < min j s.size - i := by omega
      simp only [hk, hk', if_true, Array.getElem?_push]
      have : i + k ≠ s.size := by omega
      simp [this]
    · have hk' : ¬ k < min j s.size - i := by omega
      simp [hk, hk']
  · simp only [hj, if_false]
    by_cases hi : i ≤ s.size
    · simp only [hi, if_true, Array.getElem?_push, Array.size_extract, Array.getElem?_extract]
      by_cases hk : k < min j (s.size + 1) - i
      · simp only [hk, if_true]
        by_cases hks : i + k = s.size
        · have : k = s.size - i := by omega
          subst this
          have h5 : i + (s.size - i) = s.size := by omega
          simp [h5]
        · have h2 : k < s.size - i := by omega
          have h3 : k ≠ s.size - i := by omega
          simp [hks, h2, h3]
      · have h2 : ¬ k < s.size - i := by omega
        have h3 : k ≠ s.size - i := by omega
        simp [hk, h2, h3]
    · have hk : ¬ k < min j (s.size + 1) - i := by omega
      simp [hi, hk]

@[vm_run] theorem VM.extract_empty_of_le {α : Type} (s : Array α) (i j : Nat) (h : j ≤ i) : s.extract i j = #[] := by
  apply Array.ext_getElem?
  intro k
  simp only [Array.getElem?_extract]
  have : ¬ k < min j s.size - i := by omega
  simp [this]

/-- A captured stack under arguments written with `push`. -/
@[vm_run] theorem VM.append_push {α : Type} (s t : Array α) (v : α) : s ++ t.push v = (s ++ t).push v := by
  simp

@[vm_run] theorem VM.append_empty {α : Type} (s : Array α) : s ++ (#[] : Array α) = s := by
  simp

/-- A stack written with `push` is not empty. -/
@[vm_run] theorem VM.isEmpty_push {α : Type} (s : Array α) (v : α) : (s.push v).isEmpty = false := by
  simp

/-- The stack gas of a depth (C++ `VmState::consume_stack_gas`): the entries beyond the free depth,
written out for `vm_run`. -/
@[vm_run] theorem VmState.consumeStackGas_eq (st : VmState) (d : Nat) :
    st.consumeStackGas d =
      st.consumeGas (Int.ofNat (if d > freeStackDepth then d - freeStackDepth else 0) * stackEntryGasPrice) := rfl

/-- **A jump to an ordinary continuation with closure data** (C++ `VmState::jump`,
`adjust_jump_cont`): stk_und if it takes more arguments than the stack has, else the closure data
applied to the stack (`VmState.closureStack`) and the continuation, without it, current. -/
@[vm_run low] theorem VM.run_jump_ordinary_cdata (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (cdata : OrdCdata) :
    ExceptT.run (VM.jump (.ordinary code saved cregs cdata)) st =
      if 0 ≤ cdata.nargs ∧ st.stack.size < cdata.nargs.toNat then (.error .stkUnd, st)
      else (.ok (), { st.closureStack cdata with cc := .ordinary code saved cregs OrdCdata.empty }) := by
  rcases cdata with ⟨cs, n⟩
  unfold VM.jump VmState.closureStack
  simp only [VM.run_bind, VM.run_get, VM.bindRes_ok]
  by_cases h1 : 0 ≤ n
  · by_cases h2 : st.stack.size < n.toNat
    · simp [h1, h2, VM.run_throw]
    · have h2' : ¬ n.toNat > st.stack.size := by omega
      simp only [h1, h2, h2', and_false, if_false, and_self, decide_true, if_true, ge_iff_le, decide_eq_true_eq]
      by_cases h3 : cs.isEmpty = true
      · by_cases h4 : n.toNat < st.stack.size
        · simp [h3, h4, h1, VM.run_bind, VM.run_set, VM.run_modify, VM.bindRes_ok]
        · simp [h3, h4, h1, VM.run_bind, VM.run_set, VM.run_modify, VM.bindRes_ok]
      · have hsz : n.toNat = st.stack.size ∨ n.toNat < st.stack.size := by omega
        by_cases h4 : n.toNat < st.stack.size
        · simp [h3, h4, h1, VM.run_bind, VM.run_set, VM.run_modify, VM.bindRes_ok]
          done
        · have h5 : n.toNat = st.stack.size := by omega
          simp [h3, h4, h1, h5, VM.run_bind, VM.run_set, VM.run_modify, VM.bindRes_ok]
  · by_cases h3 : cs.isEmpty = true <;> simp [h1, h3, VM.run_bind, VM.run_set, VM.run_modify, VM.bindRes_ok]


/-- The arguments a continuation with closure data takes from the stack: the top `nargs` values,
all of them if `nargs < 0`. -/
def VmState.closureArgs (st : VmState) (cdata : OrdCdata) : Stack :=
  if 0 ≤ cdata.nargs then st.stack.extract (st.stack.size - cdata.nargs.toNat) st.stack.size else st.stack

/-- The values a call saves under the arguments (restored on return): those under the top `nargs`,
none if `nargs < 0`. -/
def VmState.callSaved (st : VmState) (cdata : OrdCdata) : Stack :=
  if 0 ≤ cdata.nargs then st.stack.take (st.stack.size - cdata.nargs.toNat) else #[]

/-- The state after a call shaped the stack for a continuation with closure data (C++
`VmState::call`): the captured stack under the arguments, the gas of the new depth charged (unless
the stack is kept whole: no captured stack and `nargs < 0`). -/
def VmState.callClosure (st : VmState) (cdata : OrdCdata) : VmState :=
  if cdata.stack.isEmpty ∧ cdata.nargs < 0 then st
  else { st with stack := cdata.stack ++ st.closureArgs cdata }.consumeStackGas (cdata.stack ++ st.closureArgs cdata).size

/-- The return continuation of a call that saved the values `saved` (C++ `VmState::call`): the rest of the
current code, with the old `c0` and the saved values as its captured stack. -/
def VmState.retContWith (st : VmState) (saved : Stack) : Continuation :=
  match st.cc with
  | .ordinary code _ _ _ => .ordinary code (.quit 0) { OrdCregs.empty with c0 := some st.regs.c0 } { stack := saved, nargs := -1 }
  | _ => .quit 0

/-- The stacks of a call with closure data `captured` and `nargs` (C++ `VmState::call`, default
arguments): the values saved under the arguments, the new stack, and whether its gas is charged. -/
theorem VM.run_callComputeStacks (st : VmState) (stack captured : Stack) (nargs : Int) :
    ExceptT.run (VM.callComputeStacks stack captured nargs (-1)) st =
      if 0 ≤ nargs ∧ stack.size < nargs.toNat then (.error .stkUnd, st)
      else (.ok (if 0 ≤ nargs then stack.take (stack.size - nargs.toNat) else #[],
                 captured ++ (if 0 ≤ nargs then stack.extract (stack.size - nargs.toNat) stack.size else stack),
                 !(captured.isEmpty && decide (nargs < 0))), st) := by
  unfold VM.callComputeStacks
  by_cases h1 : 0 ≤ nargs
  · have hn : ¬ nargs < 0 := by omega
    by_cases h2 : stack.size < nargs.toNat
    · have h2' : (stack.size : Int) < nargs := by omega
      simp [h1, h2, h2', VM.run_bind, VM.run_throw]
    · have h2' : ¬ (stack.size : Int) < nargs := by omega
      have h2'' : ¬ nargs.toNat > stack.size := by omega
      by_cases h3 : captured.isEmpty = true
      · have hc : captured = #[] := by simpa using h3
        subst hc
        simp [h1, h2, h2', h2'', hn, VM.run_bind, VM.run_pure]
      · simp [h1, h2, h2', h2'', h3, hn, VM.run_bind, VM.run_pure]
  · have h2' : ¬ (stack.size : Int) < nargs := by omega
    have hn : nargs < 0 := by omega
    by_cases h3 : captured.isEmpty = true
    · have hc : captured = #[] := by simpa using h3
      subst hc
      simp [h1, h2', hn, VM.run_bind, VM.run_pure]
    · simp [h1, h2', h3, hn, VM.run_bind, VM.run_pure]

theorem VM.run_call_ordinary_noC0 (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (cdata : OrdCdata) (hc0 : cregs.c0 = none) :
    ExceptT.run (VM.call (.ordinary code saved cregs cdata)) st =
      if 0 ≤ cdata.nargs ∧ st.stack.size < cdata.nargs.toNat then (.error .stkUnd, st)
      else (.ok (), { st.callClosure cdata with
              regs := { st.regs with c0 := st.retContWith (st.callSaved cdata) },
              cc := .ordinary code saved cregs OrdCdata.empty }) := by
  rcases cdata with ⟨cs, n⟩
  unfold VM.call
  simp only [VM.run_bind, VM.run_get, VM.bindRes_ok, hc0, Option.isSome_none, Bool.false_eq_true, if_false,
    ge_iff_le, decide_eq_true_eq]
  simp only [show ¬ (0 : Int) ≤ -1 by omega, decide_false, Bool.false_eq_true, if_false, VM.run_pure,
    VM.bindRes_ok]
  simp only [VM.run_bind, VM.run_pure, VM.bindRes_ok, VM.run_callComputeStacks]
  by_cases h : 0 ≤ n ∧ st.stack.size < n.toNat
  · simp only [h, and_self, if_true]
    rfl
  · simp only [h, if_false, VM.bindRes_ok, VM.run_set, VM.run_modify, VM.run_get, VM.run_bind]
    unfold VmState.callClosure VmState.callSaved VmState.retContWith VmState.closureArgs
    by_cases hn : 0 ≤ n
    · have hn' : ¬ n < 0 := by omega
      simp only [hn, hn', if_true, decide_false, Bool.and_false, Bool.not_false, and_false, if_false]
      simp [VM.run_bind, VM.run_set, VM.run_modify, VM.run_get, VM.bindRes_ok]
      rfl
    · have hn' : n < 0 := by omega
      by_cases hc : cs.isEmpty = true
      · have hc' : cs = #[] := by simpa using hc
        subst hc'
        simp [hn, hn', VM.run_bind, VM.run_set, VM.run_modify, VM.run_get, VM.bindRes_ok]
        rfl
      · simp [hn, hn', hc, VM.run_bind, VM.run_set, VM.run_modify, VM.run_get, VM.bindRes_ok]
        rfl



/-- **A call of an ordinary continuation** (C++ `VmState::call`) with closure data: if it saved
`c0` the call is a jump; else stk_und if it takes more arguments than the stack has, else the
captured stack and the arguments on the stack (`VmState.callClosure`), the values under the
arguments saved in the return continuation (`VmState.retContWith`), which becomes `c0`, and the
continuation, without its closure data, current. -/
@[vm_run low] theorem VM.run_call_ordinary_cdata (st : VmState) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) :
    ExceptT.run (VM.call (.ordinary code saved cregs cdata)) st =
      if cregs.c0.isSome then ExceptT.run (VM.jump (.ordinary code saved cregs cdata)) st
      else if 0 ≤ cdata.nargs ∧ st.stack.size < cdata.nargs.toNat then (.error .stkUnd, st)
      else (.ok (), { st.callClosure cdata with
              regs := { st.regs with c0 := st.retContWith (st.callSaved cdata) },
              cc := .ordinary code saved cregs OrdCdata.empty }) := by
  cases hc0 : cregs.c0 with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, if_false]
    exact VM.run_call_ordinary_noC0 st code saved cregs cdata hc0
  | some k =>
    simp only [Option.isSome_some, if_true]
    unfold VM.call
    simp only [VM.run_bind, VM.run_get, VM.bindRes_ok, hc0, Option.isSome_some, if_true]
    simp only [show ¬ (0 : Int) ≤ -1 by omega, decide_false, Bool.false_eq_true, if_false]
    simp only [VM.run_bind, VM.run_pure, VM.bindRes_ok]

/-! `vm_run` writes out the stacks and the return continuation of a closure (on literal stacks they
compute). -/

attribute [vm_run] VmState.closureStack VmState.callClosure VmState.callSaved VmState.closureArgs
  VmState.retContWith

/-- The return continuation that saved no values is `VmState.retCont`. -/
@[vm_run] theorem VmState.retContWith_empty (st : VmState) : st.retContWith #[] = st.retCont := by
  unfold VmState.retContWith VmState.retCont
  cases st.cc <;> rfl

/-! ## `SETCONTARGS` -/

/-- `SETCONTARGS` runs as `ContTail.setContArgs` (the same code). -/
theorem ContTail.handler_eq (copy : Nat) (more : Int) (st : VmState) :
    ExceptT.run (execInstr (.setContArgs copy more)) st = ExceptT.run (ContTail.setContArgs copy more) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl


/-- `SETCONTARGS` of a continuation without closure data: the top `copyN` values captured, the
gas of the captured stack charged, `nargs` set to `more`. -/
theorem ContTail.run_ordArgs_empty (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (copyN : Nat) (more : Int) (h0 : 0 < copyN) (hm : -1 ≤ more) (hd : copyN ≤ st.stack.size) :
    ExceptT.run (ContTail.ordArgs code saved cregs OrdCdata.empty copyN more) st =
      ExceptT.run (VM.push (.cont (.ordinary code saved cregs
          { stack := st.stack.extract (st.stack.size - copyN) st.stack.size, nargs := more })))
        ({ st with stack := st.stack.take (st.stack.size - copyN) }.consumeStackGas copyN) := by
  unfold ContTail.ordArgs
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

/-- `SETCONTARGS copy,more` (C++ `exec_setcontargs`, contops.cpp:669) of an ordinary continuation
without closure data, `0 < copy`: the top `copy` values under it become its captured stack (their
stack gas charged), `more` the number of arguments it takes; stk_und if there are fewer. -/
@[vm_spec] theorem Spec.setContArgs_ord (st : VmState) (s : Stack) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (copy : Nat) (more : Int)
    (hs : st.stack = s.push (.cont (.ordinary code saved cregs OrdCdata.empty)))
    (hcopy : 0 < copy ∧ copy ≤ 15) (hmore : -1 ≤ more ∧ more ≤ 14) :
    ExceptT.run (execInstr (.setContArgs copy more)) st =
      if copy ≤ s.size then
        ExceptT.run (VM.push (.cont (.ordinary code saved cregs
            { stack := s.extract (s.size - copy) s.size, nargs := more })))
          ({ st with stack := s.take (s.size - copy) }.consumeStackGas copy)
      else (.error .stkUnd, st) := by
  have h1 : ¬ copy > 15 := by omega
  have h2 : ¬ (more < -1 ∨ more > 14) := by omega
  have h4 : ¬ (copy = 0 ∧ more = -1) := by omega
  have h2' : decide (more < -1 ∨ more > 14) = false := by simpa using h2
  rw [ContTail.handler_eq]
  simp only [ContTail.setContArgs, h1, if_false, h2', Bool.false_eq_true, VM.run_bind, VM.run_get, VM.bindRes_ok,
    pure_bind]
  by_cases hdepth : copy ≤ s.size
  · rw [if_pos hdepth]
    have key := ContTail.run_ordArgs_empty { st with stack := s } code saved cregs copy more hcopy.1 hmore.1 hdepth
    simp only at key
    rw [← key]
    rw [if_neg (by rw [hs, Array.size_push]; omega)]
    simp only [VM.run_bind]
    have hpos : 0 < st.stack.size := by rw [hs, Array.size_push]; omega
    rw [VM.run_popCont, dif_pos hpos]
    have hb : st.stack.back hpos = .cont (.ordinary code saved cregs OrdCdata.empty) := by
      simp only [hs, VM.back_push]
    rw [hb]
    have hpop : st.stack.pop = s := by rw [hs, Array.pop_push]
    simp only [VM.bindRes_ok, h4, if_false, Continuation.forceCdata, hpop]
  · rw [if_neg hdepth, if_pos (by rw [hs, Array.size_push]; omega)]
    simp only [VM.run_bind, VM.run_throw, VM.bindRes_error]

end TvmLean

import TvmLean.Semantics
import TvmLean.Proofs.Exec.Attr

/-!
# The VM monad, run on a state

Every instruction is a program in `VM := ExceptT Excno (StateM VmState)`; the step runs it on a
state, `(exec i).run st : Except Excno Unit × VmState` (`VmState.instrStep`). The lemmas here compute
such runs from the definitions, one monad operation at a time, without evaluating anything: the
state may hold unknown values (a symbolic stack, unknown registers), and the result is a term in
them.

* the monad: `VM.run_pure`, `VM.run_bind`, `VM.run_get`, `VM.run_set`, `VM.run_modify`,
  `VM.run_throw`, and the control flow of `do` blocks (`VM.run_ite`, `VM.run_dite`). The result of
  a step is passed on by `VM.bindRes`, which distributes over the conditions of a
  run (`VM.bindRes_ite`): the cases of an instruction stay `if`s of its result.
* the stack primitives of `VM/Ops/Stack.lean` and `VM/Ops/Cells.lean` (`VM.push`, `VM.pop`, the
  typed pops, `VM.fetch`, `VM.swap`, `VM.checkUnderflow`, `VM.pushIntQuiet`, ...), each stated for
  any state: what it does follows from the stack (`st.stack`), so on a stack whose top is known
  (`s.push a`, the form `Array.push` gives) it computes by `simp` with the lemmas of `Array.push`
  below (`VM.back_push`, `VM.getElem!_push`, `VM.set!_push`, `VM.take_push`);
* the gas (`VM.run_consumeGas`), the jumps, calls and returns to continuations without closure
  data (`VM.run_jump_ordinary`, `VM.run_call_plain`, `VM.run_ret`), the exceptions an instruction
  raises (`VM.run_throwToHandler`), integers (`IntVal`).

The lemmas are in the simp set `vm_run`, which `vm_simp` uses (`Proofs/Exec/Eval.lean`).
-/

namespace TvmLean

variable {α β : Type}

/-! ## The monad -/

@[vm_run] theorem VM.run_pure (a : α) (st : VmState) : ExceptT.run (pure a : VM α) st = (.ok a, st) := rfl

/-- What a run continues with after `m` ran with result `r`: `f` on the value, or the exception
passed on (the `bind` of the monad on results). -/
def VM.bindRes (r : Except Excno α × VmState) (f : α → VM β) : Except Excno β × VmState :=
  match r with
  | (.ok a, st) => ExceptT.run (f a) st
  | (.error e, st) => (.error e, st)

@[vm_run] theorem VM.bindRes_ok (a : α) (st : VmState) (f : α → VM β) :
    VM.bindRes (.ok a, st) f = ExceptT.run (f a) st := rfl

@[vm_run] theorem VM.bindRes_error (e : Excno) (st : VmState) (f : α → VM β) :
    VM.bindRes (.error e, st) f = (.error e, st) := rfl

@[vm_run] theorem VM.bindRes_ite (c : Prop) [Decidable c] (x y : Except Excno α × VmState) (f : α → VM β) :
    VM.bindRes (if c then x else y) f = if c then VM.bindRes x f else VM.bindRes y f := by
  split <;> rfl

@[vm_run] theorem VM.bindRes_dite (c : Prop) [Decidable c] (x : c → Except Excno α × VmState)
    (y : ¬c → Except Excno α × VmState) (f : α → VM β) :
    VM.bindRes (if h : c then x h else y h) f = if h : c then VM.bindRes (x h) f else VM.bindRes (y h) f := by
  split <;> rfl

/-- `VM.bindRes_ite` for a run whose result is typed `Id _` (as `ExceptT.run` types it). -/
@[vm_run] theorem VM.bindRes_ite_id (c : Prop) [Decidable c] (x y : Id (Except Excno α × VmState)) (f : α → VM β) :
    VM.bindRes (@ite (Id (Except Excno α × VmState)) c _ x y) f = if c then VM.bindRes x f else VM.bindRes y f := by
  split <;> rfl

@[vm_run] theorem VM.bindRes_dite_id (c : Prop) [Decidable c] (x : c → Id (Except Excno α × VmState))
    (y : ¬c → Id (Except Excno α × VmState)) (f : α → VM β) :
    VM.bindRes (@dite (Id (Except Excno α × VmState)) c _ x y) f =
      if h : c then VM.bindRes (x h) f else VM.bindRes (y h) f := by
  split <;> rfl

@[vm_run] theorem VM.run_bind (m : VM α) (f : α → VM β) (st : VmState) :
    ExceptT.run (m >>= f) st = VM.bindRes (ExceptT.run m st) f := by
  show (ExceptT.bind m f).run st = _
  simp only [ExceptT.bind, ExceptT.run, ExceptT.mk, bind, StateT.bind, ExceptT.bindCont, VM.bindRes]
  rcases h : m st with ⟨r, st'⟩
  cases r <;> rfl

@[vm_run] theorem VM.run_get (st : VmState) : ExceptT.run (get : VM VmState) st = (.ok st, st) := rfl

@[vm_run] theorem VM.run_set (st st' : VmState) : ExceptT.run (set st' : VM PUnit) st = (.ok (), st') := rfl

@[vm_run] theorem VM.run_modify (f : VmState → VmState) (st : VmState) :
    ExceptT.run (modify f : VM PUnit) st = (.ok (), f st) := rfl

@[vm_run] theorem VM.run_modifyGet (f : VmState → α × VmState) (st : VmState) :
    ExceptT.run (modifyGet f : VM α) st = (.ok (f st).1, (f st).2) := rfl

@[vm_run] theorem VM.run_throw (e : Excno) (st : VmState) : ExceptT.run (throw e : VM α) st = (.error e, st) := rfl

@[vm_run] theorem VM.run_ite (c : Prop) [Decidable c] (a b : VM α) (st : VmState) :
    ExceptT.run (if c then a else b) st = if c then ExceptT.run a st else ExceptT.run b st := by
  split <;> rfl

@[vm_run] theorem VM.run_dite (c : Prop) [Decidable c] (a : c → VM α) (b : ¬c → VM α) (st : VmState) :
    ExceptT.run (if h : c then a h else b h) st = if h : c then ExceptT.run (a h) st else ExceptT.run (b h) st := by
  split <;> rfl

@[vm_run] theorem VM.run_map (f : α → β) (m : VM α) (st : VmState) :
    ExceptT.run (f <$> m) st = VM.bindRes (ExceptT.run m st) (fun a => pure (f a)) := by
  show ExceptT.run (m >>= fun a => pure (f a)) st = _
  rw [VM.run_bind]

/-- The result of a run, by cases (for `split` on a run whose result is not known). -/
theorem VM.run_eta (m : VM α) (st : VmState) : ExceptT.run m st = ((ExceptT.run m st).1, (ExceptT.run m st).2) := rfl

/-! ## The stack primitives -/

@[vm_run] theorem VM.run_push (v : Value) (st : VmState) :
    ExceptT.run (VM.push v) st = (.ok (), { st with stack := st.stack.push v }) := rfl

@[vm_run] theorem VM.run_pop (st : VmState) :
    ExceptT.run VM.pop st =
      if h : 0 < st.stack.size then (.ok (st.stack.back h), { st with stack := st.stack.pop })
      else (.error .stkUnd, st) := by
  simp only [VM.pop, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_dite, VM.run_modify, VM.run_pure,
    VM.run_throw]

@[vm_run] theorem VM.run_popInt (st : VmState) :
    ExceptT.run VM.popInt st =
      if h : 0 < st.stack.size then
        match st.stack.back h with
        | .int i => (.ok i, { st with stack := st.stack.pop })
        | _ => (.error .typeChk, { st with stack := st.stack.pop })
      else (.error .stkUnd, st) := by
  unfold VM.popInt
  rw [VM.run_bind, VM.run_pop]
  by_cases h : 0 < st.stack.size
  · simp only [dif_pos h, VM.bindRes_ok]
    generalize st.stack.back h = v
    cases v <;> rfl
  · simp only [dif_neg h, VM.bindRes_error]

@[vm_run] theorem VM.run_popCont (st : VmState) :
    ExceptT.run VM.popCont st =
      if h : 0 < st.stack.size then
        match st.stack.back h with
        | .cont k => (.ok k, { st with stack := st.stack.pop })
        | _ => (.error .typeChk, { st with stack := st.stack.pop })
      else (.error .stkUnd, st) := by
  unfold VM.popCont
  rw [VM.run_bind, VM.run_pop]
  by_cases h : 0 < st.stack.size
  · simp only [dif_pos h, VM.bindRes_ok]
    generalize st.stack.back h = v
    cases v <;> rfl
  · simp only [dif_neg h, VM.bindRes_error]

@[vm_run] theorem VM.run_popCell (st : VmState) :
    ExceptT.run VM.popCell st =
      if h : 0 < st.stack.size then
        match st.stack.back h with
        | .cell c => (.ok c, { st with stack := st.stack.pop })
        | _ => (.error .typeChk, { st with stack := st.stack.pop })
      else (.error .stkUnd, st) := by
  unfold VM.popCell
  rw [VM.run_bind, VM.run_pop]
  by_cases h : 0 < st.stack.size
  · simp only [dif_pos h, VM.bindRes_ok]
    generalize st.stack.back h = v
    cases v <;> rfl
  · simp only [dif_neg h, VM.bindRes_error]

@[vm_run] theorem VM.run_popSlice (st : VmState) :
    ExceptT.run VM.popSlice st =
      if h : 0 < st.stack.size then
        match st.stack.back h with
        | .slice s => (.ok s, { st with stack := st.stack.pop })
        | _ => (.error .typeChk, { st with stack := st.stack.pop })
      else (.error .stkUnd, st) := by
  unfold VM.popSlice
  rw [VM.run_bind, VM.run_pop]
  by_cases h : 0 < st.stack.size
  · simp only [dif_pos h, VM.bindRes_ok]
    generalize st.stack.back h = v
    cases v <;> rfl
  · simp only [dif_neg h, VM.bindRes_error]

@[vm_run] theorem VM.run_popBuilder (st : VmState) :
    ExceptT.run VM.popBuilder st =
      if h : 0 < st.stack.size then
        match st.stack.back h with
        | .builder b => (.ok b, { st with stack := st.stack.pop })
        | _ => (.error .typeChk, { st with stack := st.stack.pop })
      else (.error .stkUnd, st) := by
  unfold VM.popBuilder
  rw [VM.run_bind, VM.run_pop]
  by_cases h : 0 < st.stack.size
  · simp only [dif_pos h, VM.bindRes_ok]
    generalize st.stack.back h = v
    cases v <;> rfl
  · simp only [dif_neg h, VM.bindRes_error]

@[vm_run] theorem VM.run_popBool (st : VmState) :
    ExceptT.run VM.popBool st =
      if h : 0 < st.stack.size then
        match st.stack.back h with
        | .int (.num n) => (.ok (n ≠ 0), { st with stack := st.stack.pop })
        | .int .nan => (.error .intOv, { st with stack := st.stack.pop })
        | _ => (.error .typeChk, { st with stack := st.stack.pop })
      else (.error .stkUnd, st) := by
  unfold VM.popBool
  rw [VM.run_bind, VM.run_popInt]
  by_cases h : 0 < st.stack.size
  · simp only [dif_pos h]
    generalize st.stack.back h = v
    cases v with
    | int i => cases i <;> rfl
    | _ => rfl
  · simp only [dif_neg h, VM.bindRes_error]

@[vm_run] theorem VM.run_fetch (k : Nat) (st : VmState) :
    ExceptT.run (VM.fetch k) st =
      if k < st.stack.size then (.ok st.stack[st.stack.size - 1 - k]!, st) else (.error .stkUnd, st) := by
  simp only [VM.fetch, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_dite, VM.run_pure, VM.run_throw]
  split <;> simp_all

@[vm_run] theorem VM.run_swap (i j : Nat) (st : VmState) :
    ExceptT.run (VM.swap i j) st =
      if Nat.max i j < st.stack.size then
        (.ok (), { st with stack := (Array.set! (Array.set! st.stack (st.stack.size - 1 - i)
          st.stack[st.stack.size - 1 - j]!) (st.stack.size - 1 - j) st.stack[st.stack.size - 1 - i]!) })
      else (.error .stkUnd, st) := by
  simp only [VM.swap, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_dite, VM.run_modify, VM.run_throw]
  split <;> simp_all

@[vm_run] theorem VM.run_checkUnderflow (n : Nat) (st : VmState) :
    ExceptT.run (VM.checkUnderflow n) st = if st.stack.size < n then (.error .stkUnd, st) else (.ok (), st) := by
  simp only [VM.checkUnderflow, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_ite, VM.run_pure, VM.run_throw]

@[vm_run] theorem VM.run_pushIntQuiet (i : IntVal) (quiet : Bool) (st : VmState) :
    ExceptT.run (VM.pushIntQuiet i quiet) st =
      if i.signedFits257 then (.ok (), { st with stack := st.stack.push (.int i) })
      else if quiet then (.ok (), { st with stack := st.stack.push (.int .nan) })
      else (.error .intOv, st) := by
  cases i with
  | nan => cases quiet <;> rfl
  | num n =>
    simp only [VM.pushIntQuiet]
    by_cases h : (IntVal.num n).signedFits257 = true
    · simp only [h, if_true]; rfl
    · cases quiet <;> simp only [h, Bool.false_eq_true, if_false] <;> rfl

@[vm_run] theorem VM.run_pushSmallInt (n : Int) (st : VmState) :
    ExceptT.run (VM.pushSmallInt n) st = (.ok (), { st with stack := st.stack.push (.int (.num n)) }) := rfl

/-! ## Stacks of known top: `Array.push` -/

@[vm_run] theorem VM.back_push {α : Type} (s : Array α) (v : α) (h : 0 < (s.push v).size) : (s.push v).back h = v := by
  simp [Array.back_eq_getElem]

@[vm_run] theorem VM.getElem!_push {α : Type} [Inhabited α] (s : Array α) (v : α) (i : Nat) :
    (s.push v)[i]! = if i = s.size then v else s[i]! := by
  by_cases h : i = s.size
  · simp [h]
  · simp [h, getElem!_def, Array.getElem?_push]

@[vm_run] theorem VM.set!_push {α : Type} (s : Array α) (v w : α) (i : Nat) :
    (s.push v).set! i w = if i = s.size then s.push w else (s.set! i w).push v := by
  apply Array.ext_getElem?
  intro j
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hi : i = s.size
  · subst hi
    simp only [Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_push, if_true]
    by_cases hj : s.size = j
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  · simp only [hi, if_false, Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_push,
      Array.size_setIfInBounds]
    by_cases hj : j = s.size
    · subst hj; simp [hi]
    · simp only [hj, if_false]
      by_cases hij : i = j
      · subst hij
        by_cases hl : i < s.size
        · simp [hl, Nat.lt_succ_of_lt hl]
        · have : ¬ i < s.size + 1 := by omega
          simp [hl, this]
      · simp [hij]

@[vm_run] theorem VM.size_singleton {α : Type} (a : α) : #[a].size = 1 := rfl

@[vm_run] theorem VM.getElem!_singleton {α : Type} [Inhabited α] (a : α) : #[a][0]! = a := rfl

@[vm_run] theorem VM.size_set! {α : Type} (s : Array α) (i : Nat) (v : α) : (s.set! i v).size = s.size := by
  simp [Array.set!_eq_setIfInBounds]

@[vm_run] theorem VM.take_push {α : Type} (s : Array α) (v : α) (k : Nat) :
    (s.push v).take k = if k ≤ s.size then s.take k else s.push v := by
  apply Array.ext_getElem?
  intro j
  by_cases hk : k ≤ s.size
  · simp only [hk, if_true, Array.take_eq_extract, Array.getElem?_extract, Array.getElem?_push, Array.size_push]
    by_cases hj : j < k
    · have : j ≠ s.size := by omega
      have h3 : j < min k (s.size + 1) := by omega
      have h4 : j < min k s.size := by omega
      simp [this, h3, h4]
    · have h3 : ¬ j < min k (s.size + 1) := by omega
      have h4 : ¬ j < min k s.size := by omega
      simp [h3, h4]
  · simp only [hk, if_false, Array.take_eq_extract, Array.getElem?_extract, Array.getElem?_push, Array.size_push]
    by_cases hj : j < s.size + 1
    · have h3 : j < min k (s.size + 1) := by omega
      simp [h3]
    · have h3 : ¬ j < min k (s.size + 1) := by omega
      have h1 : j ≠ s.size := by omega
      have h2 : s[j]? = none := by simp; omega
      simp [h3, h1, h2]

@[vm_run] theorem VM.take_size {α : Type} (s : Array α) : s.take s.size = s := by
  simp

@[vm_run] theorem VM.natMax_zero_left (a : Nat) : Nat.max 0 a = a := by simp

@[vm_run] theorem VM.natMax_zero_right (a : Nat) : Nat.max a 0 = a := by simp

@[vm_run] theorem VM.natMax_lt (a b c : Nat) : Nat.max a b < c ↔ a < c ∧ b < c := by
  simp only [Nat.max_def]; split <;> omega

/-! ## Gas -/

@[vm_run] theorem VM.run_consumeGas (amount : Int) (st : VmState) :
    ExceptT.run (VM.consumeGas amount) st =
      if (st.consumeGas amount).gasExhaustedNow then (.error .outOfGas, st.consumeGas amount)
      else (.ok (), st.consumeGas amount) := by
  simp only [VM.consumeGas, VM.run_bind, VM.run_modify, VM.bindRes_ok, VM.run_get, VM.run_ite, VM.run_throw,
    VM.run_pure]

/-! ## Jumps, calls, returns, exceptions -/

/-- The return continuation `VM.call` installs as `c0` (C++ `VmState::call`, the return
continuation of the current code with the old `c0` saved, `ControlData.save.c0`). -/
def VmState.retCont (st : VmState) : Continuation :=
  match st.cc with
  | .ordinary code _ _ _ => .ordinary code (.quit 0) { OrdCregs.empty with c0 := some st.regs.c0 } OrdCdata.empty
  | _ => .quit 0

/-- `VM.jump` to an ordinary continuation without closure data (C++ `VmState::jump`,
`adjust_jump_cont` leaves the stack): it becomes the current continuation. -/
@[vm_run] theorem VM.run_jump_ordinary (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs) :
    ExceptT.run (VM.jump (.ordinary code saved cregs OrdCdata.empty)) st =
      (.ok (), { st with cc := .ordinary code saved cregs OrdCdata.empty }) := by
  simp [VM.jump, OrdCdata.empty, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

@[vm_run] theorem VM.run_jump_envelope (st : VmState) (ext : Continuation) (cregs : OrdCregs) :
    ExceptT.run (VM.jump (.envelope ext cregs OrdCdata.empty)) st =
      (.ok (), { st with cc := .envelope ext cregs OrdCdata.empty }) := by
  simp [VM.jump, OrdCdata.empty, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

@[vm_run] theorem VM.run_jump_quit (st : VmState) (n : Int) :
    ExceptT.run (VM.jump (.quit n)) st = (.ok (), { st with cc := .quit n }) := by
  simp [VM.jump, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

@[vm_run] theorem VM.run_jump_excQuit (st : VmState) :
    ExceptT.run (VM.jump .excQuit) st = (.ok (), { st with cc := .excQuit }) := by
  simp [VM.jump, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_modify]

/-- `VM.call` of an ordinary continuation without saved registers or closure data (C++
`VmState::call`): the return continuation (`VmState.retCont`) becomes `c0`, the continuation the
current one. -/
@[vm_run] theorem VM.run_call_plain (st : VmState) (code : Slice) (saved : Continuation) :
    ExceptT.run (VM.call (.ordinary code saved OrdCregs.empty OrdCdata.empty)) st =
      (.ok (), { st with regs := { st.regs with c0 := st.retCont }
                         cc := .ordinary code saved OrdCregs.empty OrdCdata.empty }) := by
  simp [VM.call, VM.callComputeStacks, OrdCdata.empty, OrdCregs.empty, VM.run_bind, VM.run_get, VM.bindRes_ok,
    VmState.retCont]
  split
  · omega
  · simp [VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_pure, VM.run_set]
    split <;> simp_all

/-- The state an exception makes (C++ `VmState::throw_exception`): the stack `[0, n]`, on the
`push` form the stack lemmas compute with, and `c2` the current continuation. -/
@[vm_run] theorem VM.throwException_eq (st : VmState) (e : Int) :
    st.throwException e = { st with stack := (#[].push (.int (.num 0))).push (.int (.num e)), cc := st.regs.c2 } := rfl

/-- `VM.throwException_eq` with an argument. -/
@[vm_run] theorem VM.throwExceptionArg_eq (st : VmState) (e : Int) (arg : Value) :
    st.throwExceptionArg e arg = { st with stack := (#[].push arg).push (.int (.num e)), cc := st.regs.c2 } := rfl

@[vm_run] theorem VM.jumpTo_eq (st : VmState) (k : Continuation) : st.jumpTo k = { st with cc := k } := rfl

/-- `VM.ret` (C++ `VmState::ret`): `c0` becomes `quit 0` and the VM jumps to the old `c0`. -/
@[vm_run] theorem VM.run_ret (st : VmState) :
    ExceptT.run (VM.ret) st = ExceptT.run (VM.jump st.regs.c0) { st with regs := { st.regs with c0 := .quit 0 } } := by
  simp [VM.ret, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_set]

/-- An exception raised by an instruction (C++ `VmState::throw_exception`): the state `raise`
makes (the exception's stack, `c2` the current continuation) is charged the exception gas (out of
gas at once), and the jump to the handler fails with stk_und if it expects more arguments. -/
@[vm_run] theorem VM.run_throwToHandler (raise : VmState → VmState) (st : VmState) :
    ExceptT.run (VM.throwToHandler raise) st =
      if ((raise st).consumeGas exceptionGasPrice).gasExhaustedNow then
        (.error .outOfGas, (raise st).consumeGas exceptionGasPrice)
      else if ((raise st).consumeGas exceptionGasPrice).excHandlerNeedsMoreArgs then
        (.error .stkUnd, (raise st).consumeGas exceptionGasPrice)
      else (.ok (), (raise st).consumeGas exceptionGasPrice) := by
  simp only [VM.throwToHandler, VM.run_bind, VM.run_modify, VM.bindRes_ok, VM.run_consumeGas]
  split
  · simp [VM.bindRes_error]
  · simp only [VM.bindRes_ok, VM.run_bind, VM.run_get, VM.run_ite, VM.run_throw, VM.run_pure]

/-! ## Integers -/

@[vm_run] theorem VM.intVal_add_num (a b : Int) : (IntVal.num a).add (.num b) = .num (a + b) := rfl
@[vm_run] theorem VM.intVal_sub_num (a b : Int) : (IntVal.num a).sub (.num b) = .num (a - b) := rfl
@[vm_run] theorem VM.intVal_mul_num (a b : Int) : (IntVal.num a).mul (.num b) = .num (a * b) := rfl
@[vm_run] theorem VM.intVal_inc_num (a : Int) : (IntVal.num a).inc = .num (a + 1) := rfl
@[vm_run] theorem VM.intVal_dec_num (a : Int) : (IntVal.num a).dec = .num (a - 1) := rfl
@[vm_run] theorem VM.intVal_add_nan (x : IntVal) : IntVal.nan.add x = .nan := rfl
@[vm_run] theorem VM.intVal_sub_nan (x : IntVal) : IntVal.nan.sub x = .nan := rfl
@[vm_run] theorem VM.intVal_inc_nan : IntVal.nan.inc = .nan := rfl
@[vm_run] theorem VM.intVal_dec_nan : IntVal.nan.dec = .nan := rfl

/-- A finite integer fits 257 bits (C++ `signed_fits_bits(257)`): `-2^256 ≤ n < 2^256`. -/
@[vm_run] theorem VM.intVal_signedFits257_num (n : Int) :
    (IntVal.num n).signedFits257 = decide (-2 ^ 256 ≤ n ∧ n < 2 ^ 256) := rfl

@[vm_run] theorem VM.intVal_signedFits257_nan : IntVal.nan.signedFits257 = false := rfl

@[vm_run] theorem VM.fst_pair {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl
@[vm_run] theorem VM.snd_pair {α β : Type} (a : α) (b : β) : (a, b).2 = b := rfl

@[vm_run] theorem VM.intPow2_eq (n : Nat) : intPow2 n = 2 ^ n := rfl

/-- The complement of an integer (exit codes are complemented, `~~~ n`). -/
@[vm_run] theorem VM.int_complement (n : Int) : ~~~ n = -n - 1 := by
  show Int.not n = _
  cases n with
  | ofNat k => simp [Int.not]; omega
  | negSucc k => simp [Int.not, Int.negSucc_eq]

end TvmLean

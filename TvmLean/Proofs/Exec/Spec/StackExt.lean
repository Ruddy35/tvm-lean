import TvmLean.Proofs.Exec.Eval
import TvmLean.Proofs.Exec.Spec.Stack

/-!
# Specifications: the rest of stack manipulation

In the format of `Proofs/Exec/Spec/Stack.lean`. The instructions with immediate arguments are
specified for any stack, with the values at a depth (`Stack.at`) and the exchange of two depths
(`Stack.exchange`, what `VM.swap` does), as `XCPU` there; the common ones also for the shape they
take (`2DUP`, `2OVER`, `2SWAP`, `TUCK`, `-ROT`, `2DROP`). A count taken from the stack (`PICK`,
`XCHGX`, `ONLYX`, `CHKDEPTH`, ...) is an integer `n`: range_chk if it is negative or above the
limit of the global version (`2^30 - 1` from version 4, 255 before; C++ `pop_smallint_range`).

* `PUSH2`, `PUSH3`, `XCHG s(x),s(y)`, `XCHG s1,s(k)`, `XCHG2`, `XCHG3`, `XC2PU`, `XCPUXC`, `XCPU2`,
  `PUXC`, `PUXC2`, `PUXCPU`, `PU2XC`, `2DUP`, `2OVER`, `2SWAP`, `TUCK`, `-ROT`, `2DROP`,
  `BLKSWAP`, `BLKDROP2`, `DEPTH`, `PUSHPOW2DEC`, `PUSHNEGPOW2`, `NOP`;
* `PICK`, `XCHGX`, `CHKDEPTH`, `ONLYX`, `DROPX`, `ONLYTOPX`, `ROLL`, `-ROLL`;
* the loops: `BLKPUSH`, `REVERSE`, `ROLL`, `-ROLL` as folds over `List.range'` of the step of the
  handler (`VM.run_forIn_stack`), which `simp` computes for a literal count.

The exchanges of `PU2XC` are proved without the lemmas of `Array.push` (`stack_simp'`): with them
the contextual `simp` of `vm_simp` splits on the coincidence of depths and loops.
-/

namespace TvmLean

/-- The stack `s` with the values at depths `i` and `j` exchanged: what `VM.swap i j` makes of it
(C++ `Stack::swap`, the entry at depth `i` set first). -/
abbrev Stack.exchange (s : Stack) (i j : Nat) : Stack :=
  (s.set! (s.size - 1 - i) (s.at j)).set! (s.size - 1 - j) (s.at i)

/-- `Stack.exchange` unfolded, for `vm_run` to compute it on a stack of known top (`VM.set!_push`
applies to the inner `set!`, which the abbreviation hides from `simp`). -/
@[vm_run] theorem Stack.exchange_eq (s : Stack) (i j : Nat) :
    s.exchange i j = (s.set! (s.size - 1 - i) (s.at j)).set! (s.size - 1 - j) (s.at i) := rfl

/-- A loop over `l` whose body maps the stack by `f i` and goes on, as long as `P` holds of the
stack: its run is the fold of `f` over `l`. -/
theorem VM.run_forIn_stack (l : List Nat) (b : Nat → PUnit → VM (ForInStep PUnit))
    (f : Nat → Stack → Stack) (P : Stack → Prop) (hP : ∀ i ∈ l, ∀ s, P s → P (f i s))
    (hb : ∀ i ∈ l, ∀ (st : VmState), P st.stack →
      ExceptT.run (b i PUnit.unit) st = (.ok (.yield PUnit.unit), { st with stack := f i st.stack }))
    (st : VmState) (h : P st.stack) :
    ExceptT.run (forIn l PUnit.unit b) st =
      (.ok PUnit.unit, { st with stack := l.foldl (fun s i => f i s) st.stack }) := by
  induction l generalizing st with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons, VM.run_bind, hb i (List.mem_cons_self ..) st h, VM.bindRes_ok]
    exact ih (fun j hj => hP j (List.mem_cons_of_mem _ hj)) (fun j hj => hb j (List.mem_cons_of_mem _ hj))
      { st with stack := f i st.stack } (hP i (List.mem_cons_self ..) _ h)

/-- The loop of `ROLL` (C++ `exec_roll`): the exchanges of the depths `x-1-i` and `x-i`, `i < x`. -/
theorem VM.run_roll_loop (x : Nat) (st : VmState) (h : x < st.stack.size) :
    ExceptT.run (forIn [:x] PUnit.unit fun i _ => do
        VM.swap (x - 1 - i) (x - 1 - i + 1)
        pure (ForInStep.yield PUnit.unit)) st =
      (.ok PUnit.unit,
        { st with stack := (List.range' 0 x).foldl (fun a i => a.exchange (x - 1 - i) (x - 1 - i + 1)) st.stack }) := by
  rw [Std.Range.forIn_eq_forIn_range',
    VM.run_forIn_stack _ _ (fun i a => a.exchange (x - 1 - i) (x - 1 - i + 1)) (fun a => a.size = st.stack.size)
      (by intro i _ a h; simp [h]) (by intro i hi st' h'; simp at hi; vm_simp [h', Stack.exchange, Stack.at]) _ rfl]
  simp [Std.Range.size]

/-- The loop of `ROLLREV` (C++ `exec_rollrev`): the exchanges of the depths `i` and `i+1`,
`i < x`. -/
theorem VM.run_rollRev_loop (x : Nat) (st : VmState) (h : x < st.stack.size) :
    ExceptT.run (forIn [:x] PUnit.unit fun i _ => do
        VM.swap i (i + 1)
        pure (ForInStep.yield PUnit.unit)) st =
      (.ok PUnit.unit, { st with stack := (List.range' 0 x).foldl (fun a i => a.exchange i (i + 1)) st.stack }) := by
  rw [Std.Range.forIn_eq_forIn_range',
    VM.run_forIn_stack _ _ (fun i a => a.exchange i (i + 1)) (fun a => a.size = st.stack.size)
      (by intro i _ a h; simp [h]) (by intro i hi st' h'; simp at hi; vm_simp [h', Stack.exchange, Stack.at]) _ rfl]
  simp [Std.Range.size]

namespace Spec

set_option linter.unusedSimpArgs false

/-- The index of the depth `k`, `size - 1 - k`, as the model's fetches after pushes leave it. -/
theorem sub_one_sub (n k : Nat) : n - 1 - k = n - (k + 1) := by omega

/-- The size of a stack chosen by a condition (an exchange of the top with a depth that may be
0). -/
theorem size_ite {α : Type} (c : Prop) [Decidable c] (a b : Array α) :
    (if c then a else b).size = if c then a.size else b.size := by
  split <;> rfl

/-- `vm_simp` with the depths of `Stack.at` and `Stack.exchange` unfolded and their index
arithmetic normalized (`size - 1 - k` and `size - (k + 1)` alike). -/
local macro "stack_simp" : tactic =>
  `(tactic| vm_simp [Stack.at, Stack.exchange, sub_one_sub, size_ite, ite_self, and_assoc])

/-- The run of the handler, the stacks it makes left as `push`, `set!` and reads of the stacks
before (`Stack.exchange`, `Stack.at` unfolded alike on both sides): for the instructions whose
exchanges `vm_simp` would split on the coincidence of depths (its contextual `simp` then loops). -/
local macro "stack_simp'" : tactic =>
  `(tactic| simp (config := { contextual := true }) (disch := vm_disch) only [TvmLean.Exec.reduceExecInstrRun,
    VM.run_bind, VM.run_get, VM.bindRes_ok, VM.bindRes_error, VM.bindRes_ite, VM.run_fetch, VM.run_push,
    VM.run_swap, VM.run_pure, VM.run_throw, VM.run_ite, Stack.exchange, Stack.at, Array.size_push,
    VM.size_set!, VM.natMax_lt, if_pos, if_neg, Bool.and_eq_true, decide_eq_true_eq, and_assoc])

/-! ## Immediate arguments -/

/-- `PUSH2 s(x),s(y)` (C++ `exec_push2`): the values at depths `x` and `y` are pushed. -/
@[vm_spec] theorem push2 (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.push2 x y)) st =
      if x < st.stack.size ∧ y < st.stack.size then
        (.ok (), { st with stack := (st.stack.push (st.stack.at x)).push (st.stack.at y) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `PUSH3 s(x),s(y),s(z)` (C++ `exec_push3`): the values at depths `x`, `y`, `z` are pushed. -/
@[vm_spec] theorem push3 (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.push3 x y z)) st =
      if x < st.stack.size ∧ y < st.stack.size ∧ z < st.stack.size then
        (.ok (), { st with stack := ((st.stack.push (st.stack.at x)).push (st.stack.at y)).push (st.stack.at z) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `XCHG s(x),s(y)` (C++ `exec_xchg`, `0 < x < y`): the values at depths `x` and `y` are
exchanged; inv_opcode for other arguments. -/
@[vm_spec] theorem xchg (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.xchg x y)) st =
      if x = 0 ∨ y ≤ x then (.error .invOpcode, st)
      else if y < st.stack.size then (.ok (), { st with stack := st.stack.exchange x y })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `XCHG s1,s(k)` (C++ `exec_xchg1`). -/
@[vm_spec] theorem xchg1 (st : VmState) (k : Nat) :
    ExceptT.run (execInstr (.xchg1 k)) st =
      if 1 < st.stack.size ∧ k < st.stack.size then (.ok (), { st with stack := st.stack.exchange 1 k })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `XCHG2 s(x),s(y)` (C++ `exec_xchg2`): `XCHG s1,s(x)`, then `XCHG s0,s(y)`. -/
@[vm_spec] theorem xchg2 (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.xchg2 x y)) st =
      if x < st.stack.size ∧ y < st.stack.size ∧ 1 < st.stack.size then
        (.ok (), { st with stack := (st.stack.exchange 1 x).exchange 0 y })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `XCHG3 s(x),s(y),s(z)` (C++ `exec_xchg3`): `XCHG s2,s(x)`, `XCHG s1,s(y)`, `XCHG s0,s(z)`. -/
@[vm_spec] theorem xchg3 (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.xchg3 x y z)) st =
      if x < st.stack.size ∧ y < st.stack.size ∧ z < st.stack.size ∧ 2 < st.stack.size then
        (.ok (), { st with stack := ((st.stack.exchange 2 x).exchange 1 y).exchange 0 z })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `XC2PU s(x),s(y),s(z)` (C++ `exec_xc2pu`): `XCHG2 s(x),s(y)`, then `PUSH s(z)`. -/
@[vm_spec] theorem xc2pu (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.xc2pu x y z)) st =
      if x < st.stack.size ∧ y < st.stack.size ∧ z < st.stack.size ∧ 1 < st.stack.size then
        let s1 := (st.stack.exchange 1 x).exchange 0 y
        (.ok (), { st with stack := s1.push (s1.at z) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `XCPUXC s(x),s(y),s(z-1)` (C++ `exec_xcpuxc`): `XCHG s1,s(x)`, `PUSH s(y)`, `SWAP`,
`XCHG s0,s(z)`. -/
@[vm_spec] theorem xcpuxc (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.xcpuxc x y z)) st =
      if x < st.stack.size ∧ y < st.stack.size ∧ 1 < st.stack.size ∧ z ≤ st.stack.size then
        let s1 := st.stack.exchange 1 x
        (.ok (), { st with stack := Stack.exchange (Stack.exchange (s1.push (s1.at y)) 0 1) 0 z })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `XCPU2 s(x),s(y),s(z)` (C++ `exec_xcpu2`): `XCHG s0,s(x)`, then `PUSH2 s(y),s(z)`. -/
@[vm_spec] theorem xcpu2 (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.xcpu2 x y z)) st =
      if x < st.stack.size ∧ y < st.stack.size ∧ z < st.stack.size then
        let s1 := st.stack.exchange 0 x
        (.ok (), { st with stack := (s1.push (s1.at y)).push (s1.at z) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `PUXC s(x),s(y-1)` (C++ `exec_puxc`): `PUSH s(x)`, `SWAP`, `XCHG s0,s(y)`. -/
@[vm_spec] theorem puxc (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.puxc x y)) st =
      if x < st.stack.size ∧ y ≤ st.stack.size then
        (.ok (), { st with stack := Stack.exchange (Stack.exchange (st.stack.push (st.stack.at x)) 0 1) 0 y })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `PUXC2 s(x),s(y-1),s(z-1)` (C++ `exec_puxc2`): `PUSH s(x)`, `XCHG s0,s2`, `XCHG2 s(y),s(z)`. -/
@[vm_spec] theorem puxc2 (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.puxc2 x y z)) st =
      if x < st.stack.size ∧ 1 < st.stack.size ∧ y ≤ st.stack.size ∧ z ≤ st.stack.size then
        let s1 := Stack.exchange (st.stack.push (st.stack.at x)) 0 2
        (.ok (), { st with stack := (s1.exchange 1 y).exchange 0 z })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `PUXCPU s(x),s(y-1),s(z-1)` (C++ `exec_puxcpu`): `PUXC s(x),s(y-1)`, then `PUSH s(z)`. -/
@[vm_spec] theorem puxcpu (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.puxcpu x y z)) st =
      if x < st.stack.size ∧ y ≤ st.stack.size ∧ z ≤ st.stack.size then
        let s1 := Stack.exchange (Stack.exchange (st.stack.push (st.stack.at x)) 0 1) 0 y
        (.ok (), { st with stack := s1.push (s1.at z) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `PU2XC s(x),s(y-1),s(z-2)` (C++ `exec_pu2xc`): `PUSH s(x)`, `SWAP`, `PUSH s(y)`, `SWAP`,
`XCHG s0,s(z)`. -/
@[vm_spec] theorem pu2xc (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.pu2xc x y z)) st =
      if x < st.stack.size ∧ y ≤ st.stack.size ∧ z ≤ st.stack.size + 1 then
        let s1 := Stack.exchange (st.stack.push (st.stack.at x)) 0 1
        (.ok (), { st with stack := Stack.exchange (Stack.exchange (s1.push (s1.at y)) 0 1) 0 z })
      else (.error .stkUnd, st) := by
  stack_simp'

/-- `2DUP` (C++ `exec_dup2`): the values at depths 1 and 0 are pushed. -/
@[vm_spec] theorem twoDup (st : VmState) :
    ExceptT.run (execInstr .twoDup) st =
      if 1 < st.stack.size then (.ok (), { st with stack := (st.stack.push (st.stack.at 1)).push (st.stack.at 0) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `2OVER` (C++ `exec_over2`): the values at depths 3 and 2 are pushed. -/
@[vm_spec] theorem twoOver (st : VmState) :
    ExceptT.run (execInstr .twoOver) st =
      if 3 < st.stack.size then (.ok (), { st with stack := (st.stack.push (st.stack.at 3)).push (st.stack.at 2) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `2SWAP` (C++ `exec_swap2`): `XCHG s1,s3`, `XCHG s0,s2`. -/
@[vm_spec] theorem twoSwap (st : VmState) :
    ExceptT.run (execInstr .twoSwap) st =
      if 3 < st.stack.size then (.ok (), { st with stack := (st.stack.exchange 1 3).exchange 0 2 })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `TUCK` (C++ `exec_tuck`): `SWAP`, then `PUSH s1`. -/
@[vm_spec] theorem tuck (st : VmState) :
    ExceptT.run (execInstr .tuck) st =
      if 1 < st.stack.size then
        let s1 := st.stack.exchange 0 1
        (.ok (), { st with stack := s1.push (s1.at 1) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `-ROT` = `ROTREV` (C++ `exec_rotrev`): `SWAP`, `XCHG s1,s2`. -/
@[vm_spec] theorem rotRev (st : VmState) :
    ExceptT.run (execInstr .rotRev) st =
      if 2 < st.stack.size then (.ok (), { st with stack := (st.stack.exchange 0 1).exchange 1 2 })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `2DROP` (C++ `exec_drop2`): the top two values are dropped. -/
@[vm_spec] theorem drop2 (st : VmState) :
    ExceptT.run (execInstr .drop2) st =
      if 2 ≤ st.stack.size then (.ok (), { st with stack := st.stack.take (st.stack.size - 2) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `BLKSWAP x,y` (C++ `exec_blkswap`): the block of the `x` values below the top `y` and the block
of the top `y` change places. -/
@[vm_spec] theorem blkSwap (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.blkSwap x y)) st =
      if x + y ≤ st.stack.size then
        let n := st.stack.size
        (.ok (), { st with stack := st.stack.take (n - (x + y)) ++ st.stack.extract (n - y) n ++
                                     st.stack.extract (n - (x + y)) (n - y) })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `BLKDROP2 x,y` (C++ `exec_blkdrop2`): the `x` values below the top `y` are dropped. -/
@[vm_spec] theorem blkdrop2 (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.blkdrop2 x y)) st =
      if x + y ≤ st.stack.size then
        let n := st.stack.size
        (.ok (), { st with stack := st.stack.take (n - (x + y)) ++ st.stack.extract (n - (x + y) + x) n })
      else (.error .stkUnd, st) := by
  stack_simp

/-- `DEPTH` (C++ `exec_depth`): the depth of the stack is pushed. -/
@[vm_spec] theorem depth (st : VmState) :
    ExceptT.run (execInstr .depth) st =
      (.ok (), { st with stack := st.stack.push (.int (.num st.stack.size)) }) := by
  stack_simp

/-- `PUSHPOW2DEC e` (C++ `exec_push_pow2dec`): `2^e - 1`. -/
@[vm_spec] theorem pushPow2Dec (st : VmState) (e : Nat) :
    ExceptT.run (execInstr (.pushPow2Dec e)) st =
      if -2 ^ 256 ≤ (2 : Int) ^ e - 1 ∧ (2 : Int) ^ e - 1 < 2 ^ 256 then
        (.ok (), { st with stack := st.stack.push (.int (.num (2 ^ e - 1))) })
      else (.error .intOv, st) := by
  stack_simp

/-- `PUSHNEGPOW2 e` (C++ `exec_push_negpow2`): `-2^e`. -/
@[vm_spec] theorem pushNegPow2 (st : VmState) (e : Nat) :
    ExceptT.run (execInstr (.pushNegPow2 e)) st =
      if -2 ^ 256 ≤ -(2 : Int) ^ e ∧ -(2 : Int) ^ e < 2 ^ 256 then
        (.ok (), { st with stack := st.stack.push (.int (.num (-2 ^ e))) })
      else (.error .intOv, st) := by
  stack_simp

/-- `NOP` (C++ `exec_nop`). -/
@[vm_spec] theorem nop (st : VmState) : ExceptT.run (execInstr .nop) st = (.ok (), st) := by
  stack_simp

/-! ## Counts on the stack -/

/-- `PICK` = `PUSHX` (C++ `exec_pick`): the count `n` on top; the value at depth `n` of the rest is
pushed. -/
@[vm_spec] theorem pick (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .pick) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < n.toNat then (.error .rangeChk, { st with stack := s })
      else if n.toNat < s.size then (.ok (), { st with stack := s.push (s.at n.toNat) })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Stack.at, Nat.shiftLeft_eq]

/-- `XCHGX` (C++ `exec_xchg_x`): the count `n` on top; the top of the rest and its value at depth
`n` are exchanged. -/
@[vm_spec] theorem xchgX (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .xchgX) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < n.toNat then (.error .rangeChk, { st with stack := s })
      else if n.toNat < s.size then (.ok (), { st with stack := s.exchange 0 n.toNat })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Stack.at, Stack.exchange, Nat.shiftLeft_eq]

/-- `CHKDEPTH` (C++ `exec_chkdepth`): the count `n` on top; stk_und unless the rest has `n`
values. -/
@[vm_spec] theorem chkDepth (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .chkDepth) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < n.toNat then (.error .rangeChk, { st with stack := s })
      else if n.toNat ≤ s.size then (.ok (), { st with stack := s })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Nat.shiftLeft_eq]

/-- `ONLYX` (C++ `exec_onlyx`): the count `n` on top; the bottom `n` values of the rest stay. -/
@[vm_spec] theorem onlyX (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .onlyX) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < n.toNat then (.error .rangeChk, { st with stack := s })
      else if n.toNat ≤ s.size then (.ok (), { st with stack := s.take n.toNat })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Nat.shiftLeft_eq]

/-- `DROPX` (C++ `exec_drop_x`): the count `n` on top; the top `n` values of the rest are
dropped. -/
@[vm_spec] theorem dropX (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .dropX) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < n.toNat then (.error .rangeChk, { st with stack := s })
      else if n.toNat ≤ s.size then (.ok (), { st with stack := s.take (s.size - n.toNat) })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Nat.shiftLeft_eq]

/-- `ONLYTOPX` (C++ `exec_onlytop_x`): the count `n` on top; the top `n` values of the rest stay,
the entries over 255 charged one gas each. -/
@[vm_spec] theorem onlyTopX (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .onlyTopX) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < n.toNat then (.error .rangeChk, { st with stack := s })
      else if n.toNat ≤ s.size then
        if 0 < s.size - n.toNat then
          if 255 < n.toNat then
            (.ok (), { st with stack := s.extract (s.size - n.toNat) s.size,
                               gas := st.gas.consume (n.toNat - 255 : Nat) })
          else (.ok (), { st with stack := s.extract (s.size - n.toNat) s.size })
        else (.ok (), { st with stack := s })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Nat.shiftLeft_eq, VmState.consumeGas]

/-! ## Shapes -/

/-- `2DUP` on a stack `s a b`: `s a b a b`. -/
@[vm_spec] theorem twoDup_shape (st : VmState) (s : Stack) (a b : Value) (hs : st.stack = (s.push a).push b) :
    ExceptT.run (execInstr .twoDup) st = (.ok (), { st with stack := (((s.push a).push b).push a).push b }) := by
  vm_simp [hs]

/-- `2OVER` on a stack `s a b c d`: `s a b c d a b`. -/
@[vm_spec] theorem twoOver_shape (st : VmState) (s : Stack) (a b c d : Value)
    (hs : st.stack = (((s.push a).push b).push c).push d) :
    ExceptT.run (execInstr .twoOver) st =
      (.ok (), { st with stack := (((((s.push a).push b).push c).push d).push a).push b }) := by
  vm_simp [hs]

/-- `2SWAP` on a stack `s a b c d`: `s c d a b`. -/
@[vm_spec] theorem twoSwap_shape (st : VmState) (s : Stack) (a b c d : Value)
    (hs : st.stack = (((s.push a).push b).push c).push d) :
    ExceptT.run (execInstr .twoSwap) st = (.ok (), { st with stack := (((s.push c).push d).push a).push b }) := by
  vm_simp [hs]

/-- `TUCK` on a stack `s a b`: `s b a b`. -/
@[vm_spec] theorem tuck_shape (st : VmState) (s : Stack) (a b : Value) (hs : st.stack = (s.push a).push b) :
    ExceptT.run (execInstr .tuck) st = (.ok (), { st with stack := ((s.push b).push a).push b }) := by
  vm_simp [hs]

/-- `-ROT` on a stack `s a b c`: `s c a b`. -/
@[vm_spec] theorem rotRev_shape (st : VmState) (s : Stack) (a b c : Value) (hs : st.stack = ((s.push a).push b).push c) :
    ExceptT.run (execInstr .rotRev) st = (.ok (), { st with stack := ((s.push c).push a).push b }) := by
  vm_simp [hs]

/-- `2DROP` on a stack `s a b`: `s`. -/
@[vm_spec] theorem drop2_shape (st : VmState) (s : Stack) (a b : Value) (hs : st.stack = (s.push a).push b) :
    ExceptT.run (execInstr .drop2) st = (.ok (), { st with stack := s }) := by
  vm_simp [hs]

/-- `PUSH2 s1,s0` = `2DUP` written as `PUSH2` on a stack `s a b`: `s a b a b`. -/
@[vm_spec] theorem push2_shape (st : VmState) (s : Stack) (a b : Value) (hs : st.stack = (s.push a).push b) :
    ExceptT.run (execInstr (.push2 1 0)) st = (.ok (), { st with stack := (((s.push a).push b).push a).push b }) := by
  vm_simp [hs]

/-! ## Loops -/

/-- `BLKPUSH x,y` (C++ `exec_blkpush`): `x` times, the value at depth `y` is pushed (`y` counted on
the stack as it grows). -/
@[vm_spec] theorem blkPush (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.blkPush x y)) st =
      if y < st.stack.size then
        (.ok (), { st with stack := (List.range' 0 x).foldl (fun s _ => s.push (s.at y)) st.stack })
      else (.error .stkUnd, st) := by
  vm_simp
  split
  · rw [Std.Range.forIn_eq_forIn_range', VM.run_forIn_stack _ _ (fun _ s => s.push (s.at y)) (fun s => y < s.size)
      (by intro i _ s h; simp; omega) (by intro i _ st h; vm_simp [Stack.at, h]) st (by assumption)]
    simp [Std.Range.size, VM.bindRes_ok, VM.run_pure]
  · rfl

/-- `REVERSE x,y` (C++ `exec_reverse`): the `x` values below the top `y` are reversed, by
exchanging the entries `i0 + i` and `i1 - 1 - i` (`i0`, `i1` the ends of the block, from the
bottom) for `i < x / 2`. -/
@[vm_spec] theorem reverse (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.reverse x y)) st =
      if x + y ≤ st.stack.size then
        let i0 := st.stack.size - (x + y)
        let i1 := st.stack.size - y
        let s' := (List.range' 0 (x / 2)).foldl
          (fun a i => (a.set! (i0 + i) a[i1 - 1 - i]!).set! (i1 - 1 - i) a[i0 + i]!) st.stack
        (.ok (), { st with stack := s' })
      else (.error .stkUnd, st) := by
  vm_simp
  simp [Std.Range.forIn_eq_forIn_range', Std.Range.size, List.forIn_pure_yield_eq_foldl]

/-- `ROLL` = `ROLLX` (C++ `exec_roll`): the count `n` on top; the value at depth `n` of the rest
moves to the top, by the exchanges of depths `n-1-i`, `n-i` for `i < n`; the entries over 255
charged one gas each. -/
@[vm_spec] theorem roll (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .roll) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < n.toNat then (.error .rangeChk, { st with stack := s })
      else if n.toNat < s.size then
        let s' := (List.range' 0 n.toNat).foldl (fun a i => a.exchange (n.toNat - 1 - i) (n.toNat - 1 - i + 1)) s
        if 255 < n.toNat then (.ok (), { st with stack := s', gas := st.gas.consume (n.toNat - 255 : Nat) })
        else (.ok (), { st with stack := s' })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Nat.shiftLeft_eq, VmState.consumeGas, VM.run_roll_loop]

/-- `-ROLL` = `ROLLREVX` (C++ `exec_rollrev`): the count `n` on top; the top of the rest moves to
depth `n`, by the exchanges of depths `i`, `i+1` for `i < n`. -/
@[vm_spec] theorem rollRev (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .rollRev) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < n.toNat then (.error .rangeChk, { st with stack := s })
      else if n.toNat < s.size then
        let s' := (List.range' 0 n.toNat).foldl (fun a i => a.exchange i (i + 1)) s
        if 255 < n.toNat then (.ok (), { st with stack := s', gas := st.gas.consume (n.toNat - 255 : Nat) })
        else (.ok (), { st with stack := s' })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Nat.shiftLeft_eq, VmState.consumeGas, VM.run_rollRev_loop]

end Spec

end TvmLean

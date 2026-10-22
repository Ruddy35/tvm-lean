import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: stack manipulation

The format of every specification of `Proofs/Exec/Spec`: for an instruction `i`, a state `st`
whose stack has a given shape (`hs : st.stack = ...`, written with `Array.push`, the top last) and
any further condition on `st`, the run of the instruction is given exactly:

  `ExceptT.run (execInstr i) st = (result, state after)`

with the cases the instruction distinguishes as `if`s (the conditions on the unknown values that
the run depends on). The specification is proved from the model (`vm_simp`, which runs the
instruction's handler); `VmState.stepOnceWith_instr` turns it into the step of the VM. The state
after is `st` with the fields the instruction changes, so the specification also says what it
leaves alone.

A family of instructions has a module here (`Spec/Stack`, `Spec/Arith`, `Spec/Flow`, `Spec/Cell`,
`Spec/TonEnv`); a new specification is stated in this format and proved by `vm_simp [hs]` (or with
the lemmas of the primitives its handler uses added to `vm_run`, `Proofs/Exec/VM.lean`).

The parametric instructions (`PUSH s(k)`, `POP s(k)`, `XCHG s0,s(k)`, `BLKDROP n`) are specified
for any stack deep enough, with the value at depth `k` (`Stack.at`); the others for the shape they
take.
-/

namespace TvmLean

/-- The value at depth `k` of a stack (`s0` is the top): `s[size - 1 - k]!`, as the model reads it
(`VM.fetch`). -/
abbrev Stack.at (s : Stack) (k : Nat) : Value := s[s.size - 1 - k]!

/-- The stack with the values at depths `i` and `j` exchanged (`VM.swap`). -/
abbrev Stack.swap (s : Stack) (i j : Nat) : Stack :=
  (s.set! (s.size - 1 - i) (s.at j)).set! (s.size - 1 - j) (s.at i)

namespace Spec

/-- `PUSH s(k)` (C++ `exec_push`, `exec_dup`, `exec_over`, stackops.cpp): the value at depth `k`
is pushed; stk_und if the stack is not deeper than `k`. -/
@[vm_spec] theorem push (st : VmState) (k : Nat) :
    ExceptT.run (execInstr (.push k)) st =
      if k < st.stack.size then (.ok (), { st with stack := st.stack.push (st.stack.at k) })
      else (.error .stkUnd, st) := by
  vm_simp

/-- `XCHG s0,s(k)` (C++ `exec_xchg0`, `exec_swap`): the top and the value at depth `k` are
exchanged. -/
@[vm_spec] theorem xchg0 (st : VmState) (k : Nat) :
    ExceptT.run (execInstr (.xchg0 k)) st =
      if k < st.stack.size then
        (.ok (), { st with stack := ((st.stack.set! (st.stack.size - 1) (st.stack.at k)).set!
          (st.stack.size - 1 - k) (st.stack.at 0)) })
      else (.error .stkUnd, st) := by
  vm_simp
  rfl

/-- `SWAP` = `XCHG s0,s1` on a stack `s a b`: `s b a`. -/
@[vm_spec] theorem swap (st : VmState) (s : Stack) (a b : Value) (hs : st.stack = (s.push a).push b) :
    ExceptT.run (execInstr (.xchg0 1)) st = (.ok (), { st with stack := (s.push b).push a }) := by
  vm_simp [hs]

/-- `XCHG s0,s2` on a stack `s a b c`: `s c b a`. -/
@[vm_spec] theorem xchg0_2 (st : VmState) (s : Stack) (a b c : Value) (hs : st.stack = ((s.push a).push b).push c) :
    ExceptT.run (execInstr (.xchg0 2)) st = (.ok (), { st with stack := ((s.push c).push b).push a }) := by
  vm_simp [hs]

/-- `POP s(k)` (C++ `exec_pop`, `exec_drop`, `exec_nip`): the top replaces the value at depth `k`
and is dropped. -/
@[vm_spec] theorem pop (st : VmState) (k : Nat) :
    ExceptT.run (execInstr (.pop k)) st =
      if k < st.stack.size then
        (.ok (), { st with stack := ((st.stack.set! (st.stack.size - 1) (st.stack.at k)).set!
          (st.stack.size - 1 - k) (st.stack.at 0)).pop })
      else (.error .stkUnd, st) := by
  vm_simp [Stack.at]

/-- `DROP` = `POP s0` on a stack `s a`: `s`. -/
@[vm_spec] theorem drop (st : VmState) (s : Stack) (a : Value) (hs : st.stack = s.push a) :
    ExceptT.run (execInstr (.pop 0)) st = (.ok (), { st with stack := s }) := by
  vm_simp [hs]

/-- `NIP` = `POP s1` on a stack `s a b`: `s b`. -/
@[vm_spec] theorem nip (st : VmState) (s : Stack) (a b : Value) (hs : st.stack = (s.push a).push b) :
    ExceptT.run (execInstr (.pop 1)) st = (.ok (), { st with stack := s.push b }) := by
  vm_simp [hs]

/-- `ROT` (C++ `exec_rot`) on a stack `s a b c`: `s b c a`. -/
@[vm_spec] theorem rot (st : VmState) (s : Stack) (a b c : Value) (hs : st.stack = ((s.push a).push b).push c) :
    ExceptT.run (execInstr .rot) st = (.ok (), { st with stack := ((s.push b).push c).push a }) := by
  vm_simp [hs]

/-- `XCPU s(i),s(j)` on a stack `s a b c` with `i = 2`, `j = 0`... see `xcpu`. -/
@[vm_spec] theorem xcpu (st : VmState) (i j : Nat) :
    ExceptT.run (execInstr (.xcpu i j)) st =
      if Nat.max i j < st.stack.size then
        let s1 := (st.stack.set! (st.stack.size - 1) (st.stack.at i)).set! (st.stack.size - 1 - i) (st.stack.at 0)
        (.ok (), { st with stack := s1.push (Stack.at s1 j) })
      else (.error .stkUnd, st) := by
  vm_simp [Stack.at]

/-- `BLKDROP n` (C++ `exec_blkdrop`): the top `n` values are dropped. -/
@[vm_spec] theorem blkdrop (st : VmState) (n : Nat) :
    ExceptT.run (execInstr (.blkdrop n)) st =
      if n ≤ st.stack.size then (.ok (), { st with stack := st.stack.take (st.stack.size - n) })
      else (.error .stkUnd, st) := by
  vm_simp

/-- `PUSHINT x` (C++ `exec_push_tinyint4`, `exec_push_tinyint8`, `exec_push_smallint`,
`exec_push_int`): a finite `x` is pushed if it fits 257 bits (the decoder makes only such). -/
@[vm_spec] theorem pushInt (st : VmState) (x : Int) :
    ExceptT.run (execInstr (.pushInt (.num x))) st =
      if (IntVal.num x).signedFits257 then (.ok (), { st with stack := st.stack.push (.int (.num x)) })
      else (.error .intOv, st) := by
  vm_simp

/-- `PUSHPOW2 e` (C++ `exec_push_pow2`): `2^e` is pushed. -/
@[vm_spec] theorem pushPow2 (st : VmState) (e : Nat) :
    ExceptT.run (execInstr (.pushPow2 e)) st = (.ok (), { st with stack := st.stack.push (.int (.num (2 ^ e))) }) := by
  vm_simp [intPow2]

/-- `XCHG s(x),s(y)` (C++ `exec_xchg`, `1 ≤ x < y`): the values at depths `x` and `y` are
exchanged. -/
@[vm_spec] theorem xchg (st : VmState) (x y : Nat) (hxy : 0 < x ∧ x < y) :
    ExceptT.run (execInstr (.xchg x y)) st =
      if y < st.stack.size then (.ok (), { st with stack := st.stack.swap x y })
      else (.error .stkUnd, st) := by
  have h : ¬ (x = 0 ∨ y ≤ x) := by omega
  vm_simp [h]

/-- `XCHG2 s(x),s(y)` (C++ `exec_xchg2`): `XCHG s1,s(x)` then `XCHG s0,s(y)`. -/
@[vm_spec] theorem xchg2 (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.xchg2 x y)) st =
      if Nat.max (Nat.max x y) 1 < st.stack.size then
        (.ok (), { st with stack := (st.stack.swap 1 x).swap 0 y })
      else (.error .stkUnd, st) := by
  vm_simp [Stack.swap, Stack.at]

/-- `XCHG3 s(x),s(y),s(z)` (C++ `exec_xchg3`): `XCHG s2,s(x)`, `XCHG s1,s(y)`, `XCHG s0,s(z)`. -/
@[vm_spec] theorem xchg3 (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.xchg3 x y z)) st =
      if Nat.max (Nat.max (Nat.max x y) z) 2 < st.stack.size then
        (.ok (), { st with stack := ((st.stack.swap 2 x).swap 1 y).swap 0 z })
      else (.error .stkUnd, st) := by
  vm_simp [Stack.swap, Stack.at]

/-- `XC2PU s(x),s(y),s(z)` (C++ `exec_xc2pu`): `XCHG2 s(x),s(y)`, then `PUSH s(z)`. -/
@[vm_spec] theorem xc2pu (st : VmState) (x y z : Nat) :
    ExceptT.run (execInstr (.xc2pu x y z)) st =
      if Nat.max (Nat.max (Nat.max x y) z) 1 < st.stack.size then
        (.ok (), { st with stack := ((st.stack.swap 1 x).swap 0 y).push (((st.stack.swap 1 x).swap 0 y).at z) })
      else (.error .stkUnd, st) := by
  vm_simp [Stack.swap, Stack.at]

/-- `PUSH2 s(x),s(y)` (C++ `exec_push2`): `PUSH s(x)`, then `PUSH s(y+1)`. -/
@[vm_spec] theorem push2 (st : VmState) (x y : Nat) :
    ExceptT.run (execInstr (.push2 x y)) st =
      if Nat.max x y < st.stack.size then
        (.ok (), { st with stack := (st.stack.push (st.stack.at x)).push (st.stack.at y) })
      else (.error .stkUnd, st) := by
  vm_simp [Stack.swap, Stack.at]
  have : st.stack.size - (y + 1) = st.stack.size - 1 - y := by omega
  rw [this]

/-- `TUCK` (C++ `exec_tuck`) on a stack `s a b`: `s b a b`. -/
@[vm_spec] theorem tuck (st : VmState) (s : Stack) (a b : Value) (hs : st.stack = (s.push a).push b) :
    ExceptT.run (execInstr .tuck) st = (.ok (), { st with stack := ((s.push b).push a).push b }) := by
  vm_simp [hs]

/-- `-ROT` (C++ `exec_rotrev`) on a stack `s a b c`: `s c a b`. -/
@[vm_spec] theorem rotRev (st : VmState) (s : Stack) (a b c : Value) (hs : st.stack = ((s.push a).push b).push c) :
    ExceptT.run (execInstr .rotRev) st = (.ok (), { st with stack := ((s.push c).push a).push b }) := by
  vm_simp [hs]

/-- `2DROP` (C++ `exec_drop2`) on a stack `s a b`: `s`. -/
@[vm_spec] theorem drop2 (st : VmState) (s : Stack) (a b : Value) (hs : st.stack = (s.push a).push b) :
    ExceptT.run (execInstr .drop2) st = (.ok (), { st with stack := s }) := by
  vm_simp [hs]

end Spec

end TvmLean

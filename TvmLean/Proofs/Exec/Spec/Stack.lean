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

end Spec

end TvmLean

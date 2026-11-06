import TvmLean.Proofs.Exec.Eval
import TvmLean.Proofs.Basic

/-!
# Specifications: returns, selections and throws on a flag; compositions of continuations

In the format of `Proofs/Exec/Spec/Stack.lean`. A flag is an integer, true if it is not zero (C++
`Stack::pop_bool`); a return is the run of `RET` or `RETALT` on the stack under the flag (their
specifications, `Spec.ret`, `Spec.retAlt`, ..., `Proofs/Exec/Spec/Flow.lean`, `ContSave.lean`, take
it from there).

* `RETBOOL` (C++ `exec_ret_bool`, contops.cpp:83): `RET` if the flag is true, else `RETALT`;
* `IFNOTRET` (C++ `exec_ifnotret`, contops.cpp:381): `RET` if the flag is false; `IFRETALT`,
  `IFNOTRETALT` (C++ `exec_ifretalt`, `exec_ifnotretalt`, contops.cpp:425, 433): `RETALT` if the
  flag is true, false; else the stack under the flag;
* `CONDSEL` (C++ `exec_condsel`, contops.cpp:402) on the stack `s f x y`: `x` if the flag is true,
  else `y`; `CONDSELCHK` (C++ `exec_condsel_chk`, contops.cpp:412) the same if `x` and `y` have the
  same type (the model's `sameValueType`), else type_chk with the flag left;
* `BOOLAND`, `BOOLOR`, `COMPOSBOTH` (C++ `exec_compos`, contops.cpp:975, masks 1, 2, 3) on the stack
  `s c v` of two continuations: `c` with `v` as its `c0`, as its `c1`, as both
  (`Continuation.defineC0`, `Continuation.defineC1`);
* `THROWARGIF n`, `THROWARGIFNOT n` (C++ `exec_throw_arg_fixed`, contops.cpp:1155, modes 1, 2) on the
  stack `s a f`: the exception `n` with the argument `a` raised if the flag is true (false), else
  the stack `s`.
-/

namespace TvmLean.Spec

/-- `RETBOOL` (C++ `exec_ret_bool`) on the stack `s f`: `RET` if the flag is true, else `RETALT`, on
the stack `s`. -/
@[vm_spec] theorem retBool (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .retBool) st =
      if n ≠ 0 then ExceptT.run (execInstr .ret) { st with stack := s }
      else ExceptT.run (execInstr .retAlt) { st with stack := s } := by
  by_cases hn : n = 0 <;> vm_simp [hs, hn, IntVal.toBool?]

/-- `IFNOTRET` (C++ `exec_ifnotret`) on the stack `s f`: `RET` on the stack `s` if the flag is
false. -/
@[vm_spec] theorem ifnotret (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .ifnotret) st =
      if n = 0 then ExceptT.run (execInstr .ret) { st with stack := s }
      else (.ok (), { st with stack := s }) := by
  by_cases hn : n = 0 <;> vm_simp [hs, hn, IntVal.toBool?]

/-- `IFRETALT` (C++ `exec_ifretalt`) on the stack `s f`: `RETALT` on the stack `s` if the flag is
true. -/
@[vm_spec] theorem ifretAlt (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.contExt .ifretAlt)) st =
      if n ≠ 0 then ExceptT.run (execInstr .retAlt) { st with stack := s }
      else (.ok (), { st with stack := s }) := by
  by_cases hn : n = 0 <;> vm_simp [hs, hn, IntVal.toBool?]

/-- `IFNOTRETALT` (C++ `exec_ifnotretalt`) on the stack `s f`: `RETALT` on the stack `s` if the flag
is false. -/
@[vm_spec] theorem ifnotretAlt (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.contExt .ifnotretAlt)) st =
      if n = 0 then ExceptT.run (execInstr .retAlt) { st with stack := s }
      else (.ok (), { st with stack := s }) := by
  by_cases hn : n = 0 <;> vm_simp [hs, hn, IntVal.toBool?]

/-- `CONDSEL` (C++ `exec_condsel`) on the stack `s f x y`: `x` if the flag is true, else `y`. -/
@[vm_spec] theorem condSel (st : VmState) (s : Stack) (n : Int) (x y : Value)
    (hs : st.stack = ((s.push (.int (.num n))).push x).push y) :
    ExceptT.run (execInstr (.contExt .condSel)) st =
      (.ok (), { st with stack := s.push (if n ≠ 0 then x else y) }) := by
  by_cases hn : n = 0 <;> vm_simp [hs, hn, IntVal.toBool?]

/-- `CONDSELCHK` (C++ `exec_condsel_chk`) on the stack `s f x y`: `CONDSEL` if `x` and `y` have the
same type, else type_chk with the stack `s f`. -/
@[vm_spec] theorem condSelChk (st : VmState) (s : Stack) (n : Int) (x y : Value)
    (hs : st.stack = ((s.push (.int (.num n))).push x).push y) :
    ExceptT.run (execInstr (.contExt .condSelChk)) st =
      if (private% TvmLean.Semantics.Exec.Cont.CondSel TvmLean.sameValueType) x y then
        (.ok (), { st with stack := s.push (if n ≠ 0 then x else y) })
      else (.error .typeChk, { st with stack := s.push (.int (.num n)) }) := by
  cases ht : (private% TvmLean.Semantics.Exec.Cont.CondSel TvmLean.sameValueType) x y <;>
    by_cases hn : n = 0 <;> vm_simp [hs, hn, ht, IntVal.toBool?]

/-- `BOOLAND` (C++ `exec_compos`, mask 1) on the stack `s c v`: `c` with `v` as its `c0`. -/
@[vm_spec] theorem boolAnd (st : VmState) (s : Stack) (c v : Continuation)
    (hs : st.stack = (s.push (.cont c)).push (.cont v)) :
    ExceptT.run (execInstr .boolAnd) st = (.ok (), { st with stack := s.push (.cont (c.defineC0 v)) }) := by
  vm_simp [hs]

/-- `BOOLOR` (C++ `exec_compos`, mask 2) on the stack `s c v`: `c` with `v` as its `c1`. -/
@[vm_spec] theorem boolOr (st : VmState) (s : Stack) (c v : Continuation)
    (hs : st.stack = (s.push (.cont c)).push (.cont v)) :
    ExceptT.run (execInstr .boolOr) st = (.ok (), { st with stack := s.push (.cont (c.defineC1 v)) }) := by
  vm_simp [hs]

/-- `COMPOSBOTH` (C++ `exec_compos`, mask 3) on the stack `s c v`: `c` with `v` as its `c0` and its
`c1`. -/
@[vm_spec] theorem composBoth (st : VmState) (s : Stack) (c v : Continuation)
    (hs : st.stack = (s.push (.cont c)).push (.cont v)) :
    ExceptT.run (execInstr .composBoth) st =
      (.ok (), { st with stack := s.push (.cont ((c.defineC0 v).defineC1 v)) }) := by
  vm_simp [hs]

/-- `THROWARGIF e` (C++ `exec_throw_arg_fixed`, mode 1) on the stack `s a f`: the exception `e` with
the argument `a` if the flag is true, else the stack `s`. -/
@[vm_spec] theorem throwArgIf (st : VmState) (s : Stack) (a : Value) (n e : Int)
    (hs : st.stack = (s.push a).push (.int (.num n))) :
    ExceptT.run (execInstr (.throwArgIf e)) st =
      if n ≠ 0 then ExceptT.run (VM.throwToHandler fun st => st.throwExceptionArg e a) { st with stack := s }
      else (.ok (), { st with stack := s }) := by
  by_cases hn : n = 0 <;> vm_simp [hs, hn, IntVal.toBool?]

/-- `THROWARGIFNOT e` (C++ `exec_throw_arg_fixed`, mode 2) on the stack `s a f`: the exception `e`
with the argument `a` if the flag is false, else the stack `s`. -/
@[vm_spec] theorem throwArgIfNot (st : VmState) (s : Stack) (a : Value) (n e : Int)
    (hs : st.stack = (s.push a).push (.int (.num n))) :
    ExceptT.run (execInstr (.throwArgIfNot e)) st =
      if n = 0 then ExceptT.run (VM.throwToHandler fun st => st.throwExceptionArg e a) { st with stack := s }
      else (.ok (), { st with stack := s }) := by
  by_cases hn : n = 0 <;> vm_simp [hs, hn, IntVal.toBool?]

end TvmLean.Spec

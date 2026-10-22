import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: the rest of integer arithmetic

In the format of `Proofs/Exec/Spec/Stack.lean`, for the operands finite integers (`IntVal.num`)
unless a specification says otherwise (`divMod_nan_divisor`, `isnan_nan`, ...). A result that does
not fit 257 bits (`-2^256 ≤ r < 2^256`) is int_ov, the operands popped, for the non-quiet
instructions, and NaN for the quiet ones (C++ `push_int_quiet`); the fit of a result stays an
`if`, as an operand of the stack is any integer here.

* `MUL`, the quiet forms of `ADD`, `SUB`, `SUBR`, `INC`, `DEC`, `ADDCONST`/`MULCONST`, `NEGATE`,
  `ABS`; `MIN`, `MAX`, `MINMAX` and their quiet forms;
* `CMP`, `NEQ`, `GEQ`, `SGN`, `EQINT`/`NEQINT`/`GTINT`/`LESSINT` (`ISZERO`, `ISPOS`, `ISNEG`,
  `ISNNEG`) and their quiet forms;
* the division families `DIV`/`MOD`/`DIVMOD`/`ADDDIVMOD` and `MULDIV`/`MULMOD`/`MULDIVMOD`/
  `MULADDDIVMOD`, any rounding mode the decoder makes (-1 down, 0 to nearest, 1 up: the result is
  `divModRound`), quiet or not, a zero divisor (NaN), a NaN operand of `DIV`;
* the shifts `LSHIFT`/`RSHIFT` by a constant and by the stack, their quiet forms (version
  dependent: an `if` on `st.globalVersion`), `POW2`, `QPOW2`; the right shifts are the division of
  `Int` (`floorDivPow2_eq`);
* `FITS`/`UFITS` by a constant and by the stack and their quiet forms, `BITSIZE`, `UBITSIZE`,
  `QBITSIZE`, `ISNAN`, `CHKNAN`;
* `AND`, `OR`, `XOR` and their quiet forms, on the 257-bit two's complements (`twos257`), and
  `QNOT`. (`NOT` is specified with the instructions of wallet v3.)

A handler whose conditions include literals is run after those are decided (`arith_pre`): the
contextual `simp` of `vm_simp` loops in a branch that assumes a false literal condition. The
private helpers of the handlers (`execLessIntCore`, `popLongLike`, `shiftOutOfRange`) are unfolded
by `unfoldPrivateRun` and `delta_private`.
-/

namespace TvmLean.Spec

open Lean Meta Simp in
/-- `ExceptT.run (f args) st` for a private VM program `f` of the model (a `private def` in
`TvmLean`, which `Exec.unfoldModelRun` leaves alone): `f` unfolded. -/
dsimproc unfoldPrivateRun (@ExceptT.run Excno (StateM VmState) _ _ _) := fun e => do
  let args := e.getAppArgs
  unless e.isAppOf ``ExceptT.run && args.size == 5 do return .continue
  let m := args[3]!
  let some f := m.getAppFn.constName? | return .continue
  unless isPrivateName f && (`TvmLean).isPrefixOf (privateToUserName f) do return .continue
  match ← withTransparency .all (unfoldDefinition? m) with
  | some m' => return .visit (mkAppN e.getAppFn (args.set! 3 m'.headBeta))
  | none => return .continue

open Lean Elab Tactic Meta in
/-- `delta_private [f, g]`: the private definitions `TvmLean.f`, `TvmLean.g` of the model (which
another module cannot name) delta-expanded in the goal. -/
elab "delta_private " "[" ns:ident,* "]" : tactic => do
  let names := ns.getElems.map (`TvmLean ++ ·.getId)
  liftMetaTactic1 fun g => g.deltaTarget fun c => isPrivateName c && names.contains (privateToUserName c)

/-- The conditions of the handler on literals decided before `vm_simp`: its contextual `simp`
loops on a branch whose condition is a decided literal (`(1 == 3) = true` assumed in a dead
branch rewrites `False` to `True` and back). -/
local macro "arith_pre" : tactic =>
  `(tactic| try simp only [TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok,
    Nat.reduceBEq, Nat.reduceBNe, Int.reduceBNe, Int.reduceBEq, Bool.and_false, Bool.false_and,
    Bool.and_true, Bool.true_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true, reduceIte, Int.reduceNeg])

/-- A rounding mode of the decoder (-1 down, 0 to nearest, 1 up) passes the handler's check. -/
theorem roundMode_ok (rm : Int) (h : rm = -1 ∨ rm = 0 ∨ rm = 1) : (rm != -1 && rm != 0 && rm != 1) = false := by
  rcases h with h | h | h <;> subst h <;> decide

/-! ## Addition, subtraction, multiplication -/

/-- `MUL` (C++ `exec_mul`, arithops.cpp). -/
@[vm_spec] theorem mul (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .mul) st =
      if -2 ^ 256 ≤ x * y ∧ x * y < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x * y))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `QMUL` (C++ `exec_mul`, quiet). -/
@[vm_spec] theorem qmul (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .qmul) st =
      if -2 ^ 256 ≤ x * y ∧ x * y < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x * y))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-- `QADD` (C++ `exec_add`, quiet). -/
@[vm_spec] theorem qadd (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .qadd) st =
      if -2 ^ 256 ≤ x + y ∧ x + y < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x + y))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-- `QSUB` (C++ `exec_sub`, quiet). -/
@[vm_spec] theorem qsub (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .qsub) st =
      if -2 ^ 256 ≤ x - y ∧ x - y < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x - y))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-- `SUBR` (C++ `exec_subr`): `y - x`. -/
@[vm_spec] theorem subr (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .subr) st =
      if -2 ^ 256 ≤ y - x ∧ y - x < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (y - x))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `QSUBR` (C++ `exec_subr`, quiet). -/
@[vm_spec] theorem qsubr (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .qsubr) st =
      if -2 ^ 256 ≤ y - x ∧ y - x < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (y - x))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-- `QINC` (C++ `exec_inc`, quiet). -/
@[vm_spec] theorem qinc (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .qinc) st =
      if -2 ^ 256 ≤ x + 1 ∧ x + 1 < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x + 1))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-- `QDEC` (C++ `exec_dec`, quiet). -/
@[vm_spec] theorem qdec (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .qdec) st =
      if -2 ^ 256 ≤ x - 1 ∧ x - 1 < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x - 1))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-- `ADDCONST n` = `ADDINT n` (C++ `exec_add_tinyint8`). -/
@[vm_spec] theorem addInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.addInt n)) st =
      if -2 ^ 256 ≤ x + n ∧ x + n < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x + n))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `QADDINT n` (C++ `exec_add_tinyint8`, quiet). -/
@[vm_spec] theorem qaddInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.qaddInt n))) st =
      if -2 ^ 256 ≤ x + n ∧ x + n < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x + n))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-- `MULCONST n` = `MULINT n` (C++ `exec_mul_tinyint8`). -/
@[vm_spec] theorem mulInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.mulInt n)) st =
      if -2 ^ 256 ≤ x * n ∧ x * n < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x * n))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `QMULINT n` (C++ `exec_mul_tinyint8`, quiet). -/
@[vm_spec] theorem qmulInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.qmulInt n))) st =
      if -2 ^ 256 ≤ x * n ∧ x * n < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x * n))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-- `NEGATE` (C++ `exec_negate`): `-x`, int_ov for `x = -2^256`. -/
@[vm_spec] theorem negate (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .negate) st =
      if -2 ^ 256 ≤ -x ∧ -x < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (-x))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `QNEGATE` (C++ `exec_negate`, quiet). -/
@[vm_spec] theorem qnegate (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .qnegate) st =
      if -2 ^ 256 ≤ -x ∧ -x < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (-x))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-- `ABS`, `QABS` (C++ `exec_abs`): `|x|`; it does not fit for `x = -2^256`. -/
@[vm_spec] theorem abs (st : VmState) (s : Stack) (x : Int) (quiet : Bool) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.abs quiet)) st =
      if x < 0 then
        if -2 ^ 256 ≤ -x ∧ -x < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (-x))) })
        else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ x ∧ x < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num x)) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-! ## Minimum and maximum -/

/-- `MIN` (C++ `exec_minmax`, mode 2). -/
@[vm_spec] theorem min (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .min) st =
      if -2 ^ 256 ≤ (if x ≤ y then x else y) ∧ (if x ≤ y then x else y) < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (if x ≤ y then x else y))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs, IntVal.min]

/-- `QMIN` (C++ `exec_minmax`, quiet). -/
@[vm_spec] theorem qmin (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qmin)) st =
      if -2 ^ 256 ≤ (if x ≤ y then x else y) ∧ (if x ≤ y then x else y) < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (if x ≤ y then x else y))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs, IntVal.min]

/-- `MAX` (C++ `exec_minmax`, mode 4). -/
@[vm_spec] theorem max (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .max) st =
      if -2 ^ 256 ≤ (if y ≤ x then x else y) ∧ (if y ≤ x then x else y) < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (if y ≤ x then x else y))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `QMAX` (C++ `exec_minmax`, quiet). -/
@[vm_spec] theorem qmax (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .qmax) st =
      if -2 ^ 256 ≤ (if y ≤ x then x else y) ∧ (if y ≤ x then x else y) < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (if y ≤ x then x else y))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

/-! ## Comparisons -/

/-- `CMP` (C++ `exec_cmp` with mode `0x987`): -1, 0 or 1 as `x < y`, `x = y`, `x > y`. -/
@[vm_spec] theorem cmp (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .cmp) st =
      (.ok (), { st with stack := s.push (.int (.num (if x < y then -1 else if x = y then 0 else 1))) }) := by
  vm_simp [hs]
  by_cases h1 : x < y
  · simp [h1]
  · by_cases h2 : x = y <;> simp [h1, h2]

/-- `QCMP` (C++ `exec_cmp`, quiet). -/
@[vm_spec] theorem qcmp (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .qcmp) st =
      (.ok (), { st with stack := s.push (.int (.num (if x < y then -1 else if x = y then 0 else 1))) }) := by
  vm_simp [hs]
  by_cases h1 : x < y
  · simp [h1]
  · by_cases h2 : x = y <;> simp [h1, h2]

/-- `NEQ` (C++ `exec_cmp` with mode `0x787`). -/
@[vm_spec] theorem neq (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .neq) st =
      (.ok (), { st with stack := s.push (.int (.num (if x ≠ y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `GEQ` (C++ `exec_cmp` with mode `0x778`). -/
@[vm_spec] theorem geq (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .geq) st =
      (.ok (), { st with stack := s.push (.int (.num (if x ≥ y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `QLESS` (C++ `exec_cmp`, quiet). -/
@[vm_spec] theorem qless (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qless)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x < y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `QEQUAL` (C++ `exec_cmp`, quiet). -/
@[vm_spec] theorem qequal (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qequal)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x = y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `QLEQ` (C++ `exec_cmp`, quiet). -/
@[vm_spec] theorem qleq (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qleq)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x ≤ y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `QGREATER` (C++ `exec_cmp`, quiet). -/
@[vm_spec] theorem qgreater (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qgreater)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x > y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `QNEQ` (C++ `exec_cmp`, quiet). -/
@[vm_spec] theorem qneq (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qneq)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x ≠ y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `QGEQ` (C++ `exec_cmp`, quiet). -/
@[vm_spec] theorem qgeq (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qgeq)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x ≥ y then -1 else 0))) }) := by
  vm_simp [hs]

/-- `SGN` (C++ `exec_sgn` with mode `0x987`). -/
@[vm_spec] theorem sgn (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .sgn) st =
      (.ok (), { st with stack := s.push (.int (.num (if x < 0 then -1 else if x = 0 then 0 else 1))) }) := by
  vm_simp [hs]
  by_cases h1 : x < 0
  · simp [h1]
  · by_cases h2 : x = 0 <;> simp [h1, h2]

/-- `QSGN` (C++ `exec_sgn`, quiet). -/
@[vm_spec] theorem qsgn (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.contExt .qsgn)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x < 0 then -1 else if x = 0 then 0 else 1))) }) := by
  vm_simp [hs]
  by_cases h1 : x < 0
  · simp [h1]
  · by_cases h2 : x = 0 <;> simp [h1, h2]

/-- `EQINT n` (C++ `exec_cmp_int` with mode `0x878`); `ISZERO` is `EQINT 0`. -/
@[vm_spec] theorem eqInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.eqInt n)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x = n then -1 else 0))) }) := by
  vm_simp [hs]

/-- `QEQINT n` (C++ `exec_cmp_int`, quiet). -/
@[vm_spec] theorem qeqInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.qeqInt n))) st =
      (.ok (), { st with stack := s.push (.int (.num (if x = n then -1 else 0))) }) := by
  vm_simp [hs]

/-- `NEQINT n` (C++ `exec_cmp_int` with mode `0x787`). -/
@[vm_spec] theorem neqInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.neqInt n)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x ≠ n then -1 else 0))) }) := by
  vm_simp [hs]

/-- `QNEQINT n` (C++ `exec_cmp_int`, quiet). -/
@[vm_spec] theorem qneqInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.qneqInt n))) st =
      (.ok (), { st with stack := s.push (.int (.num (if x ≠ n then -1 else 0))) }) := by
  vm_simp [hs]

/-- `GTINT n` (C++ `exec_cmp_int` with mode `0x788`); `ISPOS` is `GTINT 0`, `ISNNEG` is
`GTINT -1`. -/
@[vm_spec] theorem gtInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.gtInt n)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x > n then -1 else 0))) }) := by
  vm_simp [hs]

/-- `QGTINT n` (C++ `exec_cmp_int`, quiet). -/
@[vm_spec] theorem qgtInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.qgtInt n))) st =
      (.ok (), { st with stack := s.push (.int (.num (if x > n then -1 else 0))) }) := by
  vm_simp [hs]

/-- `LESSINT n` (C++ `exec_cmp_int` with mode `0x887`); `ISNEG` is `LESSINT 0`. -/
@[vm_spec] theorem lessInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.lessInt n)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x < n then -1 else 0))) }) := by
  vm_simp [hs, unfoldPrivateRun]

/-- `QLESSINT n` (C++ `exec_cmp_int`, quiet). -/
@[vm_spec] theorem qlessInt (st : VmState) (s : Stack) (x n : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.qlessInt n)) st =
      (.ok (), { st with stack := s.push (.int (.num (if x < n then -1 else 0))) }) := by
  vm_simp [hs, unfoldPrivateRun]

/-! ## Division -/

/-- `DIV`, `DIVR`, `DIVC` and their quiet forms (C++ `exec_divmod`, result mode 1; rounding `rm`
-1 down, 0 to nearest, 1 up): the quotient of `divModRound`. A zero divisor gives NaN (int_ov
unless quiet). -/
@[vm_spec] theorem div (st : VmState) (s : Stack) (x y rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.divMod 1 rm false quiet)) st =
      if y = 0 then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound x y rm).1 ∧ (divModRound x y rm).1 < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (divModRound x y rm).1)) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  arith_pre
  simp only [roundMode_ok rm hrm, Bool.false_eq_true, if_false]
  vm_simp [hs, Int.add_zero]

/-- `MOD`, `MODR`, `MODC` and their quiet forms (C++ `exec_divmod`, result mode 2): the remainder
of `divModRound`. -/
@[vm_spec] theorem mod (st : VmState) (s : Stack) (x y rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.divMod 2 rm false quiet)) st =
      if y = 0 then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound x y rm).2 ∧ (divModRound x y rm).2 < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (divModRound x y rm).2)) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  arith_pre
  simp only [roundMode_ok rm hrm, Bool.false_eq_true, if_false]
  vm_simp [hs, Int.add_zero]

/-- `DIVMOD`, `DIVMODR`, `DIVMODC` and their quiet forms (C++ `exec_divmod`, result mode 3): the
quotient, then the remainder, each pushed as it fits (int_ov at the first that does not, unless
quiet). -/
@[vm_spec] theorem divmod (st : VmState) (s : Stack) (x y rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.divMod 3 rm false quiet)) st =
      let q := (divModRound x y rm).1
      let r := (divModRound x y rm).2
      if y = 0 then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ q ∧ q < 2 ^ 256 then
        if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := (s.push (.int (.num q))).push (.int (.num r)) })
        else if quiet then (.ok (), { st with stack := (s.push (.int (.num q))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num q)) })
      else if quiet then
        if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num r)) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  arith_pre
  simp only [roundMode_ok rm hrm, Bool.false_eq_true, if_false]
  vm_simp [hs, Int.add_zero]

/-- `ADDDIVMOD`, `ADDDIVMODR`, `ADDDIVMODC` and their quiet forms (C++ `exec_divmod`, result mode
0, from global version 4): `DIVMOD` of `x + w` by `y`; inv_opcode before version 4. -/
@[vm_spec] theorem adddivmod (st : VmState) (s : Stack) (x w y rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num w))).push (.int (.num y))) :
    ExceptT.run (execInstr (.divMod 3 rm true quiet)) st =
      let q := (divModRound (x + w) y rm).1
      let r := (divModRound (x + w) y rm).2
      if st.globalVersion < 4 then (.error .invOpcode, st)
      else if y = 0 then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ q ∧ q < 2 ^ 256 then
        if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := (s.push (.int (.num q))).push (.int (.num r)) })
        else if quiet then (.ok (), { st with stack := (s.push (.int (.num q))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num q)) })
      else if quiet then
        if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num r)) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  arith_pre
  simp only [roundMode_ok rm hrm, Bool.false_eq_true, if_false]
  vm_simp [hs]

set_option maxHeartbeats 2000000 in
/-- The `DIV` family (`divMod d rm false quiet`, result mode `d` 1, 2 or 3) with a NaN divisor:
NaN results (two for `d = 3`), int_ov unless quiet. -/
@[vm_spec] theorem divMod_nan_divisor (st : VmState) (s : Stack) (x : IntVal) (d : Nat) (rm : Int) (quiet : Bool)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hs : st.stack = (s.push (.int x)).push (.int .nan)) :
    ExceptT.run (execInstr (.divMod d rm false quiet)) st =
      if quiet then
        if d = 3 then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.ok (), { st with stack := s.push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  rcases hd with rfl | rfl | rfl <;> arith_pre <;> cases x <;> cases quiet <;> vm_simp [hs]

set_option maxHeartbeats 2000000 in
/-- The `DIV` family with a NaN dividend: as `divMod_nan_divisor`. -/
@[vm_spec] theorem divMod_nan_dividend (st : VmState) (s : Stack) (y : IntVal) (d : Nat) (rm : Int) (quiet : Bool)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hs : st.stack = (s.push (.int .nan)).push (.int y)) :
    ExceptT.run (execInstr (.divMod d rm false quiet)) st =
      if quiet then
        if d = 3 then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.ok (), { st with stack := s.push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  rcases hd with rfl | rfl | rfl <;> arith_pre <;> cases y <;> cases quiet <;> vm_simp [hs]

/-- `MULDIV`, `MULDIVR`, `MULDIVC` and their quiet forms (C++ `exec_muldivmod`, result mode 1):
the quotient of `x * y` by `z`. -/
@[vm_spec] theorem muldiv (st : VmState) (s : Stack) (x y z rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num z))) :
    ExceptT.run (execInstr (.mulDivMod 1 rm false quiet)) st =
      if z = 0 then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * y) z rm).1 ∧ (divModRound (x * y) z rm).1 < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (divModRound (x * y) z rm).1)) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  arith_pre
  simp only [roundMode_ok rm hrm, Bool.false_eq_true, if_false]
  vm_simp [hs, Int.add_zero]

/-- `MULMOD`, `MULMODR`, `MULMODC` and their quiet forms (C++ `exec_muldivmod`, result mode 2):
the remainder of `x * y` by `z`. -/
@[vm_spec] theorem mulmod (st : VmState) (s : Stack) (x y z rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num z))) :
    ExceptT.run (execInstr (.mulDivMod 2 rm false quiet)) st =
      if z = 0 then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ (divModRound (x * y) z rm).2 ∧ (divModRound (x * y) z rm).2 < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (divModRound (x * y) z rm).2)) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  arith_pre
  simp only [roundMode_ok rm hrm, Bool.false_eq_true, if_false]
  vm_simp [hs, Int.add_zero]

/-- `MULDIVMOD`, `MULDIVMODR`, `MULDIVMODC` and their quiet forms (C++ `exec_muldivmod`, result
mode 3): the quotient and the remainder of `x * y` by `z`, as `divmod`. -/
@[vm_spec] theorem muldivmod (st : VmState) (s : Stack) (x y z rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = ((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num z))) :
    ExceptT.run (execInstr (.mulDivMod 3 rm false quiet)) st =
      let q := (divModRound (x * y) z rm).1
      let r := (divModRound (x * y) z rm).2
      if z = 0 then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ q ∧ q < 2 ^ 256 then
        if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := (s.push (.int (.num q))).push (.int (.num r)) })
        else if quiet then (.ok (), { st with stack := (s.push (.int (.num q))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num q)) })
      else if quiet then
        if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num r)) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  arith_pre
  simp only [roundMode_ok rm hrm, Bool.false_eq_true, if_false]
  vm_simp [hs, Int.add_zero]

/-- `MULADDDIVMOD`, `MULADDDIVMODR`, `MULADDDIVMODC` and their quiet forms (C++
`exec_muldivmod`, result mode 0, from global version 4): `DIVMOD` of `x * y + w` by `z`. -/
@[vm_spec] theorem muladddivmod (st : VmState) (s : Stack) (x y w z rm : Int) (quiet : Bool)
    (hrm : rm = -1 ∨ rm = 0 ∨ rm = 1)
    (hs : st.stack = (((s.push (.int (.num x))).push (.int (.num y))).push (.int (.num w))).push (.int (.num z))) :
    ExceptT.run (execInstr (.mulDivMod 3 rm true quiet)) st =
      let q := (divModRound (x * y + w) z rm).1
      let r := (divModRound (x * y + w) z rm).2
      if st.globalVersion < 4 then (.error .invOpcode, st)
      else if z = 0 then
        if quiet then (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
        else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ q ∧ q < 2 ^ 256 then
        if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := (s.push (.int (.num q))).push (.int (.num r)) })
        else if quiet then (.ok (), { st with stack := (s.push (.int (.num q))).push (.int .nan) })
        else (.error .intOv, { st with stack := s.push (.int (.num q)) })
      else if quiet then
        if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := (s.push (.int .nan)).push (.int (.num r)) })
        else (.ok (), { st with stack := (s.push (.int .nan)).push (.int .nan) })
      else (.error .intOv, { st with stack := s }) := by
  arith_pre
  simp only [roundMode_ok rm hrm, Bool.false_eq_true, if_false]
  vm_simp [hs]

/-! ## Shifts and powers of two -/

/-- `floorDivPow2 x b`, the model's division by `2^b` rounding down, is the division of `Int`
(`Int.ediv`, which rounds down for a positive divisor). -/
theorem floorDivPow2_eq (x : Int) (b : Nat) : floorDivPow2 x b = x / 2 ^ b := by
  have hp : (0 : Int) < 2 ^ b := Int.pow_pos (by decide)
  unfold floorDivPow2 intPow2
  by_cases hb : b = 0
  · subst hb; simp
  · have hb' : (b == 0) = false := by simp [hb]
    simp only [hb', Bool.false_eq_true, if_false]
    by_cases hx : x ≥ 0
    · simp [hx]
    · simp only [hx, decide_false, Bool.false_eq_true, if_false]
      generalize (2 : Int) ^ b = p at *
      have h1 := Int.emod_add_mul_ediv (-x + p - 1) p
      have h2 := Int.emod_nonneg (-x + p - 1) (Int.ne_of_gt hp)
      have h3 := Int.emod_lt_of_pos (-x + p - 1) hp
      generalize (-x + p - 1) / p = q at *
      generalize (-x + p - 1) % p = r at *
      have h4 : (p - 1 - r) + p * (-q) = x := by
        rw [Int.mul_neg]; generalize p * q = t at *; omega
      exact ((Int.ediv_emod_unique hp).2 ⟨h4, by omega, by omega⟩).1.symm

/-- `LSHIFT b`, `QLSHIFT b` (C++ `exec_lshift_tinyint8`, `1 ≤ b ≤ 256`): `x * 2^b`. -/
@[vm_spec] theorem lshiftConst (st : VmState) (s : Stack) (x : Int) (quiet : Bool) (b : Nat)
    (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.lshiftConst quiet b)) st =
      if -2 ^ 256 ≤ x * 2 ^ b ∧ x * 2 ^ b < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (x * 2 ^ b))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `RSHIFT b`, `QRSHIFT b` (C++ `exec_rshift_tinyint8`, `1 ≤ b ≤ 256`): `x / 2^b` rounded down
(`floorDivPow2_eq`). -/
@[vm_spec] theorem rshiftConst (st : VmState) (s : Stack) (x : Int) (quiet : Bool) (b : Nat)
    (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.rshiftConst quiet b)) st =
      if -2 ^ 256 ≤ x / 2 ^ b ∧ x / 2 ^ b < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (x / 2 ^ b))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs, floorDivPow2_eq]

/-- `LSHIFT` (C++ `exec_lshift`): the shift `n` on top, `0 ≤ n ≤ 1023` (range_chk otherwise), then
`x * 2^n`; a shift of 260 or more is int_ov at once. -/
@[vm_spec] theorem lshift (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr .lshift) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 260 ≤ n.toNat then (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ x * 2 ^ n.toNat ∧ x * 2 ^ n.toNat < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (x * 2 ^ n.toNat))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `RSHIFT` (C++ `exec_rshift`): the shift `n` on top, `0 ≤ n ≤ 1023`, then `x / 2^n` rounded
down. -/
@[vm_spec] theorem rshift (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr .rshift) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if -2 ^ 256 ≤ x / 2 ^ n.toNat ∧ x / 2 ^ n.toNat < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (x / 2 ^ n.toNat))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs, floorDivPow2_eq]

/-- `QLSHIFT` with the shift on the stack (C++ `exec_lshift`, quiet): a shift outside `0..1023` is
range_chk before global version 13 (and in the non-quiet form), NaN from version 13; `0` shifted
by 260 or more is NaN (the BigInt of C++ overflows). -/
@[vm_spec] theorem lshiftVar (st : VmState) (s : Stack) (x n : Int) (quiet : Bool)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.lshiftVar quiet))) st =
      if (quiet = false ∨ st.globalVersion < 13) ∧ (n < 0 ∨ 1023 < n) then
        (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if n < 0 ∨ 1023 < n then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if x = 0 ∧ 5 < 1 + n.toNat / 52 then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ x * 2 ^ n.toNat ∧ x * 2 ^ n.toNat < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (x * 2 ^ n.toNat))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  by_cases hx : x = 0
  · subst hx
    vm_simp [hs, unfoldPrivateRun]
    delta_private [shiftOutOfRange, intToBigInt52Digits, bigintWordShift]
    vm_simp
  · vm_simp [hs, unfoldPrivateRun, hx]
    delta_private [shiftOutOfRange]
    vm_simp [hx, false_and]

/-- `QRSHIFT` with the shift on the stack (C++ `exec_rshift`, quiet): as `lshiftVar`, the result
`x / 2^n` rounded down. -/
@[vm_spec] theorem rshiftVar (st : VmState) (s : Stack) (x n : Int) (quiet : Bool)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.arithExt (.rshiftVar quiet))) st =
      if (quiet = false ∨ st.globalVersion < 13) ∧ (n < 0 ∨ 1023 < n) then
        (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if n < 0 ∨ 1023 < n then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s })
      else if -2 ^ 256 ≤ x / 2 ^ n.toNat ∧ x / 2 ^ n.toNat < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (x / 2 ^ n.toNat))) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs, unfoldPrivateRun, floorDivPow2_eq]
  delta_private [shiftOutOfRange]
  vm_simp

/-- `POW2` (C++ `exec_pow2`): `2^n` for `0 ≤ n ≤ 1023` (range_chk otherwise); int_ov from
`n = 256`. -/
@[vm_spec] theorem pow2 (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr (.contExt .pow2)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s })
      else if -2 ^ 256 ≤ (2 : Int) ^ n.toNat ∧ (2 : Int) ^ n.toNat < 2 ^ 256 then
        (.ok (), { st with stack := s.push (.int (.num (2 ^ n.toNat))) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `QPOW2` (C++ `exec_pow2`, quiet): `2^n` (NaN from `n = 256`); an `n` outside `0..1023` is
range_chk before global version 13 and NaN from version 13. -/
@[vm_spec] theorem qpow2 (st : VmState) (s : Stack) (n : Int) (hs : st.stack = s.push (.int (.num n))) :
    ExceptT.run (execInstr .qpow2) st =
      if 0 ≤ n ∧ n ≤ 1023 then
        if -2 ^ 256 ≤ (2 : Int) ^ n.toNat ∧ (2 : Int) ^ n.toNat < 2 ^ 256 then
          (.ok (), { st with stack := s.push (.int (.num (2 ^ n.toNat))) })
        else (.ok (), { st with stack := s.push (.int .nan) })
      else if st.globalVersion < 13 then (.error .rangeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  by_cases h : 0 ≤ n ∧ n ≤ 1023 <;> vm_simp [hs, h]

/-! ## Bit sizes and range checks -/

/-- `FITS b`, `QFITS b` (C++ `exec_fits_tinyint8`, `1 ≤ b ≤ 256`): `x` stays if it fits `b` bits
signed; int_ov (NaN if quiet) otherwise. -/
@[vm_spec] theorem fits (st : VmState) (s : Stack) (x : Int) (quiet : Bool) (b : Nat) (hb : 0 < b)
    (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.fitsConst false quiet b))) st =
      if -2 ^ (b - 1) ≤ x ∧ x < 2 ^ (b - 1) then (.ok (), { st with stack := s.push (.int (.num x)) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  have hb' : (b == 0) = false := by simp; omega
  vm_simp [hs, intSignedFitsBits, hb']

/-- `UFITS b`, `QUFITS b` (C++ `exec_ufits_tinyint8`, `1 ≤ b ≤ 256`): `x` stays if it fits `b`
bits unsigned. -/
@[vm_spec] theorem ufits (st : VmState) (s : Stack) (x : Int) (quiet : Bool) (b : Nat) (hb : 0 < b)
    (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.arithExt (.fitsConst true quiet b))) st =
      if 0 ≤ x ∧ x < 2 ^ b then (.ok (), { st with stack := s.push (.int (.num x)) })
      else if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .intOv, { st with stack := s }) := by
  have hb' : (b == 0) = false := by simp; omega
  vm_simp [hs, intUnsignedFitsBits, hb']

/-- `FITSX` (C++ `exec_fits`): the width `n` on top, `0 ≤ n ≤ 1023`; `x` stays if it fits `n` bits
signed (`intSignedFitsBits`), int_ov otherwise. -/
@[vm_spec] theorem fitsx (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.contExt .fitsx)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if intSignedFitsBits x n.toNat then (.ok (), { st with stack := s.push (.int (.num x)) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `UFITSX` (C++ `exec_ufits`): as `fitsx`, unsigned (`intUnsignedFitsBits`). -/
@[vm_spec] theorem ufitsx (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.contExt .ufitsx)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if intUnsignedFitsBits x n.toNat then (.ok (), { st with stack := s.push (.int (.num x)) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `QFITSX` (C++ `exec_fits`, quiet): NaN when `x` does not fit. -/
@[vm_spec] theorem qfitsx (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.contExt .qfitsx)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if intSignedFitsBits x n.toNat then
        if -2 ^ 256 ≤ x ∧ x < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num x)) })
        else (.ok (), { st with stack := s.push (.int .nan) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  by_cases h : intSignedFitsBits x n.toNat = true <;> vm_simp [hs, h]

/-- `QUFITSX` (C++ `exec_ufits`, quiet). -/
@[vm_spec] theorem qufitsx (st : VmState) (s : Stack) (x n : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.contExt .qufitsx)) st =
      if n < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if 1023 < n.toNat then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if intUnsignedFitsBits x n.toNat then
        if -2 ^ 256 ≤ x ∧ x < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num x)) })
        else (.ok (), { st with stack := s.push (.int .nan) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  by_cases h : intUnsignedFitsBits x n.toNat = true <;> vm_simp [hs, h]

/-- `BITSIZE` (C++ `exec_bitsize`, signed): the least number of bits `x` fits signed. -/
@[vm_spec] theorem bitsize (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr .bitsize) st =
      (.ok (), { st with stack := s.push (.int (.num (signedBitsize x))) }) := by
  vm_simp [hs]

/-- `QBITSIZE` (C++ `exec_bitsize`, quiet). -/
@[vm_spec] theorem qbitsize (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.contExt .qbitsize)) st =
      (.ok (), { st with stack := s.push (.int (.num (signedBitsizeTvm x))) }) := by
  vm_simp [hs]

/-- `UBITSIZE`, `QUBITSIZE` (C++ `exec_bitsize`, unsigned): the least number of bits `x` fits
unsigned; a negative `x` is range_chk (NaN if quiet). -/
@[vm_spec] theorem ubitsize (st : VmState) (s : Stack) (x : Int) (quiet : Bool) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.ubitsize quiet)) st =
      if x < 0 then
        if quiet then (.ok (), { st with stack := s.push (.int .nan) }) else (.error .rangeChk, { st with stack := s })
      else (.ok (), { st with stack := s.push (.int (.num (natLenBits x.toNat))) }) := by
  vm_simp [hs]

/-- `ISNAN` on a finite integer: 0. -/
@[vm_spec] theorem isnan_num (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.contExt .isnan)) st = (.ok (), { st with stack := s.push (.int (.num 0)) }) := by
  vm_simp [hs, IntVal.isValid]

/-- `ISNAN` on NaN: -1. -/
@[vm_spec] theorem isnan_nan (st : VmState) (s : Stack) (hs : st.stack = s.push (.int .nan)) :
    ExceptT.run (execInstr (.contExt .isnan)) st = (.ok (), { st with stack := s.push (.int (.num (-1))) }) := by
  vm_simp [hs, IntVal.isValid]

/-- `CHKNAN` on a finite integer: it stays (int_ov if it does not fit). -/
@[vm_spec] theorem chknan_num (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.contExt .chknan)) st =
      if -2 ^ 256 ≤ x ∧ x < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num x)) })
      else (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `CHKNAN` on NaN: int_ov. -/
@[vm_spec] theorem chknan_nan (st : VmState) (s : Stack) (hs : st.stack = s.push (.int .nan)) :
    ExceptT.run (execInstr (.contExt .chknan)) st = (.error .intOv, { st with stack := s }) := by
  vm_simp [hs]

/-- `MINMAX` (C++ `exec_minmax`, mode 6) on two integers that fit 257 bits: the minimum, then the
maximum. -/
@[vm_spec] theorem minmax (st : VmState) (s : Stack) (x y : Int)
    (hx : -2 ^ 256 ≤ x ∧ x < 2 ^ 256) (hy : -2 ^ 256 ≤ y ∧ y < 2 ^ 256)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .minmax) st =
      if y ≤ x then (.ok (), { st with stack := (s.push (.int (.num y))).push (.int (.num x)) })
      else (.ok (), { st with stack := (s.push (.int (.num x))).push (.int (.num y)) }) := by
  vm_simp [hs, hx, hy]

/-- `QMINMAX` (C++ `exec_minmax`, quiet) on two integers that fit 257 bits: as `minmax`. -/
@[vm_spec] theorem qminmax (st : VmState) (s : Stack) (x y : Int)
    (hx : -2 ^ 256 ≤ x ∧ x < 2 ^ 256) (hy : -2 ^ 256 ≤ y ∧ y < 2 ^ 256)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .qminmax) st =
      if y ≤ x then (.ok (), { st with stack := (s.push (.int (.num y))).push (.int (.num x)) })
      else (.ok (), { st with stack := (s.push (.int (.num x))).push (.int (.num y)) }) := by
  vm_simp [hs, hx, hy]

/-! ## Bitwise operations -/

/-- The 257-bit two's complement of `x` (C++ `export_bits` of a `RefInt256`), as the model makes it
(`intToBitsTwos x 257` for an `x` that fits 257 bits). -/
def twos257 (x : Int) : BitString :=
  natToBits (if x ≥ 0 then x.toNat else (1 <<< 257) - (-x).toNat) 257

/-- `intToBitsTwos x 257`: `twos257 x` if `x` fits 257 bits, range_chk otherwise. -/
theorem intToBitsTwos_257 (x : Int) :
    intToBitsTwos x 257 = if -2 ^ 256 ≤ x ∧ x < 2 ^ 256 then .ok (twos257 x) else .error .rangeChk := by
  unfold intToBitsTwos
  simp only [intPow2, Nat.reduceSub, Nat.reduceEqDiff, if_false]
  by_cases h : -2 ^ 256 ≤ x ∧ x < 2 ^ 256
  · have h1 : ¬ (x < -2 ^ 256 ∨ x ≥ 2 ^ 256) := by omega
    rw [if_pos h]
    simp only [h1, decide_false, Bool.false_eq_true, if_false]
    by_cases h2 : x ≥ 0
    · simp only [twos257, h2, if_true]; rfl
    · simp only [twos257, h2, if_false]; rfl
  · have h1 : x < -2 ^ 256 ∨ x ≥ 2 ^ 256 := by omega
    rw [if_neg h]
    simp only [h1, decide_true, if_true]; rfl

/-- `AND` (C++ `exec_and`): the bitwise and of the 257-bit two's complements of `x` and `y`, read
back as a signed integer; range_chk for an operand that does not fit 257 bits. -/
@[vm_spec] theorem and_ (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .and_) st =
      let r := bitsToIntSignedTwos (bitsAnd (twos257 x) (twos257 y))
      if ¬ (-2 ^ 256 ≤ x ∧ x < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if ¬ (-2 ^ 256 ≤ y ∧ y < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num r)) })
      else (.error .intOv, { st with stack := s }) := by
  by_cases hx : -2 ^ 256 ≤ x ∧ x < 2 ^ 256 <;> by_cases hy : -2 ^ 256 ≤ y ∧ y < 2 ^ 256 <;>
    vm_simp [hs, intToBitsTwos_257, hx, hy]

/-- `OR` (C++ `exec_or`): as `and_`, with the bitwise or. -/
@[vm_spec] theorem or (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .or) st =
      let r := bitsToIntSignedTwos (bitsOr (twos257 x) (twos257 y))
      if ¬ (-2 ^ 256 ≤ x ∧ x < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if ¬ (-2 ^ 256 ≤ y ∧ y < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num r)) })
      else (.error .intOv, { st with stack := s }) := by
  by_cases hx : -2 ^ 256 ≤ x ∧ x < 2 ^ 256 <;> by_cases hy : -2 ^ 256 ≤ y ∧ y < 2 ^ 256 <;>
    vm_simp [hs, intToBitsTwos_257, hx, hy]

/-- `XOR` (C++ `exec_xor`): as `and_`, with the bitwise exclusive or. -/
@[vm_spec] theorem xor (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .xor) st =
      let r := bitsToIntSignedTwos (bitsXor (twos257 x) (twos257 y))
      if ¬ (-2 ^ 256 ≤ x ∧ x < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if ¬ (-2 ^ 256 ≤ y ∧ y < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num r)) })
      else (.error .intOv, { st with stack := s }) := by
  by_cases hx : -2 ^ 256 ≤ x ∧ x < 2 ^ 256 <;> by_cases hy : -2 ^ 256 ≤ y ∧ y < 2 ^ 256 <;>
    vm_simp [hs, intToBitsTwos_257, hx, hy]

/-- `QAND` (C++ `exec_and`, quiet): as `and_`, NaN for a result that does not fit. -/
@[vm_spec] theorem qand (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qand)) st =
      let r := bitsToIntSignedTwos (bitsAnd (twos257 x) (twos257 y))
      if ¬ (-2 ^ 256 ≤ x ∧ x < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if ¬ (-2 ^ 256 ≤ y ∧ y < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num r)) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  by_cases hx : -2 ^ 256 ≤ x ∧ x < 2 ^ 256 <;> by_cases hy : -2 ^ 256 ≤ y ∧ y < 2 ^ 256 <;>
    vm_simp [hs, intToBitsTwos_257, hx, hy]

/-- `QOR` (C++ `exec_or`, quiet). -/
@[vm_spec] theorem qor (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qor)) st =
      let r := bitsToIntSignedTwos (bitsOr (twos257 x) (twos257 y))
      if ¬ (-2 ^ 256 ≤ x ∧ x < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if ¬ (-2 ^ 256 ≤ y ∧ y < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num r)) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  by_cases hx : -2 ^ 256 ≤ x ∧ x < 2 ^ 256 <;> by_cases hy : -2 ^ 256 ≤ y ∧ y < 2 ^ 256 <;>
    vm_simp [hs, intToBitsTwos_257, hx, hy]

/-- `QXOR` (C++ `exec_xor`, quiet). -/
@[vm_spec] theorem qxor (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr (.contExt .qxor)) st =
      let r := bitsToIntSignedTwos (bitsXor (twos257 x) (twos257 y))
      if ¬ (-2 ^ 256 ≤ x ∧ x < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if ¬ (-2 ^ 256 ≤ y ∧ y < 2 ^ 256) then (.error .rangeChk, { st with stack := s })
      else if -2 ^ 256 ≤ r ∧ r < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num r)) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  by_cases hx : -2 ^ 256 ≤ x ∧ x < 2 ^ 256 <;> by_cases hy : -2 ^ 256 ≤ y ∧ y < 2 ^ 256 <;>
    vm_simp [hs, intToBitsTwos_257, hx, hy]

/-- `QNOT` (C++ `exec_not`, quiet): `-x - 1`. -/
@[vm_spec] theorem qnot (st : VmState) (s : Stack) (x : Int) (hs : st.stack = s.push (.int (.num x))) :
    ExceptT.run (execInstr (.contExt .qnot)) st =
      if -2 ^ 256 ≤ -x - 1 ∧ -x - 1 < 2 ^ 256 then (.ok (), { st with stack := s.push (.int (.num (-x - 1))) })
      else (.ok (), { st with stack := s.push (.int .nan) }) := by
  vm_simp [hs]

end TvmLean.Spec

import TvmLean.Proofs.Exec.Spec.ArithExt

/-!
# The rounding helpers of the model as operations of `Int`

The shifts with rounding and the shift-and-divide instructions (C++ `exec_shrmod`,
`exec_mulshrmod`, `exec_shldivmod`, arithops.cpp:337, 520, 633) compute with the model's helpers
`rshiftPow2Round`, `modPow2Round` and `divModRound` (TvmLean/Model/Basics/Bytes.lean), one per
rounding mode of the decoder (`rm`: -1 down, 0 to nearest with ties up, 1 up). Their
specifications (`Spec/ArithShift.lean`, `Spec/ArithShiftMod.lean`, `Spec/ArithMulShift.lean`,
`Spec/ArithShlDiv.lean`) state the results through these helpers; here they are the operations of
`Int`:

* `rshiftPow2Round_floor`, `rshiftPow2Round_ceil`, `rshiftPow2Round_nearest`: `x / 2^b`,
  `-((-x) / 2^b)`, `(x + 2^(b-1)) / 2^b`; `modPow2Round_floor`: `x % 2^b`; `modPow2Round_eq`: the
  remainder of the quotient, for any mode;
* `divModRound_floor` (`Spec/ArithExt.lean`), `divModRound_ceil`, `divModRound_nearest` by a
  positive divisor.

The `ADD` forms without a product (`ADDRSHIFTMOD`, C++ `exec_shrmod`, arithops.cpp:386-394) shift a
sum that C++ does not normalize: their quotient is `addShrQuot`, the model's private
`rshiftPow2RoundAddCompat` written out, which is the rounded quotient of `x + w` for a shift of at
most 64 bits (`addShrQuot_eq`); `rw_model_private` rewrites the private definition to its copy
here.

`shift_pre` (scoped to `TvmLean.Spec`) decides the conditions of these handlers on the literals of
an instruction before `vm_simp`, as `arith_pre` of `Spec/ArithExt.lean`: the handler of the three
families is large, and `vm_simp` on it alone exhausts the recursion depth.
-/

namespace TvmLean.Spec

/-! ## Rounding by a power of two -/

/-- The quotient by `p = 2 * h` rounded to nearest, ties up, as the model decides it from the
remainder: `(x + h) / p`. -/
theorem ediv_nearest (x p h : Int) (hp : p = 2 * h) (hh : 0 < h) :
    (if x % p * 2 ≥ p then x / p + 1 else x / p) = (x + h) / p := by
  have hp0 : 0 < p := by omega
  have h1 := Int.emod_add_mul_ediv x p
  have h2 := Int.emod_nonneg x (Int.ne_of_gt hp0)
  have h3 := Int.emod_lt_of_pos x hp0
  generalize x / p = q at *
  generalize x % p = r at *
  split
  · refine ((Int.ediv_emod_unique (r := r - h) hp0).2 ⟨?_, by omega, by omega⟩).1.symm
    rw [Int.mul_add, Int.mul_one]; generalize p * q = t at *; omega
  · refine ((Int.ediv_emod_unique (r := r + h) hp0).2 ⟨?_, by omega, by omega⟩).1.symm
    generalize p * q = t at *; omega

/-- The quotient of a nonnegative `x` by a positive `p` rounded up, `(x + p - 1) / p`, is
`-((-x) / p)`. -/
theorem ediv_ceil (x p : Int) (hp : 0 < p) (_hx : 0 ≤ x) : (x + p - 1) / p = -((-x) / p) := by
  have h1 := Int.emod_add_mul_ediv (-x) p
  have h2 := Int.emod_nonneg (-x) (Int.ne_of_gt hp)
  have h3 := Int.emod_lt_of_pos (-x) hp
  generalize (-x) / p = q at *
  generalize (-x) % p = r at *
  by_cases hr : r = 0
  · subst hr
    refine ((Int.ediv_emod_unique (r := p - 1) hp).2 ⟨?_, by omega, by omega⟩).1
    rw [Int.mul_neg]; generalize p * q = t at *; omega
  · refine ((Int.ediv_emod_unique (r := p - 1 - r) hp).2 ⟨?_, by omega, by omega⟩).1
    rw [Int.mul_neg]; generalize p * q = t at *; omega

/-- `rshiftPow2Round` by 0 bits: the integer itself, whatever the rounding. -/
theorem rshiftPow2Round_zero (x rm : Int) : rshiftPow2Round x 0 rm = x := by
  unfold rshiftPow2Round floorDivPow2 roundNearestDivPow2 ceilDivPow2
  split <;> simp

/-- `modPow2Round` by 0 bits: 0. -/
theorem modPow2Round_zero (x rm : Int) : modPow2Round x 0 rm = 0 := by
  simp [modPow2Round, rshiftPow2Round_zero, intPow2]

/-- `modPow2Round` is the remainder of the quotient `rshiftPow2Round`. -/
theorem modPow2Round_eq (x : Int) (b : Nat) (rm : Int) :
    modPow2Round x b rm = x - rshiftPow2Round x b rm * 2 ^ b := rfl

/-- `rshiftPow2Round` rounding down (rounding mode -1): the division of `Int` by `2^b`. -/
theorem rshiftPow2Round_floor (x : Int) (b : Nat) : rshiftPow2Round x b (-1) = x / 2 ^ b := by
  simp only [rshiftPow2Round, show (-1 : Int) < 0 by decide, decide_true, if_true, floorDivPow2_eq]

/-- `modPow2Round` rounding down: the remainder of `Int` by `2^b`. -/
theorem modPow2Round_floor (x : Int) (b : Nat) : modPow2Round x b (-1) = x % 2 ^ b := by
  rw [modPow2Round_eq, rshiftPow2Round_floor, Int.emod_def, Int.mul_comm]

/-- `rshiftPow2Round` rounding up (rounding mode 1): `-((-x) / 2^b)`. -/
theorem rshiftPow2Round_ceil (x : Int) (b : Nat) : rshiftPow2Round x b 1 = -((-x) / 2 ^ b) := by
  have hp : (0 : Int) < 2 ^ b := Int.pow_pos (by decide)
  simp only [rshiftPow2Round, show ¬ (1 : Int) < 0 by decide, decide_false, Bool.false_eq_true, if_false,
    show ((1 : Int) == 0) = false by decide]
  unfold ceilDivPow2 intPow2
  by_cases hb : b = 0
  · subst hb; simp
  · simp only [show (b == 0) = false by simp [hb], Bool.false_eq_true, if_false]
    by_cases hx : x ≥ 0
    · simp only [hx, decide_true, if_true]; exact ediv_ceil x _ hp hx
    · simp [hx]

/-- `rshiftPow2Round` rounding to nearest (rounding mode 0, ties up), by at least one bit:
`(x + 2^(b-1)) / 2^b`. -/
theorem rshiftPow2Round_nearest (x : Int) (b : Nat) (hb : 0 < b) :
    rshiftPow2Round x b 0 = (x + 2 ^ (b - 1)) / 2 ^ b := by
  simp only [rshiftPow2Round, show ¬ (0 : Int) < 0 by decide, decide_false, Bool.false_eq_true, if_false,
    show ((0 : Int) == 0) = true by decide, if_true]
  unfold roundNearestDivPow2 intPow2
  simp only [show (b == 0) = false by simp; omega, Bool.false_eq_true, if_false, floorDivPow2_eq]
  have hpow : (2 : Int) ^ b = 2 * 2 ^ (b - 1) := by
    rw [← Int.pow_succ']; congr 1; omega
  have hh : (0 : Int) < 2 ^ (b - 1) := Int.pow_pos (by decide)
  rw [← ediv_nearest x _ _ hpow hh, Int.emod_def]
  simp only [ge_iff_le, decide_eq_true_eq, Int.mul_comm (x / 2 ^ b)]

/-! ## Division with rounding -/

/-- The ceiling division of the model (`ceilDiv`) by a positive divisor: `-((-x) / y)`. -/
theorem ceilDiv_of_pos (x y : Int) (hy : 0 < y) : ceilDiv x y = -((-x) / y) := by
  have hf := floorDiv_of_pos (-x) y hy
  have hc : ceilDiv x y = -floorDiv (-x) y := by
    have hy0 : ¬ y = 0 := by omega
    by_cases hx0 : x = 0
    · subst hx0
      simp [ceilDiv, floorDiv, intAbs, hy0]
    have habs : intAbs (-x) = intAbs x := by
      unfold intAbs
      by_cases h : x < 0
      · simp only [h, decide_true, if_true, show ¬ -x < 0 by omega, decide_false, Bool.false_eq_true, if_false]
      · by_cases h' : -x < 0
        · simp only [h, h', decide_true, decide_false, if_true, Bool.false_eq_true, if_false]; omega
        · simp only [h, h', decide_false, Bool.false_eq_true, if_false]; omega
    unfold ceilDiv floorDiv
    simp only [hy0, if_false, habs, show decide (y < 0) = false by simp; omega]
    generalize (intAbs x).toNat / (intAbs y).toNat = q
    generalize (intAbs x).toNat % (intAbs y).toNat = r
    by_cases hx : x < 0
    · simp only [hx, show ¬ -x < 0 by omega, decide_true, decide_false]
      simp
    · simp only [hx, show -x < 0 by omega, decide_true, decide_false]
      by_cases hr : r = 0 <;> simp [hr] <;> omega
  rw [hc, hf]

/-- `divModRound` rounding up (rounding mode 1) by a positive divisor: the quotient `-((-x) / y)`. -/
theorem divModRound_ceil (x y : Int) (hy : 0 < y) :
    divModRound x y 1 = (-((-x) / y), x - -((-x) / y) * y) := by
  have hy0 : ¬ y = 0 := by omega
  simp only [divModRound, hy0, if_false, show ¬ (1 : Int) = -1 by decide, if_true, ceilDiv_of_pos x y hy]

/-- `divModRound` rounding to nearest (rounding mode 0, ties up) by a positive divisor: the quotient
`(2 * x + y) / (2 * y)`. -/
theorem divModRound_nearest (x y : Int) (hy : 0 < y) :
    divModRound x y 0 = ((2 * x + y) / (2 * y), x - (2 * x + y) / (2 * y) * y) := by
  have hy0 : ¬ y = 0 := by omega
  simp only [divModRound, hy0, if_false, show ¬ (0 : Int) = -1 by decide, show ¬ (0 : Int) = 1 by decide,
    floorDiv_of_pos x y hy, show decide (y > 0) = true by simp; omega, show decide (y < 0) = false by simp; omega,
    Bool.true_and, Bool.false_and, Bool.or_false, decide_eq_true_eq]
  have hq : (if (x - x / y * y) * 2 ≥ y then x / y + 1 else x / y) = (2 * x + y) / (2 * y) := by
    have h2 : (0 : Int) < 2 * y := by omega
    have h1 := Int.emod_add_mul_ediv x y
    have h2' := Int.emod_nonneg x (Int.ne_of_gt hy)
    have h3 := Int.emod_lt_of_pos x hy
    rw [show x - x / y * y = x % y by rw [Int.emod_def, Int.mul_comm]]
    generalize x / y = q at *
    generalize x % y = r at *
    split
    · refine ((Int.ediv_emod_unique (r := 2 * r - y) h2).2 ⟨?_, by omega, by omega⟩).1.symm
      rw [Int.mul_add, Int.mul_one, Int.mul_assoc]; generalize y * q = t at *; omega
    · refine ((Int.ediv_emod_unique (r := 2 * r + y) h2).2 ⟨?_, by omega, by omega⟩).1.symm
      rw [Int.mul_assoc]; generalize y * q = t at *; omega
  rw [hq]

/-! ## What the handlers leave of the rounding mode -/

/-- A shift by 0 bits from the stack rounds down (C++ `exec_shrmod`, arithops.cpp:383-385;
`exec_mulshrmod`, arithops.cpp:548-550): the quotient is the integer itself either way. -/
theorem rshiftPow2Round_ite_zero (x : Int) (b : Nat) (rm : Int) :
    rshiftPow2Round x b (if b = 0 then -1 else rm) = rshiftPow2Round x b rm := by
  by_cases hb : b = 0
  · subst hb; simp [rshiftPow2Round_zero]
  · simp [hb]

/-- The remainder of a shift by 0 bits is 0 whatever the rounding. -/
theorem modPow2Round_ite_zero (x : Int) (b : Nat) (rm : Int) :
    modPow2Round x b (if b = 0 then -1 else rm) = modPow2Round x b rm := by
  simp only [modPow2Round_eq, rshiftPow2Round_ite_zero]

/-- The handler's check of the rounding mode passes for a mode of the decoder (`-1`, `0`, `1`) and
for `-1` (a shift by 0). -/
theorem roundMode_ite_ok (c : Prop) [Decidable c] (rm : Int) (h : rm = -1 ∨ rm = 0 ∨ rm = 1) :
    ((((if c then (-1 : Int) else rm) != -1) = true ∧ ((if c then (-1 : Int) else rm) != 0) = true) ∧
      ((if c then (-1 : Int) else rm) != 1) = true) = False := by
  by_cases hc : c <;> simp only [hc, if_true, if_false] <;> rcases h with rfl | rfl | rfl <;> decide

/-- The handler's check of the rounding mode passes for a mode of the decoder (`-1`, `0`, `1`). -/
theorem roundMode_prop_ok (rm : Int) (h : rm = -1 ∨ rm = 0 ∨ rm = 1) :
    (((rm != -1) = true ∧ (rm != 0) = true) ∧ (rm != 1) = true) = False := by
  rcases h with rfl | rfl | rfl <;> decide

/-- The range check of a shift from the stack in the quiet forms (C++ `exec_mulshrmod`,
`exec_shldivmod`: range_chk unless quiet from version 13) as an `if` on the flag: instantiated
with a literal flag it reduces by `if_true`/`if_false` alone (`False`, not `True ∨ p`, which the
simp set of a step leaves). -/
theorem quiet_or_and (q : Bool) (p r : Prop) : ((q = false ∨ p) ∧ r) ↔ (if q then p ∧ r else r) := by
  cases q <;> simp

theorem quiet_or_and' (q : Bool) (p r : Prop) : ((¬ q = true ∨ p) ∧ r) ↔ (if q then p ∧ r else r) := by
  cases q <;> simp

/-- The range check of a shift from the stack from version 14 (C++ `exec_shrmod`: range_chk
unless quiet) as an `if` on the flag (`quiet_or_and`). -/
theorem quiet_and (q : Bool) (r : Prop) : (q = false ∧ r) ↔ (if q then False else r) := by
  cases q <;> simp

theorem quiet_and' (q : Bool) (r : Prop) : (¬ q = true ∧ r) ↔ (if q then False else r) := by
  cases q <;> simp

/-! ## The quotient of the `ADD` forms: a sum C++ does not normalize

`exec_shrmod` adds `w` to `x` without normalizing the 52-bit digits of the `BigInt` and shifts that
(arithops.cpp:386-394); for a shift beyond the digits, `rshift_any` takes the sign of the top
digit, which may differ from that of `x + w`. The model's `rshiftPow2RoundAddCompat` is private to
`Semantics/Exec/Arith/Ext.lean`; `addShrQuot` is the same definition here, with its helpers
(`rw_model_private` rewrites the one to the other). -/

/-- The 52-bit digits of `q` (least significant first, each in `[-2^51, 2^51)`), at most `fuel` of
them, after `out` (`intToBigInt52DigitsAux` of the model). -/
def digits52Aux (q : Int) (out : Array Int) : Nat → Array Int
  | 0 => out
  | fuel + 1 =>
      if q != 0 then
        let r : Int := Int.emod q (intPow2 52)
        let d : Int :=
          if decide (r >= intPow2 (52 - 1)) then
            r - intPow2 52
          else
            r
        digits52Aux ((q - d) / intPow2 52) (out.push d) fuel
      else
        out

/-- The 52-bit digits of `n`, `#[0]` for 0 (`intToBigInt52Digits` of the model). -/
def digits52 (n : Int) : Array Int :=
  if n == 0 then
    #[0]
  else
    let out := digits52Aux n #[] (n.natAbs + 1)
    if out.isEmpty then #[0] else out

/-- Digits added one by one, not normalized (`addAnyNoNormalize` of the model). -/
def addDigits (x y : Array Int) : Array Int :=
  if y.size <= x.size then
    Id.run do
      let mut out := x
      for i in [0:y.size] do
        out := out.set! i (out[i]! + y[i]!)
      out
  else
    Id.run do
      let mut out := y
      for i in [0:x.size] do
        out := out.set! i (out[i]! + x[i]!)
      out

/-- The quotient of `x + w` by `2^shift` as C++ `exec_shrmod` computes it for the `ADD` forms
(`rshiftPow2RoundAddCompat` of the model): beyond the digits of the sum, the sign of its top
digit. -/
def addShrQuot (x w : Int) (shift : Nat) (roundMode : Int) : Int :=
  let tmp : Int := x + w
  let xDigits := digits52 x
  let wDigits := digits52 w
  let tmpDigits := addDigits xDigits wDigits
  let fastLimit : Nat := tmpDigits.size * 52 + (64 - 52)
  if shift > fastLimit then
    let top : Int := tmpDigits[tmpDigits.size - 1]!
    if roundMode == 0 then
      0
    else if decide (roundMode < 0) then
      if decide (top < 0) then -1 else 0
    else
      if decide (top > 0) then 1 else 0
  else
    rshiftPow2Round tmp shift roundMode

/-- A loop over a range in `Id` keeps an invariant that every step keeps. -/
theorem id_forIn_range_keeps {β : Type} (P : β → Prop) {r : Std.Range} {init : β}
    {f : Nat → β → Id (ForInStep β)} (h0 : P init)
    (hf : ∀ i b, P b → P (f i b).run.value) : P (Id.run (forIn r init f)) := by
  rw [Std.Range.forIn_eq_forIn_range']
  generalize List.range' r.start r.size r.step = l
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih =>
    simp only [List.forIn_cons]
    have := hf a init h0
    cases hfa : f a init with
    | done b => rw [hfa] at this; exact this
    | yield b => rw [hfa] at this; exact ih this

theorem digits52_size_pos (n : Int) : 0 < (digits52 n).size := by
  unfold digits52
  split
  · simp
  · simp only []
    split
    · simp
    · rename_i h; simp only [Array.isEmpty_iff] at h; exact Array.size_pos_iff.mpr h

theorem addDigits_size_pos (x y : Array Int) (hx : 0 < x.size) (hy : 0 < y.size) :
    0 < (addDigits x y).size := by
  unfold addDigits
  split
  · exact id_forIn_range_keeps (fun a : Array Int => 0 < a.size) hx (fun i b hb => by simpa using hb)
  · exact id_forIn_range_keeps (fun a : Array Int => 0 < a.size) hy (fun i b hb => by simpa using hb)

/-- For a shift of at most 64 bits the quotient of the `ADD` forms is the rounded quotient of
`x + w`: the shift is within the digits of the sum. -/
theorem addShrQuot_eq (x w : Int) (b : Nat) (rm : Int) (hb : b ≤ 64) :
    addShrQuot x w b rm = rshiftPow2Round (x + w) b rm := by
  have h := addDigits_size_pos (digits52 x) (digits52 w) (digits52_size_pos x) (digits52_size_pos w)
  unfold addShrQuot
  simp only []
  rw [if_neg (by omega)]

/-- A shift by 0 bits from the stack rounds down: the same quotient. -/
theorem addShrQuot_ite_zero (x w : Int) (b : Nat) (rm : Int) :
    addShrQuot x w b (if b = 0 then -1 else rm) = addShrQuot x w b rm := by
  by_cases hb : b = 0
  · subst hb
    rw [addShrQuot_eq _ _ _ _ (by omega), addShrQuot_eq _ _ _ _ (by omega)]
    simp [rshiftPow2Round_zero]
  · simp [hb]

open Lean Meta Elab Tactic in
/-- `rw_model_private f => g`: the applications of a private definition `TvmLean.f` of the model
(which this module cannot name) in the goal rewritten to `g`, a definition with the same body: the
equation `∀ xs, f xs = g xs` is an auxiliary theorem whose proof `Eq.refl` the kernel checks by
unfolding both. -/
elab "rw_model_private " f:ident " => " g:ident : tactic => withMainContext do
  let user := `TvmLean ++ f.getId
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some c := t.find? (fun e => e.isConst && isPrivateName e.constName! && privateToUserName e.constName! == user)
    | throwError "rw_model_private: no {user} in the goal"
  let pc := c.constName!
  let gName ← realizeGlobalConstNoOverloadWithInfo g
  let info ← getConstInfo pc
  let lvls := info.levelParams.map Level.param
  let (eqTy, pf) ← forallTelescope info.type fun xs _ => do
    let lhs := mkAppN (.const pc lvls) xs
    let ty ← mkForallFVars xs (← mkEq lhs (mkAppN (.const gName lvls) xs))
    let pf ← mkLambdaFVars xs (← mkEqRefl lhs)
    return (ty, pf)
  let thm ← mkAuxTheorem eqTy pf
  let s ← ({} : SimpTheorems).addConst thm.constName!
  let ctx ← Simp.mkContext (simpTheorems := #[s]) (congrTheorems := ← getSimpCongrTheorems)
  match ← simpTarget goal ctx with
  | (none, _) => replaceMainGoal []
  | (some g', _) => replaceMainGoal [g']

/-- The conditions of the handlers of the shift families on the literals of the instruction
decided before `vm_simp` (`arith_pre` of `Spec/ArithExt.lean`, with the `Option` of a constant
shift). -/
scoped macro "shift_pre" : tactic =>
  `(tactic| try simp only [TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok,
    Nat.reduceBEq, Nat.reduceBNe, Int.reduceBNe, Int.reduceBEq, Bool.and_false, Bool.false_and,
    Bool.and_true, Bool.true_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true, reduceIte, Int.reduceNeg,
    Option.isSome_some, Option.isNone_some, Option.isSome_none, Option.isNone_none])

end TvmLean.Spec

import TvmLean.Proofs.Exec.Spec.CellExt

/-!
# Specifications: integers stored with the width on the stack, quiet loads, `STVARINT`

In the format of `Proofs/Exec/Spec/CellExt.lean` (a builder or slice is any; a width from the
stack is an integer, range_chk if it is negative or above the limit, C++ `pop_smallint_range`):

* `STIX`, `STUX`, `STIXR`, `STUXR` and their quiet forms (C++ `exec_store_int_var`,
  cellops.cpp:600, and `exec_store_int_common`, cellops.cpp:377): `stIntVar`, `stIntVar_rev`; a
  width of 0 stores nothing and takes only 0;
* `LDIQ`, `LDUQ`, `PLDIQ`, `PLDUQ` (C++ `exec_load_int_fixed2`, cellops.cpp:1103, and
  `exec_load_int_common`, cellops.cpp:957): `loadIntQ` (the non-quiet forms are `Spec.loadInt` of
  `Spec/Cell.lean`);
* `STVARINT16`, `STVARINT32` (C++ `exec_store_var_integer`, tonops.cpp:1587, and
  `store_var_integer`, tonops.cpp:2566, signed): `stVarInt`; the length in bytes of the
  two's complement, which always fits it (`intToBitsTwos_varInt`).
-/

namespace TvmLean.Spec

/-- The two's complement of `x` in 0 bits: nothing. -/
theorem twosBits_zero (x : Int) : twosBits x 0 = #[] := by
  simp [twosBits, natToBits]

/-- The model's two's complement in 0 bits: nothing, whatever `x`. -/
theorem intToBitsTwos_zero (x : Int) : intToBitsTwos x 0 = .ok #[] := by
  simp [intToBitsTwos]; rfl

/-- A natural number is below 2 to the power of its length in bits. -/
theorem lt_two_pow_natLenBits (m : Nat) : m < 2 ^ natLenBits m := by
  unfold natLenBits
  split
  · subst_vars; decide
  · exact Nat.lt_log2_self

/-- `m < 2^k` read in `Int`. -/
theorem natCast_lt_two_pow {m k : Nat} (h : m < 2 ^ k) : (m : Int) < 2 ^ k := by
  have : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
  rw [← this]; exact Int.ofNat_lt.mpr h

/-- The two's complement of `x` in whole bytes, as many as its length in bits needs (C++
`store_var_integer`, tonops.cpp:2567-2578, which checks that the store succeeds): `x` always fits,
the model gives `twosBits`. -/
theorem intToBitsTwos_varInt (x : Int) :
    intToBitsTwos x ((intSignedBitSizeTwos x + 7) / 8 * 8) =
      .ok (twosBits x ((intSignedBitSizeTwos x + 7) / 8 * 8)) := by
  by_cases hx0 : x = 0
  · subst hx0
    simp only [intSignedBitSizeTwos, if_true, Nat.zero_add, Nat.reduceDiv, Nat.zero_mul, intToBitsTwos_zero,
      twosBits_zero]
  generalize hL : (intSignedBitSizeTwos x + 7) / 8 * 8 = L
  have hbs : intSignedBitSizeTwos x ≤ L := by omega
  have hbs0 : 0 < intSignedBitSizeTwos x := by
    unfold intSignedBitSizeTwos
    rw [if_neg hx0]; split <;> omega
  have hL0 : 0 < L := by omega
  rw [intToBitsTwos_eq x L hL0, if_pos]
  by_cases hpos : x > 0
  · have hm := lt_two_pow_natLenBits x.toNat
    have hb : intSignedBitSizeTwos x = natLenBits x.toNat + 1 := by
      unfold intSignedBitSizeTwos; simp [hx0, hpos]
    have hle : 2 ^ natLenBits x.toNat ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h1 := natCast_lt_two_pow (Nat.lt_of_lt_of_le hm hle)
    have h2 : (x.toNat : Int) = x := by omega
    have h3 : (0 : Int) < 2 ^ (L - 1) := Int.pow_pos (by decide)
    omega
  · have hneg : x < 0 := by omega
    have hm := lt_two_pow_natLenBits (-x - 1).toNat
    have hb : intSignedBitSizeTwos x = natLenBits (-x - 1).toNat + 1 := by
      unfold intSignedBitSizeTwos; simp [hx0, hpos]
    have hle : 2 ^ natLenBits (-x - 1).toNat ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h1 := natCast_lt_two_pow (Nat.lt_of_lt_of_le hm hle)
    have h2 : ((-x - 1).toNat : Int) = -x - 1 := by omega
    omega

/-- The conditions of the handlers on the literals of the instruction decided before `vm_simp`
(`cell_pre` of `Spec/CellExt.lean`, the handler unfolded by `unfoldModelRun`). -/
local macro "cell_int_pre" : tactic =>
  `(tactic| try simp only [TvmLean.Exec.reduceExecInstrRun, TvmLean.Exec.unfoldModelRun, VM.run_bind, VM.run_get,
    VM.bindRes_ok, Nat.reduceBEq, Nat.reduceBNe, Nat.reduceAdd, Bool.and_false, Bool.false_and, Bool.and_true,
    Bool.true_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, if_false, if_true, reduceIte, Nat.reduceEqDiff, Nat.reduceShiftLeft])

set_option maxHeartbeats 2000000 in
/-- `STIX`, `STUX` and their quiet forms `STIXQ`, `STUXQ` (C++ `exec_store_int_var`,
cellops.cpp:600-607, opcodes `CF00`, `CF01`, `CF04`, `CF05`; `exec_store_int_common`,
cellops.cpp:377-406): the width `n` on top, `0 ≤ n ≤ 257` (256 unsigned; range_chk), then the
builder, then the integer, stored in `n` bits (unsigned: `natToBits`, signed: `twosBits`), then 0
if quiet; if the builder has no room, cell_ov, or (quiet) the integer and the builder back and -1;
if the integer does not fit, range_chk, or (quiet) both back and 1. -/
@[vm_spec] theorem stIntVar (st : VmState) (s : Stack) (x : Int) (b : Builder) (unsigned quiet : Bool) (n : Int)
    (hs : st.stack = ((s.push (.int (.num x))).push (.builder b)).push (.int (.num n))) :
    ExceptT.run (execInstr (.stIntVar unsigned false quiet)) st =
      if n < 0 then (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.builder b) })
      else if (if unsigned then 256 else 257) < n.toNat then
        (.error .rangeChk, { st with stack := (s.push (.int (.num x))).push (.builder b) })
      else if b.canExtendBy n.toNat then
        if (if n.toNat = 0 then x = 0 else if unsigned then 0 ≤ x ∧ x < 2 ^ n.toNat
            else -2 ^ (n.toNat - 1) ≤ x ∧ x < 2 ^ (n.toNat - 1)) then
          let s1 := s.push (.builder (b.storeBits (if unsigned then natToBits x.toNat n.toNat else twosBits x n.toNat)))
          (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1 })
        else if quiet then
          (.ok (), { st with stack := ((s.push (.int (.num x))).push (.builder b)).push (.int (.num 1)) })
        else (.error .rangeChk, { st with stack := s })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.int (.num x))).push (.builder b)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  by_cases hn0 : n.toNat = 0
  · cases unsigned <;> cases quiet <;> cell_int_pre <;>
      vm_simp [hs, hn0, twosBits_zero, intToBitsTwos_zero]
  · have hn : 0 < n.toNat := by omega
    cases unsigned <;> cases quiet <;> cell_int_pre <;>
      vm_simp [hs, hn0, intSignedFitsBits, intToBitsTwos_eq x n.toNat hn]

set_option maxHeartbeats 2000000 in
/-- `STIXR`, `STUXR` and their quiet forms `STIXRQ`, `STUXRQ` (C++ `exec_store_int_var`,
cellops.cpp:600-607, opcodes `CF02`, `CF03`, `CF06`, `CF07`): as `stIntVar`, the integer above the
builder. -/
@[vm_spec] theorem stIntVar_rev (st : VmState) (s : Stack) (x : Int) (b : Builder) (unsigned quiet : Bool) (n : Int)
    (hs : st.stack = ((s.push (.builder b)).push (.int (.num x))).push (.int (.num n))) :
    ExceptT.run (execInstr (.stIntVar unsigned true quiet)) st =
      if n < 0 then (.error .rangeChk, { st with stack := (s.push (.builder b)).push (.int (.num x)) })
      else if (if unsigned then 256 else 257) < n.toNat then
        (.error .rangeChk, { st with stack := (s.push (.builder b)).push (.int (.num x)) })
      else if b.canExtendBy n.toNat then
        if (if n.toNat = 0 then x = 0 else if unsigned then 0 ≤ x ∧ x < 2 ^ n.toNat
            else -2 ^ (n.toNat - 1) ≤ x ∧ x < 2 ^ (n.toNat - 1)) then
          let s1 := s.push (.builder (b.storeBits (if unsigned then natToBits x.toNat n.toNat else twosBits x n.toNat)))
          (.ok (), { st with stack := if quiet then s1.push (.int (.num 0)) else s1 })
        else if quiet then
          (.ok (), { st with stack := ((s.push (.builder b)).push (.int (.num x))).push (.int (.num 1)) })
        else (.error .rangeChk, { st with stack := s })
      else if quiet then
        (.ok (), { st with stack := ((s.push (.builder b)).push (.int (.num x))).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  by_cases hn0 : n.toNat = 0
  · cases unsigned <;> cases quiet <;> cell_int_pre <;>
      vm_simp [hs, hn0, twosBits_zero, intToBitsTwos_zero]
  · have hn : 0 < n.toNat := by omega
    cases unsigned <;> cases quiet <;> cell_int_pre <;>
      vm_simp [hs, hn0, intSignedFitsBits, intToBitsTwos_eq x n.toNat hn]

/-- `LDIQ n`, `LDUQ n`, `PLDIQ n`, `PLDUQ n` (C++ `exec_load_int_fixed2`, cellops.cpp:1103-1108,
opcodes `D70Cxx`-`D70Fxx`, `xx` = `n - 1`; `exec_load_int_common`, cellops.cpp:957-980,
`1 ≤ n ≤ 256`): the first `n` bits of the slice as an integer (`loadIntValue`), then the rest of the
slice unless prefetching, then -1; if the slice is shorter, the slice back unless prefetching, then
0. -/
@[vm_spec] theorem loadIntQ (st : VmState) (s : Stack) (sl : Slice) (unsigned prefetch : Bool) (n : Nat)
    (hn : 0 < n) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.loadInt unsigned prefetch true n)) st =
      if sl.haveBits n then
        if (IntVal.num (loadIntValue unsigned (sl.readBits n))).signedFits257 then
          (.ok (), { st with
            stack :=
              (if prefetch then s.push (.int (.num (loadIntValue unsigned (sl.readBits n))))
                else (s.push (.int (.num (loadIntValue unsigned (sl.readBits n))))).push (.slice (sl.advanceBits n))).push
                (.int (.num (-1))) })
        else (.error .intOv, { st with stack := s })
      else (.ok (), { st with stack := (if prefetch then s else s.push (.slice sl)).push (.int (.num 0)) }) := by
  have hn' : (n == 0) = false := by simp; omega
  cases unsigned <;> cases prefetch <;> cell_int_pre <;> vm_simp [hs, hn']

set_option maxHeartbeats 2000000 in
/-- `STVARINT16` (`k = 16`) and `STVARINT32` (`k = 32`) (C++ `exec_store_var_integer`,
tonops.cpp:1587-1606, opcodes `FA03`, `FA07`; `store_var_integer`, tonops.cpp:2566-2579, signed):
the integer on top, the builder below: the length `l` in bytes of its two's complement in 4 or 5
bits (range_chk if `l` does not fit them), then the two's complement in `l` bytes; cell_ov if the
builder has no room. -/
@[vm_spec] theorem stVarInt (st : VmState) (s : Stack) (b : Builder) (x : Int) (k : Nat) (hk : k = 16 ∨ k = 32)
    (hs : st.stack = (s.push (.builder b)).push (.int (.num x))) :
    ExceptT.run (execInstr (.cellExt (.stVarInt true k))) st =
      let lb := if k = 16 then 4 else 5
      let l := (intSignedBitSizeTwos x + 7) / 8
      if 2 ^ lb ≤ l then (.error .rangeChk, { st with stack := s })
      else if b.canExtendBy (lb + l * 8) then
        (.ok (), { st with stack := s.push (.builder (b.storeBits (natToBits l lb ++ twosBits x (l * 8)))) })
      else (.error .cellOv, { st with stack := s }) := by
  rcases hk with rfl | rfl <;> cell_int_pre <;> vm_simp [hs, Nat.reduceShiftLeft, intToBitsTwos_varInt x]

end TvmLean.Spec

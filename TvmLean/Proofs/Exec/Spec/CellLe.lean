import TvmLean.Proofs.Exec.Spec.CellExt
import TvmLean.Proofs.Exec.Spec.Crypto

/-!
# Specifications: little-endian integers in slices and builders

In the format of `Proofs/Exec/Spec/Stack.lean`, on any slice or builder; the forms exist for 4 and 8
bytes (C++ `exec_load_le_int`, `exec_store_le_int`, cellops.cpp).

* `{P}LD{I,U}LE{4,8}{Q}`: the first `bytes` bytes of the slice read as a little-endian integer
  (`Spec.leIntValue`), then the rest of the slice unless prefetching, then -1 if quiet; if the slice
  is shorter, cell_und, or (quiet) the slice back unless prefetching and 0;
* `ST{I,U}LE{4,8}`: the integer below the builder stored as `bytes` bytes, little-endian
  (`leBytesToBitString` of its big-endian bits); cell_ov if the builder has no room, range_chk if
  the integer does not fit.
-/

namespace TvmLean.Spec

/-- The conditions of the handler on literals decided before `vm_simp` (as in `Spec/CellExt.lean`). -/
local macro "cell_pre" : tactic =>
  `(tactic| try simp only [TvmLean.Exec.reduceExecInstrRun, VM.run_bind, VM.run_get, VM.bindRes_ok,
    Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, Bool.or_false,
    Bool.false_or, Bool.or_true, Bool.true_or, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false,
    if_true, reduceIte, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reduceMul, ne_eq, not_true_eq_false,
    and_false, false_and, and_self])

/-- The integer `{P}LD{I,U}LE{bytes}` reads: the first `bytes` bytes of the slice, little-endian,
unsigned or (`natToIntSignedTwos`) signed. -/
abbrev leIntValue (unsigned : Bool) (bytes : Nat) (sl : Slice) : Int :=
  if unsigned then Int.ofNat (bytesToNatLE (bitStringToBytesBE (sl.readBits (bytes * 8))))
  else natToIntSignedTwos (bytesToNatLE (bitStringToBytesBE (sl.readBits (bytes * 8)))) (bytes * 8)

/-- `{P}LD{I,U}LE{bytes}{Q}` on the stack `s sl` (`bytes` 4 or 8). -/
@[vm_spec] theorem loadLeInt (st : VmState) (s : Stack) (sl : Slice) (u : Bool) (bytes : Nat) (p q : Bool)
    (hb : bytes = 4 ∨ bytes = 8) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.cellOp (.loadLeInt u bytes p q))) st =
      if sl.haveBits (bytes * 8) then
        if (IntVal.num (leIntValue u bytes sl)).signedFits257 then
          let s1 := s.push (.int (.num (leIntValue u bytes sl)))
          let s2 := if p then s1 else s1.push (.slice { sl with bitPos := sl.bitPos + bytes * 8 })
          (.ok (), { st with stack := if q then s2.push (.int (.num (-1))) else s2 })
        else (.error .intOv, { st with stack := s })
      else if q then
        (.ok (), { st with stack := (if p then s else s.push (.slice sl)).push (.int (.num 0)) })
      else (.error .cellUnd, { st with stack := s }) := by
  rcases hb with rfl | rfl <;> cases u <;> cases p <;> cases q <;> cell_pre <;>
    vm_simp [hs, prefetchBytesCellUnd_eq, leIntValue]

/-- `ST{I,U}LE{bytes}` on the stack `s x b` (`bytes` 4 or 8). -/
@[vm_spec] theorem stLeInt (st : VmState) (s : Stack) (x : Int) (b : Builder) (u : Bool) (bytes : Nat)
    (hb : bytes = 4 ∨ bytes = 8) (hs : st.stack = (s.push (.int (.num x))).push (.builder b)) :
    ExceptT.run (execInstr (.cellExt (.stLeInt u bytes))) st =
      if b.canExtendBy (bytes * 8) then
        if (if u then 0 ≤ x ∧ x < 2 ^ (bytes * 8) else -2 ^ (bytes * 8 - 1) ≤ x ∧ x < 2 ^ (bytes * 8 - 1)) then
          (.ok (), { st with stack := s.push (.builder (b.storeBits (leBytesToBitString
            (if u then natToBits x.toNat (bytes * 8) else twosBits x (bytes * 8)) bytes))) })
        else (.error .rangeChk, { st with stack := s })
      else (.error .cellOv, { st with stack := s }) := by
  rcases hb with rfl | rfl <;> cases u <;> cell_pre <;>
    vm_simp [hs, intSignedFitsBits, intUnsignedFitsBits, intToBitsTwos_eq x _ (by decide : 0 < 32),
      intToBitsTwos_eq x _ (by decide : 0 < 64)]

end TvmLean.Spec

import TvmLean.Proofs.Exec.Spec.StackExt

/-!
# Specifications: `BLKSWX`

In the format of `Proofs/Exec/Spec/StackExt.lean` (the counts from the stack are integers, range_chk
if negative or above `2^30 - 1`, before global version 4 above 255, C++ `pop_smallint_range`):
`BLKSWX` (C++ `exec_blkswap_x`, stackops.cpp:436), `BLKSWAP x,y` with `x` and `y` from the stack.
-/

namespace TvmLean.Spec

set_option maxHeartbeats 2000000 in
/-- `BLKSWX` (C++ `exec_blkswap_x`, stackops.cpp:436-450, opcode `63`): `y` on top, then `x`; the
`y` values on top of the rest move below the `x` values under them (`std::rotate`), as
`BLKSWAP x,y` (`Spec.blkSwap`); nothing if `x` or `y` is 0; from global version 4 the entries over
255 charged one gas each (stackops.cpp:443-445); stk_und if the rest has fewer than `x + y`
values. -/
@[vm_spec] theorem blkSwapX (st : VmState) (s : Stack) (x y : Int)
    (hs : st.stack = (s.push (.int (.num x))).push (.int (.num y))) :
    ExceptT.run (execInstr .blkSwapX) st =
      if y < 0 then (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < y.toNat then
        (.error .rangeChk, { st with stack := s.push (.int (.num x)) })
      else if x < 0 then (.error .rangeChk, { st with stack := s })
      else if (if 4 ≤ st.globalVersion then 2 ^ 30 - 1 else 255) < x.toNat then (.error .rangeChk, { st with stack := s })
      else if x.toNat + y.toNat ≤ s.size then
        if 0 < x.toNat ∧ 0 < y.toNat then
          let n := s.size
          let s' := s.take (n - (x.toNat + y.toNat)) ++ s.extract (n - y.toNat) n ++
            s.extract (n - (x.toNat + y.toNat)) (n - y.toNat)
          if 255 < x.toNat + y.toNat ∧ 4 ≤ st.globalVersion then
            (.ok (), { st with stack := s', gas := st.gas.consume (x.toNat + y.toNat - 255 : Nat) })
          else (.ok (), { st with stack := s' })
        else (.ok (), { st with stack := s })
      else (.error .stkUnd, { st with stack := s }) := by
  vm_simp [hs, Nat.shiftLeft_eq, VmState.consumeGas]

end TvmLean.Spec

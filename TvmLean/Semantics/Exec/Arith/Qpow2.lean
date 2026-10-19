import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
/-- `QPOW2`, as C++ `exec_pow2(st, quiet := true)` (crypto/vm/arithops.cpp at commit 3d478cb):
the argument is popped with `pop_long`, which maps NaN and integers outside 64 bits to `LLONG_MIN`.
An argument outside `0..1023` throws `range_chk` before TVM 13; since TVM 13 the quiet form pushes
NaN instead. Inside the range the result `2^x` is pushed quietly (NaN if it does not fit 257 bits). -/
def execInstrArithQpow2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qpow2 =>
      let v ← VM.popInt
      let inRange : Option Nat :=
        match v with
        | .num n => if 0 ≤ n ∧ n ≤ 1023 then some n.toNat else none
        | .nan => none
      match inRange with
      | some e => VM.pushIntQuiet (.num (intPow2 e)) true
      | none =>
          if (← get).globalVersion < 13 then
            throw .rangeChk
          else
            VM.pushIntQuiet .nan true
  | _ => next

end TvmLean

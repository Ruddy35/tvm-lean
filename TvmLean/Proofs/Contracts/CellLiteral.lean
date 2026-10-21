import Lean
import TvmLean.Model.Cell.Cell

/-!
# Bit-string literals for cells

`cellBits! "<hex>"` is the bit string of a cell's data in Fift's `x{...}` notation: hexadecimal
digits, four bits each, and an optional final `_`, which removes the trailing zeros and the `1`
before them (the completion tag, `td::BitSlice` / `x{...}` in `crypto/fift/words.cpp`). It
elaborates to the explicit array `#[true, false, ...]`: the cell literals of
`tools/boc2lean/boc2lean.py` are closed constructor terms, which the kernel and `simp`/`whnf`
take apart without unfolding a decoding function. `parseHexBits?` is the reading, also usable as a
function.
-/

namespace TvmLean

/-- The bits of a hexadecimal digit, most significant first. -/
def hexDigitBits? (c : Char) : Option (List Bool) :=
  let v? : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  v?.map fun v => [v.testBit 3, v.testBit 2, v.testBit 1, v.testBit 0]

/-- Drops the completion tag: the trailing `false`s and the `true` before them (`none` if there is
no `true`). -/
def dropCompletionTag? (bs : List Bool) : Option (List Bool) :=
  match bs.reverse.dropWhile (· == false) with
  | true :: rest => some rest.reverse
  | _ => none

/-- Fift `x{...}` notation: hex digits, optionally ending in `_` (completion tag). -/
def parseHexBits? (s : String) : Option BitString := do
  let (digits, tagged) :=
    if s.endsWith "_" then (s.dropRight 1, true) else (s, false)
  let bits ← digits.toList.mapM hexDigitBits?
  let bits := bits.flatten
  let bits ← if tagged then dropCompletionTag? bits else some bits
  return bits.toArray

open Lean Elab Term in
/-- `cellBits! "<hex>"`: the explicit bit array of `x{<hex>}`. -/
elab "cellBits! " s:str : term => do
  match parseHexBits? s.getString with
  | some bs => return toExpr bs
  | none => throwErrorAt s "cellBits!: expected hex digits, optionally ending in `_`"

example : cellBits! "A_" = #[true, false] := rfl
example : cellBits! "C_" = #[true] := rfl
example : cellBits! "8_" = #[] := rfl
example : cellBits! "4_" = #[false] := rfl
example : cellBits! "F2" = #[true, true, true, true, false, false, true, false] := rfl
example : cellBits! "" = #[] := rfl

end TvmLean

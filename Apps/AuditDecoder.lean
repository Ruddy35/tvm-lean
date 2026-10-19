import TvmLean.Model

/-!
# Decoder audit: the model's side

For every 24-bit value `v` in `[lo, hi)` the slice `v (24 bits) ++ tail ++ 4 empty refs` is decoded
with `decodeCp0WithBits`, exactly as `tools/audit/decoder/cpp.fif` asks the C++ dispatch table.

    tvm-lean-audit-decoder len  <tail0|tail1> <lo> <hi>   one line per v: bits + 65536*refs, 0 if invalid
    tvm-lean-audit-decoder name <tail0|tail1> <lo> <hi>   one line per v with v % 256 = 0: v, length, instruction
-/

open TvmLean

def mkSlice (v : Nat) (tailBit : Bool) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits v 24 ++ Array.replicate 480 tailBit)
    #[Cell.empty, Cell.empty, Cell.empty, Cell.empty])

def lenCode (s : Slice) : Except Excno (Instr × Nat) :=
  match decodeCp0WithBits s with
  | .ok (i, _, r) => .ok (i, r.bitPos + 65536 * r.refPos)
  | .error e => .error e

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, tail, lo, hi] =>
      let tailBit := tail == "tail1"
      let lo := lo.toNat!; let hi := hi.toNat!
      let out ← IO.getStdout
      let mut buf : String := ""
      let mut k : Nat := 0
      for v in [lo:hi] do
        if mode == "len" then
          let n := match lenCode (mkSlice v tailBit) with | .ok (_, n) => n | .error _ => 0
          buf := buf ++ toString n ++ "\n"
        else if v % 256 == 0 then
          let line := match lenCode (mkSlice v tailBit) with
            | .ok (i, n) => s!"{v} {n} {i.pretty}"
            | .error _ => s!"{v} 0 INVALID"
          buf := buf ++ line ++ "\n"
        k := k + 1
        if k % 65536 == 0 then
          out.putStr buf; buf := ""
      out.putStr buf
      return 0
  | _ =>
      IO.eprintln "usage: tvm-lean-audit-decoder <len|name> <tail0|tail1> <lo> <hi>"
      return 2

import Tests.Harness.Registry

/-!
Slices advanced in their cell. A C++ `CellSlice` is a window into its cell (`bits_st`, `refs_st`):
the instructions that read a slice see what is left in the window. The cases of the suites give
their slices whole (the oracle passes a slice as the cell of its remaining part, `SB:`), so a model
that read the slice's cell instead of the window (`SDEPTH` read the depth of the whole cell, C++
`CellSlice::get_depth` that of the references left, crypto/vm/cells/CellSlice.cpp:803-809) agreed with
C++ on all of them.

`advance c` is the case `c` with the whole slices of ordinary cells on its stack (the three nearest
the top) replaced by slices of larger cells: some random bits before their bits and up to four
references (deeper ones first) before their references. The code first brings each such slice to the
top (`XCHG s0,s(j)`), reads the extra bits (`LDU k`, `NIP`) and references (`LDREF`, `NIP`) off it,
and puts it back: the case's instructions then run on a slice whose window is the original slice in
a cell with more before it, on the C++ side as on the model's. A variant whose code no longer fits
one cell is dropped. `casesOf` is this variant of every oracle case of a suite that has such a slice
(in `Tests.suiteOracleCases`); the fuzz runs the variant of every case it generates
(`Tests.runFuzzSpec`).
-/

namespace Tests.Gen.AdvancedSlices

open TvmLean

/-- A chain of `d` ordinary cells: depth `d`. -/
private def chain (d : Nat) : Cell :=
  (List.range d).foldl (fun c _ => Cell.mkOrdinary #[true] #[c]) Cell.empty

/-- The references put before a slice's own: deep ones first (depth 7, 5), then a leaf and depth 2. -/
private def extraRefPool : Array Cell := #[chain 7, chain 5, Cell.mkOrdinary (natToBits 0x2d 6) #[], chain 2]

/-- A whole slice of an ordinary cell with room for more bits or references. -/
private def eligible (s : Slice) : Bool :=
  s.bitPos == 0 && s.refPos == 0 && !s.cell.special && (s.cell.bits.size < 1023 || s.cell.refs.size < 4)

/-- The cell of `s` with `k` bits (`pat`) and `q` references (`extraRefPool`) before its own. -/
private def widen (s : Slice) (k q pat : Nat) : Cell :=
  Cell.mkOrdinary (natToBits pat k ++ s.cell.bits) (extraRefPool.extract 0 q ++ s.cell.refs)

/-- The code that reads `k` bits and `q` references off the slice `j` entries below the top. -/
private def prelude (j k q : Nat) : Array Instr :=
  let swap : Array Instr := if j = 0 then #[] else #[.xchg0 j]
  swap ++ (if k = 0 then #[] else #[.ldu k, .pop 1]) ++ (Array.replicate q #[Instr.ldref, .pop 1]).flatten ++ swap

/-- The case `c` on advanced slices (`none` if it has no whole slice to advance, or a code cell of
its own). -/
def advance (c : OracleCase) (rng0 : StdGen) : Option OracleCase × StdGen := Id.run do
  if c.codeCell?.isSome then
    return (none, rng0)
  -- the three slices nearest the top: the code before the case's stays short
  let chosen := ((List.range c.initStack.size).filter fun idx =>
    match c.initStack[idx]! with
    | .slice s => eligible s
    | _ => false).reverse.take 3
  if chosen.isEmpty then
    return (none, rng0)
  let mut rng := rng0
  let mut stack := c.initStack
  let mut pre : Array Instr := #[]
  for idx in chosen do
    match c.initStack[idx]! with
    | .slice s =>
        let maxK := Nat.min 64 (1023 - s.cell.bits.size)
        let maxQ := 4 - s.cell.refs.size
        let (k0, r1) := randNat rng 0 maxK
        let (q0, r2) := randNat r1 0 maxQ
        let (k, q) := if k0 = 0 ∧ q0 = 0 then (if 0 < maxK then (1, 0) else (0, 1)) else (k0, q0)
        let (pat, r3) := randNat r2 0 (2 ^ k - 1)
        rng := r3
        stack := stack.set! idx (.slice (Slice.ofCell (widen s k q pat)))
        pre := pre ++ prelude (c.initStack.size - 1 - idx) k q
    | _ => pure ()
  let program := pre ++ c.program
  -- the code must still be one cell the oracle can pass (`stdBocSerialize`)
  match assembleCp0 program.toList with
  | .ok code =>
      if code.bits.size ≤ 1023 ∧ code.refs.size ≤ 4 then
        return (some { c with name := s!"{c.name}/advanced", initStack := stack, program := program }, rng)
      else
        return (none, rng)
  | .error _ => return (none, rng)

/-- The advanced variant of every case of `oracle` that has a whole slice on its stack. -/
def casesOf (oracle : Array OracleCase) : Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  let mut rng := mkStdGen 20261030
  for c in oracle do
    let (v?, rng') := advance c rng
    rng := rng'
    if let some v := v? then
      out := out.push v
  return out

end Tests.Gen.AdvancedSlices

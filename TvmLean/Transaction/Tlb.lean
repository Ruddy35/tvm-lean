import TvmLean.Model

/-!
# TL-B readers and writers for the block structures of a transaction

The transaction code of C++ (`crypto/block/transaction.cpp`) reads accounts, messages and the
configuration through the generated TL-B code (`block/block-auto.cpp`: `tlb::unpack`,
`csr_unpack`, `fetch_to`); a failed read makes the whole operation fail. A `Reader` is such a read:
the rest of the slice, or `none` where the C++ read fails. Writers build the bits and references of
a cell in the order of the TL-B constructor.
-/

namespace TvmLean.Tx

/-- A TL-B read of a slice: the value and the rest, `none` if C++ `unpack` fails. -/
abbrev Reader := StateT Slice Option

namespace Reader

def fail : Reader α := fun _ => none

def bits (n : Nat) : Reader BitString := fun s =>
  if s.haveBits n then some (s.readBits n, s.advanceBits n) else none

def uint (n : Nat) : Reader Nat := do return bitsToNat (← bits n)

/-- A signed `n`-bit integer (two's complement). -/
def int (n : Nat) : Reader Int := do
  let v ← uint n
  return if n > 0 ∧ v ≥ 2 ^ (n - 1) then Int.ofNat v - 2 ^ n else Int.ofNat v

def bool : Reader Bool := do return (← bits 1)[0]!

def ref : Reader Cell := fun s =>
  if s.haveRefs 1 then some (s.cell.refs[s.refPos]!, { s with refPos := s.refPos + 1 }) else none

/-- `#< n`: an integer below `n` in the bits needed for `n - 1`. -/
def lessThan (n : Nat) : Reader Nat := do
  let v ← uint (n - 1).log2.succ
  if v < n then return v else fail

/-- `VarUInteger n`: `len:(#< n) value:(uint (len * 8))`. -/
def varUInt (n : Nat) : Reader Nat := do
  let len ← lessThan n
  uint (8 * len)

/-- `Grams = VarUInteger 16`. -/
def grams : Reader Nat := varUInt 16

/-- `Maybe X`. -/
def maybe (r : Reader α) : Reader (Option α) := do
  if ← bool then return some (← r) else return none

/-- `HashmapE n X` as its root: `hme_empty$0` or `hme_root$1 root:^(Hashmap n X)`. -/
def hashmapE : Reader (Option Cell) := maybe ref

/-- The current slice, nothing consumed. -/
def peek : Reader Slice := fun s => some (s, s)

/-- The slice that is left, all of it consumed. -/
def rest : Reader Slice := fun s => some (s, { s with bitPos := s.cell.bits.size, refPos := s.cell.refs.size })

/-- Whether nothing is left (`tlb::unpack_exact`). -/
def atEnd : Reader Bool := fun s => some (s.bitsRemaining == 0 && s.refsRemaining == 0, s)

/-- Run on the whole cell, requiring that all of it is read. -/
def runExact (r : Reader α) (c : Cell) : Option α :=
  match r (Slice.ofCell c) with
  | some (v, s) => if s.bitsRemaining == 0 && s.refsRemaining == 0 then some v else none
  | none => none

def run (r : Reader α) (c : Cell) : Option α := (r (Slice.ofCell c)).map (·.1)

end Reader

/-- A cell being written: bits and references in order. -/
structure W where
  bits : BitString := #[]
  refs : Array Cell := #[]

namespace W

def uint (w : W) (v n : Nat) : W := { w with bits := w.bits ++ natToBits v n }

def int (w : W) (v : Int) (n : Nat) : W := w.uint (if v < 0 then (2 ^ n - v.natAbs) % 2 ^ n else v.toNat) n

def bool (w : W) (b : Bool) : W := { w with bits := w.bits.push b }

def bitStr (w : W) (bs : BitString) : W := { w with bits := w.bits ++ bs }

def ref (w : W) (c : Cell) : W := { w with refs := w.refs.push c }

/-- The bits and references left in a slice. -/
def slice (w : W) (s : Slice) : W :=
  { bits := w.bits ++ s.readBits s.bitsRemaining, refs := w.refs ++ s.cell.refs.extract s.refPos s.cell.refs.size }

def varUInt (w : W) (v n : Nat) : W :=
  let len := if v = 0 then 0 else (v.log2 + 8) / 8
  (w.uint len (n - 1).log2.succ).uint v (8 * len)

def grams (w : W) (v : Nat) : W := w.varUInt v 16

def maybeRef (w : W) (c : Option Cell) : W :=
  match c with
  | some c => (w.bool true).ref c
  | none => w.bool false

def cell (w : W) : Cell := Cell.mkOrdinary w.bits w.refs

end W

/-- `CurrencyCollection`: grams and the dictionary of other currencies (`ExtraCurrencyCollection`,
`HashmapE 32 (VarUInteger 32)`, kept as its root). -/
structure Currencies where
  grams : Nat
  extra : Option Cell := none
  /-- the grams have no leading zero byte (`block::tlb::VarUInteger` reads only these) -/
  gramsCanonical : Bool := true
  deriving Inhabited

def Reader.currencies : Reader Currencies := do
  let s ← Reader.peek
  let grams ← Reader.grams
  let len := if s.haveBits 4 then bitsToNat (s.readBits 4) else 0
  return { grams, extra := ← Reader.hashmapE, gramsCanonical := len == 0 || grams >>> (8 * len - 8) != 0 }

def W.currencies (w : W) (c : Currencies) : W := (w.grams c.grams).maybeRef c.extra

end TvmLean.Tx

import TvmLean.Model.Cell.Cell

namespace TvmLean

structure Builder where
  bits : BitString
  refs : Array Cell
  deriving Repr

def Builder.empty : Builder :=
  { bits := #[], refs := #[] }

def Builder.canExtendBy (b : Builder) (bits : Nat) (refs : Nat := 0) : Bool :=
  decide (b.bits.size + bits ≤ 1023 ∧ b.refs.size + refs ≤ 4)

def Builder.storeBits (b : Builder) (bs : BitString) : Builder :=
  { b with bits := b.bits ++ bs }

def Builder.finalize (b : Builder) : Cell :=
  Cell.mkOrdinary b.bits b.refs

/-- C++ `CellBuilder::finalize{,_copy,_novm}` of an ordinary cell: `DataCell::create` rejects a
cell deeper than `Cell.maxDepth` (`CellWriteError`, cell_ov in `VmState::run_inner`). -/
def Builder.finalizeChecked (b : Builder) : Except Excno Cell :=
  if Cell.refsDepthOk b.refs then .ok b.finalize else .error .cellOv

def Builder.finalizeCopy (b : Builder) (special : Bool := false) : Except Excno Cell := do
  if !special then
    return (← b.finalizeChecked)

  -- We emulate C++ `vm::DataCell::create(..., is_special=true)` validation by
  -- searching for the unique level mask that makes the exotic cell well-formed.
  -- If none work, TON throws `cell_ov`.
  for m in [0:8] do
    let c : Cell :=
      { bits := b.bits
      , refs := b.refs
      , special := true
      , levelMask := m
      }
    match Cell.computeLevelInfo? c with
    | .ok info =>
        -- `DataCell::create` also rejects a depth above `Cell.maxDepth` at any level
        if info.depths.all (· ≤ Cell.maxDepth) then return c else throw .cellOv
    | .error _ => continue
  throw .cellOv

instance : BEq Builder := ⟨fun a b => a.bits == b.bits && a.refs == b.refs⟩

end TvmLean

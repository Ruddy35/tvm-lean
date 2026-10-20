import TvmLean.Semantics.Exec.Common

namespace TvmLean

open Std

structure DataSizeAcc where
  visited : HashSet ByteArray
  cells : Nat
  bits : Nat
  refs : Nat

def DataSizeAcc.empty : DataSizeAcc :=
  { visited := {}
    cells := 0
    bits := 0
    refs := 0 }

def DataSizeAcc.visitCell (limit : Nat) (c : Cell) (acc : DataSizeAcc) : Except Excno DataSizeAcc := do
  let h : ByteArray := ByteArray.mk (Cell.hashBytes c)
  if acc.visited.contains h then
    return acc
  if acc.cells ≥ limit then
    throw .cellOv
  let acc :=
    { visited := acc.visited.insert h
      cells := acc.cells + 1
      bits := acc.bits + c.bits.size
      refs := acc.refs + c.refs.size }
  let mut acc := acc
  for hr : r in c.refs do
    acc ← DataSizeAcc.visitCell limit r acc
  return acc
termination_by sizeOf c
decreasing_by
  all_goals
    have h1 := Array.sizeOf_lt_of_mem hr
    cases c
    simp_all
    omega

def VM.visitDataSizeCell (limit : Nat) (c : Cell) (acc : DataSizeAcc) : VM DataSizeAcc := do
  let h : ByteArray := ByteArray.mk (Cell.hashBytes c)
  if acc.visited.contains h then
    return acc
  if acc.cells ≥ limit then
    throw .cellOv
  -- Match C++ `VmStorageStat::add_storage`: loading a newly visited cell charges cell-load gas. It
  -- is `load_cell_slice_special` (boc.cpp:1257): a library cell stays as it is, no library is loaded.
  VM.registerCellLoadSpecial c
  let acc :=
    { visited := acc.visited.insert h
      cells := acc.cells + 1
      bits := acc.bits + c.bits.size
      refs := acc.refs + c.refs.size }
  let mut acc := acc
  for hr : r in c.refs do
    acc ← VM.visitDataSizeCell limit r acc
  return acc
termination_by sizeOf c
decreasing_by
  all_goals
    have h1 := Array.sizeOf_lt_of_mem hr
    cases c
    simp_all
    omega

def VM.execCdataSize (quiet : Bool) : VM Unit := do
  VM.checkUnderflow 2
  -- C++ `exec_compute_data_size`: `pop_int` (NaN allowed), the cell or slice, then range_chk for
  -- a bound that is NaN or negative
  let bound ← VM.popInt
  let c? ← VM.popMaybeCell
  let n : Int ←
    match bound with
    | .nan => throw .rangeChk
    | .num n => if n < 0 then throw .rangeChk else pure n
  let maxBoundNat : Nat := (1 <<< 63) - 1
  let maxBound : Int := Int.ofNat maxBoundNat
  let limit : Nat := if n > maxBound then maxBoundNat else n.toNat
  match c? with
  | none =>
      VM.pushSmallInt 0
      VM.pushSmallInt 0
      VM.pushSmallInt 0
      if quiet then
        VM.pushSmallInt (-1)
  | some c =>
      try
        let acc ← VM.visitDataSizeCell limit c DataSizeAcc.empty
        VM.pushSmallInt (Int.ofNat acc.cells)
        VM.pushSmallInt (Int.ofNat acc.bits)
        VM.pushSmallInt (Int.ofNat acc.refs)
        if quiet then
          VM.pushSmallInt (-1)
      catch
      | .cellOv =>
          if quiet then
            VM.pushSmallInt 0
          else
            throw .cellOv
      | e =>
          throw e

def VM.execSdataSize (quiet : Bool) : VM Unit := do
  VM.checkUnderflow 2
  -- C++ `exec_compute_data_size`: `pop_int` (NaN allowed), the cell or slice, then range_chk for
  -- a bound that is NaN or negative
  let bound ← VM.popInt
  let s ← VM.popSlice
  let n : Int ←
    match bound with
    | .nan => throw .rangeChk
    | .num n => if n < 0 then throw .rangeChk else pure n
  let maxBoundNat : Nat := (1 <<< 63) - 1
  let maxBound : Int := Int.ofNat maxBoundNat
  let limit : Nat := if n > maxBound then maxBoundNat else n.toNat
  let mut acc : DataSizeAcc :=
    { DataSizeAcc.empty with bits := s.bitsRemaining, refs := s.refsRemaining }
  let mut ok : Bool := true
  for i in [s.refPos:s.cell.refs.size] do
    let c := s.cell.refs[i]!
    try
      let acc' ← VM.visitDataSizeCell limit c acc
      acc := acc'
    catch
    | .cellOv =>
        ok := false
        break
    | e =>
        throw e

  if ok then
    VM.pushSmallInt (Int.ofNat acc.cells)
    VM.pushSmallInt (Int.ofNat acc.bits)
    VM.pushSmallInt (Int.ofNat acc.refs)
    if quiet then
      VM.pushSmallInt (-1)
  else
    if quiet then
      VM.pushSmallInt 0
    else
      throw .cellOv

set_option maxHeartbeats 1000000 in
def execInstrMisc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellExt (.cdataSize quiet) => VM.execCdataSize quiet
  | .cellExt (.sdataSize quiet) => VM.execSdataSize quiet
  | _ => next

end TvmLean

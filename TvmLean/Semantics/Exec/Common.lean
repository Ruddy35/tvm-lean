import TvmLean.Model
import TvmLean.Semantics.VM.Ops.Stack
import TvmLean.Semantics.VM.Ops.Cells
import TvmLean.Semantics.VM.Ops.Gas
import TvmLean.Semantics.VM.Ops.Cont
import TvmLean.Semantics.VM.Ops.State

namespace TvmLean

def VM.checkUnderflow (n : Nat) : VM Unit := do
  let st ← get
  if st.stack.size < n then
    throw .stkUnd

/-- The count of the stack operations that take it from the stack (`PICK`, `ROLL`, `ROLLREV`,
`BLKSWX`, `REVX`, `DROPX`, `XCHGX`, `CHKDEPTH`, `ONLYTOPX`, `ONLYX`): C++ `pop_smallint_range` up to
`2^30 - 1` from version 4, up to 255 before (stackops.cpp:404-530). -/
def VM.popStackCount : VM Nat := do
  VM.popNatUpTo (if (← get).globalVersion ≥ 4 then (1 <<< 30) - 1 else 255)

/-- The cell loader of C++ `load_cell_slice_impl` (cells/CellSlice.cpp) in this VM: a library cell
is replaced by the root of its library from `VmState.libraries`, any other exotic cell is cell_und.
Passed as `resolve` to the dictionary functions, which load every node this way. -/
def VM.cellResolver : VM (Cell → Except Excno Cell) := do
  return libraryResolver (← get).libraries

/-- C++ `load_cell_slice` / `load_cell_slice_ref`: the load of `c` is charged (a library cell's,
not its root's), then `c` is resolved as by `VM.cellResolver`. -/
def VM.loadCellSlice (c : Cell) : VM Slice := do
  VM.registerCellLoad c
  match libraryResolver (← get).libraries c with
  | .ok r => return Slice.ofCell r
  | .error e => throw e

/-- C++ `DataCell::create` (cells/DataCell.cpp:78) of a new ordinary cell with references `refs`,
its creation already charged: cell_ov if it would be deeper than `Cell.maxDepth` (`CellBuilder::
finalize` throws `CellWriteError`, `VmState::run_inner` turns it into cell_ov). -/
def VM.checkNewCellDepth (refs : Array Cell) : VM Unit := do
  if !Cell.refsDepthOk refs then
    throw .cellOv

/-- Gas for the `created` cells of a dictionary set operation (C++ `dict_set`, `dict_lookup_set`,
`pfx_dict_set`, dict.cpp) whose new root is `newRoot?`; `path` gives the nodes on the key's path in
it, root first (`dictKeyPath`, `pfxDictKeyPath`). C++ creates the cells bottom-up — the leaf of the
key, the lower part of a split edge (when `created` exceeds the path by one), then the forks of the
path up to the root — each charged before `DataCell::create`, which fails at the first one deeper
than `Cell.maxDepth` (cell_ov). Depth grows towards the root, so the root decides whether one fails;
the cells up to the lowest failing one are then charged. -/
def VM.chargeDictSetCreates (newRoot? : Option Cell) (created : Nat) (path : Cell → Array Cell) : VM Unit := do
  if created == 0 then
    return
  match newRoot? with
  | some root =>
      if !Cell.refsDepthOk root.refs then
        let nodes := path root
        let split : Nat := created - nodes.size
        -- the lowest node over the limit, counted from the leaf
        let up : Nat := (nodes.reverse.findIdx? (fun c => !Cell.refsDepthOk c.refs)).getD 0
        VM.chargeCellCreates (if up == 0 then 1 else up + split + 1)
        throw .cellOv
  | none => pure ()
  VM.chargeCellCreates created

/-- C++ `VmState::throw_exception` called by an instruction: `raise` makes the exception stack and
continuation, then the exception gas is charged (out of gas at once) and the jump to `c2` fails with
stk_und if `c2` expects more arguments than the stack holds (`adjust_jump_cont`). -/
def VM.throwToHandler (raise : VmState → VmState) : VM Unit := do
  modify raise
  VM.consumeGas exceptionGasPrice
  if (← get).excHandlerNeedsMoreArgs then
    throw .stkUnd

/--
Marks an instruction path as not yet implemented.

The VM core still uses `Excno` as the execution error channel, so this bridges the
structured `VmError.unimplemented` marker to `Excno.unimplemented`.
-/
def VM.unimplementedInstr (id : InstrId) (msg : String := "not yet implemented") : VM α := do
  let _ : VmError := .unimplemented id msg
  throw .unimplemented

def VM.execNullSwapIf (cond : Bool) (depth : Nat) (count : Nat) : VM Unit := do
  -- Matches C++ `exec_null_swap_if` / `exec_null_swap_if_many` (tupleops.cpp).
  let st ← get
  if depth + 1 > st.stack.size then
    throw .stkUnd
  let x ← VM.popIntFinite
  let trigger : Bool := if cond then x != 0 else x == 0
  if trigger then
    for _ in [0:count] do
      VM.push .null
    for i in [0:depth] do
      VM.swap i (i + count)
  VM.push (.int (.num x))

def VM.getUnpackedConfigTuple : VM (Array Value) := do
  -- Mirrors C++ `get_unpacked_config_tuple(st)` (tonops.cpp):
  --   t1 := tuple_index(c7, 0); t2 := tuple_index(t1, 14); return t2
  match (← get).regs.c7[0]? with
  | none => throw .rangeChk
  | some (Value.tuple params) =>
      match params[14]? with
      | none => throw .rangeChk
      | some (Value.tuple unpacked) => return unpacked
      | some _ => throw .typeChk
  | some _ =>
      throw .typeChk

/-- C++ `Config::do_get_msg_prices` (mc-config.cpp, `tlb::unpack`: trailing data allowed), cell_und
when it does not parse: (lump_price, bit_price, cell_price, ihr_factor, first_frac). -/
def parseMsgPrices (pricesCs : Slice) : Except Excno (Int × Int × Int × Nat × Nat) := do
  let (tag, s1) ← pricesCs.takeBitsAsNatCellUnd 8
  if tag != 0xea then
    throw .cellUnd
  let (lumpPrice, s2) ← s1.takeBitsAsNatCellUnd 64
  let (bitPrice, s3) ← s2.takeBitsAsNatCellUnd 64
  let (cellPrice, s4) ← s3.takeBitsAsNatCellUnd 64
  let (ihrFactor, s5) ← s4.takeBitsAsNatCellUnd 32 -- ihr_price_factor
  let (firstFrac, s6) ← s5.takeBitsAsNatCellUnd 16
  let (_, _) ← s6.takeBitsAsNatCellUnd 16 -- next_frac
  return (Int.ofNat lumpPrice, Int.ofNat bitPrice, Int.ofNat cellPrice, ihrFactor, firstFrac)

def VM.getMsgPrices (isMasterchain : Bool) : VM (Int × Int × Int × Nat × Nat) := do
  -- Mirrors `util::get_msg_prices(get_unpacked_config_tuple(st), is_masterchain)`.
  -- Returns (lump_price, bit_price, cell_price, ihr_factor, first_frac).
  let unpacked ← VM.getUnpackedConfigTuple
  let idx : Nat := if isMasterchain then 4 else 5
  match unpacked[idx]? with
  | some (.slice pricesCs) =>
      match parseMsgPrices pricesCs with
      | .ok p => return p
      | .error e => throw e
  | some .null => throw .typeChk
  | some _ => throw .typeChk
  | none => throw .rangeChk

def VM.getGasPrices (isMasterchain : Bool) : VM (Nat × Nat × Nat) := do
  -- Mirrors `util::get_gas_prices(get_unpacked_config_tuple(st), is_masterchain)`.
  -- Returns (gas_price, flat_gas_limit, flat_gas_price).
  let unpacked ← VM.getUnpackedConfigTuple
  let idx : Nat := if isMasterchain then 2 else 3

  let parseTail (tag : Nat) (s : Slice) : Except Excno Nat := do
    if tag == 0xdd then
      let (gasPrice, s2) ← s.takeBitsAsNatCellUnd 64
      let (_, s3) ← s2.takeBitsAsNatCellUnd 64 -- gas_limit
      let (_, s4) ← s3.takeBitsAsNatCellUnd 64 -- gas_credit
      let (_, s5) ← s4.takeBitsAsNatCellUnd 64 -- block_gas_limit
      let (_, s6) ← s5.takeBitsAsNatCellUnd 64 -- freeze_due_limit
      let (_, _) ← s6.takeBitsAsNatCellUnd 64 -- delete_due_limit
      return gasPrice
    else if tag == 0xde then
      let (gasPrice, s2) ← s.takeBitsAsNatCellUnd 64
      let (_, s3) ← s2.takeBitsAsNatCellUnd 64 -- gas_limit
      let (_, s4) ← s3.takeBitsAsNatCellUnd 64 -- special_gas_limit
      let (_, s5) ← s4.takeBitsAsNatCellUnd 64 -- gas_credit
      let (_, s6) ← s5.takeBitsAsNatCellUnd 64 -- block_gas_limit
      let (_, s7) ← s6.takeBitsAsNatCellUnd 64 -- freeze_due_limit
      let (_, _) ← s7.takeBitsAsNatCellUnd 64 -- delete_due_limit
      return gasPrice
    else
      throw .cellUnd

  let parseGasLimitsPrices (cs : Slice) : Except Excno (Nat × Nat × Nat) := do
    let (tag0, s1) ← cs.takeBitsAsNatCellUnd 8
    if tag0 == 0xd1 then
      let (flatLimit, s2) ← s1.takeBitsAsNatCellUnd 64
      let (flatPrice, s3) ← s2.takeBitsAsNatCellUnd 64
      let (tag1, s4) ← s3.takeBitsAsNatCellUnd 8
      let gasPrice ← parseTail tag1 s4
      return (gasPrice, flatLimit, flatPrice)
    else
      let gasPrice ← parseTail tag0 s1
      return (gasPrice, 0, 0)

  match unpacked[idx]? with
  | some (.slice pricesCs) =>
      match (parseGasLimitsPrices pricesCs : Except Excno (Nat × Nat × Nat)) with
      | .ok (gasPrice, flatGasLimit, flatGasPrice) => return (gasPrice, flatGasLimit, flatGasPrice)
      | .error e => throw e
  | some .null => throw .typeChk
  | some _ => throw .typeChk
  | none => throw .rangeChk

def VM.extractCc (saveCr : Nat) (stackCopy : Int := -1) (ccArgs : Int := -1) : VM Continuation := do
  -- Mirrors C++ `VmState::extract_cc(save_cr, stack_copy, cc_args)`.
  let st ← get
  let codeAfter : Slice ←
    match st.cc with
    | .ordinary code _ _ _ => pure code
    | _ => throw .typeChk

  let depth : Nat := st.stack.size
  let mut bottom : Stack := #[]
  let mut newStack : Stack := st.stack
  let mut chargeSplitGas : Bool := false

  if decide (stackCopy < 0) then
    -- Keep the whole stack, capture nothing.
    bottom := #[]
    newStack := st.stack
  else
    let copy : Nat := stackCopy.toNat
    if copy > depth then
      throw .stkUnd
    if copy = depth then
      bottom := #[]
      newStack := st.stack
    else if copy = 0 then
      bottom := st.stack
      newStack := #[]
    else
      let split : Nat := depth - copy
      bottom := st.stack.take split
      newStack := st.stack.extract split depth
      chargeSplitGas := true

  -- Update stack and charge stack gas only when we actually split off a non-empty `newStack` via `copy > 0`.
  -- C++ charges only for the strict split path (`0 < copy < depth`).
  let st :=
    if chargeSplitGas then
      ({ st with stack := newStack }).consumeStackGas newStack.size
    else
      { st with stack := newStack }

  let mut ccCregs : OrdCregs := OrdCregs.empty
  let mut regs := st.regs
  if (saveCr &&& 1) = 1 then
    ccCregs := { ccCregs with c0 := some regs.c0 }
    regs := { regs with c0 := .quit 0 }
  if (saveCr &&& 2) = 2 then
    ccCregs := { ccCregs with c1 := some regs.c1 }
    regs := { regs with c1 := .quit 1 }
  if (saveCr &&& 4) = 4 then
    ccCregs := { ccCregs with c2 := some regs.c2 }

  set { st with regs := regs }

  let ccCdata : OrdCdata := { stack := bottom, nargs := ccArgs }
  return .ordinary codeAfter (.quit 0) ccCregs ccCdata

def VM.pushCode : VM Unit := do
  -- Mirrors C++ `VmState::push_code()`: push current remaining code slice.
  let st ← get
  match st.cc with
  | .ordinary code _ _ _ =>
      VM.push (.slice code)
  | _ =>
      throw .typeChk

end TvmLean

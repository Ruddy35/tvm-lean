import TvmLean.Model
import TvmLean.Semantics.VM.Monad

namespace TvmLean

def VmState.consumeGas (st : VmState) (amount : Int) : VmState :=
  { st with gas := st.gas.consume amount }

/-- Gas ran out and C++ `VmState::consume_gas` throws at once: from version 4 it is `consume_chk`;
before, it only subtracts, and the `gas.check()` that ends the step finds it (vm.h:203-209,
vm.cpp:485). -/
def VmState.gasExhaustedNow (st : VmState) : Bool :=
  st.globalVersion ≥ 4 && decide (st.gas.gasRemaining < 0)

/-- C++ `VmState::register_chksgn_call` (vm.h:434-443): from version 4 the first `chksgn_free_count`
checks are free, their price counted as free gas (`consume_free_gas`); before, checks are not
counted or charged. -/
def VmState.registerChkSgnCall (st : VmState) : VmState :=
  if st.globalVersion < 4 then st else
  let cnt := st.chksgnCounter + 1
  let st' := { st with chksgnCounter := cnt }
  if cnt > chksgnFreeCount then
    st'.consumeGas chksgnGasPrice
  else
    { st' with freeGasConsumed := st'.freeGasConsumed + chksgnGasPrice }

def VmState.consumeTupleGas (st : VmState) (tupleLen : Nat) : VmState :=
  st.consumeGas (Int.ofNat tupleLen * tupleEntryGasPrice)

def VmState.consumeStackGas (st : VmState) (stackDepth : Nat) : VmState :=
  let extra : Nat := if stackDepth > freeStackDepth then stackDepth - freeStackDepth else 0
  st.consumeGas (Int.ofNat extra * stackEntryGasPrice)

def VmState.registerCellLoad (st : VmState) (c : Cell) : VmState :=
  let h : Array UInt8 := Cell.hashBytes c
  let seen : Bool := st.loadedCells.any (fun x => x == h)
  let st' : VmState :=
    if seen then
      st
    else
      { st with loadedCells := st.loadedCells.push h }
  st'.consumeGas (if seen then cellReloadGasPrice else cellLoadGasPrice)

/-- VM-monad cell load: registers the cell and consumes gas. This mirrors C++
`load_cell_slice_impl` → `register_cell_load` → `consume_gas`, which from version 4 throws
`VmNoGas` at once on gas exhaustion, aborting the instruction (`VmState.gasExhaustedNow`). -/
def VM.registerCellLoad (c : Cell) : VM Unit := do
  modify fun st => st.registerCellLoad c
  if (← get).gasExhaustedNow then
    throw .outOfGas

/-- C++ `VmState::consume_gas`: out of gas at once from version 4 (`VmState.gasExhaustedNow`). -/
def VM.consumeGas (amount : Int) : VM Unit := do
  modify fun st => st.consumeGas amount
  if (← get).gasExhaustedNow then
    throw .outOfGas

/-- Charges `n` cell creations one at a time, checking the limit after each: in C++ every
`CellBuilder::finalize` calls `register_cell_create` (`consume_gas`), which throws as soon as the
limit is exceeded, so when gas runs out inside an instruction only the creations up to the first
overrun are counted. -/
def VM.chargeCellCreates (n : Nat) : VM Unit := do
  for _ in [0:n] do
    VM.consumeGas cellCreateGasPrice

end TvmLean

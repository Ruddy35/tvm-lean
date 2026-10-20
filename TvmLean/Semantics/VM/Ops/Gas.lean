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

/-- C++ `VmState::load_library` (vm.cpp:644-656) before its lookup: with `max_library_loads` set,
once that many libraries are loaded a library not among them is refused (it reads as missing, vm.cpp:
647-652); while fewer are, the library is recorded as loaded (vm.cpp:654), also if its lookup then
fails. Returns whether it is refused. -/
def VmState.admitLibrary (st : VmState) (hash : BitString) : VmState × Bool :=
  match st.maxLibraryLoads with
  | none => (st, false)
  | some m =>
      if m == st.loadedLibraries.size then
        (st, !st.loadedLibraries.contains hash)
      else if st.loadedLibraries.contains hash then
        (st, false)
      else
        ({ st with loadedLibraries := st.loadedLibraries.push hash }, false)

/-- The call of `load_library` for `hash` made by loading a cell whose library the resolver of the
step (`libraryResolveLoads` with `librariesRefused`) followed unless it refused it: the libraries are
admitted as C++ admits them (`VmState.admitLibrary`), and a refusal the resolver did not make is
recorded in `librariesMissed`, for the step to be run again (`VmState.stepWith`). -/
def VmState.registerLibraryLoad (st : VmState) (hash : BitString) : VmState :=
  let (st, refused) := st.admitLibrary hash
  if refused && !st.librariesRefused.contains hash then
    { st with librariesMissed := st.librariesMissed.push hash }
  else
    st

/-- What C++ does after charging the load of `c` when it loads `c` as a cell slice
(`load_cell_slice_impl`): the loads of following a library and the calls of `load_library`
(`libraryResolveLoads` with the libraries the step refuses); from version 5 only the call, nothing
for an ordinary cell. -/
def VmState.libraryLoads (st : VmState) (c : Cell) : Array LibraryLoadStep :=
  if c.special then (libraryResolveLoads st.libraries st.globalVersion c st.librariesRefused).1 else #[]

/-- Makes `steps` in order: charges each load (`register_cell_load`), registers each call of
`load_library` (`VmState.registerLibraryLoad`); from version 4 the first load that exhausts gas
throws and the rest are not made: `true` then. -/
def VmState.registerCellLoads (st : VmState) : List LibraryLoadStep → VmState × Bool
  | [] => (st, false)
  | .cell c :: rest =>
      let st := st.registerCellLoad c
      if st.gasExhaustedNow then (st, true) else st.registerCellLoads rest
  | .library hash :: rest => (st.registerLibraryLoad hash).registerCellLoads rest

/-- VM-monad load of `c` as C++ `load_cell_slice` loads it (`load_cell_slice_impl`): `c` is
charged (`register_cell_load` → `consume_gas`, which from version 4 throws `VmNoGas` at once,
aborting the instruction: `VmState.gasExhaustedNow`), then what following a library does
(`VmState.libraryLoads`). -/
def VM.registerCellLoad (c : Cell) : VM Unit := do
  let st ← get
  let (st', exhausted) := st.registerCellLoads (.cell c :: (st.libraryLoads c).toList)
  set st'
  if exhausted then
    throw .outOfGas

/-- VM-monad load of `c` that may stay exotic (C++ `load_cell_slice_special`,
`load_cell_slice_ref_special`): no library is followed, only `c` is charged. -/
def VM.registerCellLoadSpecial (c : Cell) : VM Unit := do
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

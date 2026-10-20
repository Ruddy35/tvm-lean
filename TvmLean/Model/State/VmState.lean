import TvmLean.Model.State.Registers

namespace TvmLean

structure VmState where
  stack : Stack
  regs : Regs
  cc : Continuation
  cp : Int
  gas : GasLimits
  chksgnCounter : Nat
  loadedCells : Array (Array UInt8)
  -- Library collections used by XLOAD (see TON `VmState::load_library`).
  -- Each entry is a dictionary root cell mapping 256-bit hashes to ^Cell values.
  libraries : Array Cell
  callStack : Array CallFrame
  cstate : CommittedState
  maxDataDepth : Nat
  /-- Network global version (config param 8), as in C++ `VmState::global_version`.
  Instruction semantics differ between versions (e.g. quiet shifts, NaN handling in v13/v14).
  The model implements versions 13 and later; the default 13 is the behaviour the model had
  before versioning was introduced. -/
  globalVersion : Nat := 13
  /-- C++ `VmState::free_gas_consumed`: gas of free signature checks and of the part of cheap
  GETEXTRABALANCE calls above their cap; charged by `RUNVM` with isolated gas. -/
  freeGasConsumed : Int := 0
  /-- C++ `VmState::get_extra_balance_counter`. -/
  getExtraBalanceCounter : Nat := 0
  /-- C++ `VmState::jump_to`'s `cnt`: the jumps made by the current chain of continuations. A chain
  starts with a jump (an instruction, an implicit `RET` or `JMPREF`, an exception) and ends when an
  ordinary continuation is entered or the VM halts; the model makes one step per continuation. -/
  chainJumps : Nat := 0
  /-- C++ `VmState::steps` (the `vm_steps` of a transaction): one per step that runs an instruction,
  an implicit `RET` or `JMPREF` (`VmState::step`), one per exception handled and one for an out of gas
  that ends the VM (`run_inner`, `run`), and the steps of a `RUNVM` child (`restore_parent_vm`). -/
  steps : Nat := 0
  deriving Repr

def VmState.initial (code : Cell) (gasLimit : Int := 1_000_000) (gasMax : Int := GasLimits.infty)
    (gasCredit : Int := 0) : VmState :=
  { stack := #[]
    regs := Regs.initial
    cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty
    cp := 0
    gas := GasLimits.ofLimits gasLimit gasMax gasCredit
    chksgnCounter := 0
    loadedCells := #[]
    libraries := #[]
    callStack := #[]
    cstate := CommittedState.empty
    maxDataDepth := 512 }

end TvmLean

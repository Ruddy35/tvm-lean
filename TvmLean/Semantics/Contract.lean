import TvmLean.Semantics

/-!
# Compute phase of a contract: formal entry point and outcome

These definitions describe what a validator does around the TVM in the compute phase:
how the initial VM state is built from an inbound message, and which state persists after
the run. They are the objects contract theorems are stated about:

* base case:   `Inv data₀`
* step:        `Inv data → (computePhase fuel (computePhaseInit …data…) data).c4 satisfies Inv`

The model of the transaction builds the VM of its compute phase with `computePhaseStack` and
`computePhaseInit` and reads its result with `ComputeOutcome.ofHalt` (`Tx.runVm`,
`Tx.computePhaseRun` in `TvmLean/Transaction/Run.lean`), so these exact definitions are checked
against the TON transaction emulator on every transaction case; the differential-test runner
(`Validation/Diff/Runner.lean`) uses them too, on every fixture.

The run depends on nothing but the VM state: the cryptography (signatures, hashes, elliptic
curves) is defined in Lean (`TvmLean/Model/Crypto`), so theorems about it make no assumption
about external code.
-/

namespace TvmLean

/-- Initial stack of `recv_internal` / `recv_external`
(C++ `Transaction::prepare_vm_stack`): balance, message value, full message cell,
message body slice, and the selector (`0` internal, `-1` external). -/
def computePhaseStack (balance msgValue : Int) (inMsg : Cell) (body : Slice) (isExternal : Bool) : Stack :=
  #[.int (.num balance), .int (.num msgValue), .cell inMsg, .slice body,
    .int (.num (if isExternal then -1 else 0))]

/-- Initial VM state of the compute phase. As in C++ (`flags = 1`, same_c3), `c3` is the
root continuation of the code, so `CALLDICT`/`JMPDICT` re-enter the dispatcher. -/
def computePhaseInit (code data : Cell) (stack : Stack) (c7 : Array Value)
    (gasLimit gasMax gasCredit : Int) (globalVersion : Nat) : VmState :=
  let base0 := VmState.initial code gasLimit gasMax gasCredit
  let base : VmState := { base0 with regs := { base0.regs with c3 := base0.cc } }
  { base with stack := stack, regs := { base.regs with c4 := data, c7 := c7 },
              globalVersion := globalVersion }

/-- Network global version from the config dictionary: param 8,
`capabilities#c4 version:uint32 capabilities:uint64`. -/
def globalVersionOfConfig? (configRoot : Cell) : Option Nat :=
  match dictLookup (some configRoot) (natToBits 8 32) with
  | .ok (some s) =>
      if s.haveBits 40 && bitsToNat (s.readBits 8) == 0xc4 then
        some (bitsToNat ((s.advanceBits 8).readBits 32))
      else none
  | _ => none

/-- What persists after the compute phase. -/
structure ComputeOutcome where
  /-- Exit code as reported by the blockchain (`compute_exit_code`). -/
  exitCode : Int
  /-- New persistent data. -/
  c4 : Cell
  /-- Action list handed to the action phase. -/
  c5 : Cell
  /-- Gas used, at most the gas limit (`cp.gas_used`, transaction.cpp:2016). -/
  gasUsed : Int

/-- The commit rule of TON C++: only a committed state (explicit `COMMIT` or successful
termination) persists; otherwise the data is rolled back and the action list is empty. -/
def ComputeOutcome.ofHalt (exitCode : Int) (stF : VmState) (data0 : Cell) : ComputeOutcome :=
  let ok : Bool := (stF.gas.gasCredit == 0) && stF.cstate.committed
  { exitCode := ~~~ exitCode
    c4 := if ok then stF.cstate.c4 else data0
    c5 := if ok then stF.cstate.c5 else Cell.empty
    gasUsed := min stF.gas.gasConsumed stF.gas.gasLimit }

/-- Run the compute phase with at most `fuel` steps (`none` if the fuel is exhausted). -/
def computePhase (fuel : Nat) (st0 : VmState) (data0 : Cell) : Option ComputeOutcome :=
  match VmState.run fuel st0 with
  | .halt ec stF => some (ComputeOutcome.ofHalt ec stF data0)
  | .continue _ => none

/-! ## Basic facts -/

@[simp] theorem computePhaseInit_c4 (code data : Cell) (stack : Stack) (c7 : Array Value)
    (gl gm gc : Int) (gv : Nat) : (computePhaseInit code data stack c7 gl gm gc gv).regs.c4 = data := rfl

@[simp] theorem computePhaseInit_c7 (code data : Cell) (stack : Stack) (c7 : Array Value)
    (gl gm gc : Int) (gv : Nat) : (computePhaseInit code data stack c7 gl gm gc gv).regs.c7 = c7 := rfl

@[simp] theorem computePhaseInit_stack (code data : Cell) (stack : Stack) (c7 : Array Value)
    (gl gm gc : Int) (gv : Nat) : (computePhaseInit code data stack c7 gl gm gc gv).stack = stack := rfl

@[simp] theorem computePhaseInit_globalVersion (code data : Cell) (stack : Stack) (c7 : Array Value)
    (gl gm gc : Int) (gv : Nat) : (computePhaseInit code data stack c7 gl gm gc gv).globalVersion = gv := rfl

@[simp] theorem computePhaseStack_size (b v : Int) (m : Cell) (s : Slice) (e : Bool) :
    (computePhaseStack b v m s e).size = 5 := rfl

/-- **Rollback.** If the run did not commit, the persistent data is exactly the old data and
no actions are emitted — whatever the code did before failing. This is the fact that makes
"a failing transaction cannot break the invariant" trivial in every induction step. -/
theorem ComputeOutcome.ofHalt_rollback (ec : Int) (stF : VmState) (data0 : Cell)
    (h : stF.cstate.committed = false) :
    (ComputeOutcome.ofHalt ec stF data0).c4 = data0 ∧
      (ComputeOutcome.ofHalt ec stF data0).c5 = Cell.empty := by
  simp [ComputeOutcome.ofHalt, h]

/-- If the run committed (and there is no outstanding gas credit), the persistent data is the
committed `c4`. -/
theorem ComputeOutcome.ofHalt_commit (ec : Int) (stF : VmState) (data0 : Cell)
    (h : stF.cstate.committed = true) (hc : stF.gas.gasCredit = 0) :
    (ComputeOutcome.ofHalt ec stF data0).c4 = stF.cstate.c4 ∧
      (ComputeOutcome.ofHalt ec stF data0).c5 = stF.cstate.c5 := by
  simp [ComputeOutcome.ofHalt, h, hc]

/-- **Invariant preservation, reduced to committed states.** To show that an invariant on `c4`
survives a transaction it suffices to show it for committed final states; failed runs are
handled once and for all by the rollback rule. -/
theorem ComputeOutcome.ofHalt_preserves (Inv : Cell → Prop) (ec : Int) (stF : VmState)
    (data0 : Cell) (h0 : Inv data0)
    (hcommit : stF.cstate.committed = true → stF.gas.gasCredit = 0 → Inv stF.cstate.c4) :
    Inv (ComputeOutcome.ofHalt ec stF data0).c4 := by
  unfold ComputeOutcome.ofHalt
  by_cases h1 : stF.cstate.committed = true
  · by_cases h2 : stF.gas.gasCredit = 0
    · simp [h1, h2]; exact hcommit h1 h2
    · simp [h2]; exact h0
  · simp [h1]; exact h0

/-! ## The contract's environment: `c7` (SmartContractInfo) -/

/-- What the contract can observe about its environment (TVM `c7[0]`, "SmartContractInfo").
Field order of `params` is the TVM layout: `GETPARAM i` reads index `i`. -/
structure SmartContractInfo where
  actions : Int := 0
  msgsSent : Int := 0
  /-- `NOW`, index 3 -/
  now : Int
  /-- `BLOCKLT`, index 4 -/
  blockLt : Int
  /-- `LTIME`, index 5 -/
  txLt : Int
  /-- `RANDSEED`, index 6 -/
  randSeed : Value
  /-- `BALANCE`, index 7: `[grams, extra-currencies]` -/
  balanceGrams : Int
  /-- `MYADDR`, index 8 -/
  myAddr : Value
  /-- `CONFIGROOT`, index 9 -/
  configRoot : Value
  /-- `MYCODE`, index 10 -/
  myCode : Cell
  /-- `INCOMINGVALUE`, index 11 -/
  incomingGrams : Int
  /-- `STORAGEFEES`, index 12 -/
  storageFees : Int
  /-- `PREVBLOCKSINFOTUPLE`, index 13 -/
  prevBlocks : Value := .null
  /-- `UNPACKEDCONFIGTUPLE`, index 14 -/
  unpackedConfig : Array Value
  /-- `DUEPAYMENT`, index 15 -/
  duePayment : Int
  /-- `GETPRECOMPILEDGAS`, index 16 -/
  precompiledGas : Value
  /-- `INMSGPARAMS`, index 17 -/
  inMsgParams : Value

/-- The params tuple, in TVM index order (magic `0x076ef1ea` at index 0). -/
def SmartContractInfo.params (i : SmartContractInfo) : Array Value :=
  #[.int (.num 0x076ef1ea), .int (.num i.actions), .int (.num i.msgsSent), .int (.num i.now),
    .int (.num i.blockLt), .int (.num i.txLt), i.randSeed, .tuple #[.int (.num i.balanceGrams), .null],
    i.myAddr, i.configRoot, .cell i.myCode, .tuple #[.int (.num i.incomingGrams), .null],
    .int (.num i.storageFees), i.prevBlocks, .tuple i.unpackedConfig, .int (.num i.duePayment),
    i.precompiledGas, i.inMsgParams]

/-- Register `c7` as set up for the compute phase. The diff-test runner builds its `c7` with
this function, so the layout is checked against TON C++ on every fixture. -/
def SmartContractInfo.toC7 (i : SmartContractInfo) : Array Value := #[.tuple i.params]

@[simp] theorem SmartContractInfo.params_size (i : SmartContractInfo) : i.params.size = 18 := rfl
@[simp] theorem SmartContractInfo.params_now (i : SmartContractInfo) :
    i.params[3]! = .int (.num i.now) := rfl
@[simp] theorem SmartContractInfo.params_txLt (i : SmartContractInfo) :
    i.params[5]! = .int (.num i.txLt) := rfl
@[simp] theorem SmartContractInfo.params_balance (i : SmartContractInfo) :
    i.params[7]! = .tuple #[.int (.num i.balanceGrams), .null] := rfl
@[simp] theorem SmartContractInfo.params_myAddr (i : SmartContractInfo) :
    i.params[8]! = i.myAddr := rfl
@[simp] theorem SmartContractInfo.toC7_get (i : SmartContractInfo) :
    i.toC7[0]! = .tuple i.params := rfl

end TvmLean

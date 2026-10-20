import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Step.Core
import TvmLean.Semantics.Exec.Stack
import TvmLean.Semantics.Exec.Cont
import TvmLean.Semantics.Exec.Cell
import TvmLean.Semantics.Exec.Flow.Setcp
import TvmLean.Semantics.Exec.Flow.Ifret
import TvmLean.Semantics.Exec.Flow.Ifnotret
import TvmLean.Semantics.Exec.Flow.IfretAlt
import TvmLean.Semantics.Exec.Flow.If
import TvmLean.Semantics.Exec.Flow.Ifnot
import TvmLean.Semantics.Exec.Flow.PushSliceConst
import TvmLean.Semantics.Exec.Flow.PushCont
import TvmLean.Semantics.Exec.Flow.PushRef
import TvmLean.Semantics.Exec.Flow.PushRefSlice
import TvmLean.Semantics.Exec.Flow.PushRefCont
import TvmLean.Semantics.Exec.Flow.Execute
import TvmLean.Semantics.Exec.Flow.Jmpx
import TvmLean.Semantics.Exec.Flow.CallxArgs
import TvmLean.Semantics.Exec.Flow.JmpxArgs
import TvmLean.Semantics.Exec.Flow.Callcc
import TvmLean.Semantics.Exec.Flow.CallxVarArgs
import TvmLean.Semantics.Exec.Flow.Ret
import TvmLean.Semantics.Exec.Flow.RetAlt
import TvmLean.Semantics.Exec.Flow.RetBool
import TvmLean.Semantics.Exec.Flow.RetArgs
import TvmLean.Semantics.Exec.Flow.RetVarArgs
import TvmLean.Semantics.Exec.Flow.RetData
import TvmLean.Semantics.Exec.Flow.JmpxVarArgs
import TvmLean.Semantics.Exec.Flow.JmpxData
import TvmLean.Semantics.Exec.Flow.Ifjmp
import TvmLean.Semantics.Exec.Flow.Ifnotjmp
import TvmLean.Semantics.Exec.Flow.Ifelse
import TvmLean.Semantics.Exec.Flow.Ifref
import TvmLean.Semantics.Exec.Flow.Ifnotref
import TvmLean.Semantics.Exec.Flow.Ifjmpref
import TvmLean.Semantics.Exec.Flow.Ifnotjmpref
import TvmLean.Semantics.Exec.Flow.IfrefElse
import TvmLean.Semantics.Exec.Flow.IfelseRef
import TvmLean.Semantics.Exec.Flow.IfrefElseRef
import TvmLean.Semantics.Exec.Flow.IfBitJmp
import TvmLean.Semantics.Exec.Flow.CallRef
import TvmLean.Semantics.Exec.Flow.JmpRef
import TvmLean.Semantics.Exec.Flow.CallDict
import TvmLean.Semantics.Exec.Flow.PrepareDict
import TvmLean.Semantics.Exec.Flow.Until
import TvmLean.Semantics.Exec.Flow.While
import TvmLean.Semantics.Exec.Flow.LoopExt
import TvmLean.Semantics.Exec.Flow.Blkdrop2
import TvmLean.Semantics.Exec.Flow.Blkdrop
import TvmLean.Semantics.Exec.Flow.Drop2
import TvmLean.Semantics.Exec.Arith
import TvmLean.Semantics.Exec.Tuple
import TvmLean.Semantics.Exec.CellOp
import TvmLean.Semantics.Exec.TonEnv
import TvmLean.Semantics.Exec.Crypto
import TvmLean.Semantics.Exec.Msg
import TvmLean.Semantics.Exec.Misc
import TvmLean.Semantics.Exec.Debug
import TvmLean.Semantics.Exec.Exception
import TvmLean.Semantics.Exec.Dict

namespace TvmLean

def popNatUpToSigned (max : Nat) : VM Nat :=
  VM.popNatUpTo max

def popGasRange : VM Int := do
  let v ← VM.popInt
  match v with
  | .nan =>
      -- C++ `pop_long_range` maps NaN / non-int64 values to `range_chk`.
      throw .rangeChk
  | .num n =>
      if n < 0 ∨ n > GasLimits.infty then
        throw .rangeChk
      return n

def VM.popTuple : VM (Array Value) := do
  let v ← VM.pop
  match v with
  | .tuple t => return t
  | _ => throw .typeChk

set_option maxHeartbeats 1000000 in
def execInstrFlowChildNoRunvm (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrFlowSetcp i <|
  execInstrFlowIfret i <|
  execInstrFlowIfnotret i <|
  execInstrFlowIfretAlt i <|
  execInstrFlowIf i <|
  execInstrFlowIfnot i <|
  execInstrFlowPushSliceConst i <|
  execInstrFlowPushCont i <|
  execInstrFlowPushRef i <|
  execInstrFlowPushRefSlice i <|
  execInstrFlowPushRefCont i <|
  execInstrFlowExecute i <|
  execInstrFlowJmpx i <|
  execInstrFlowCallxArgs i <|
  execInstrFlowJmpxArgs i <|
  execInstrFlowCallcc i <|
  execInstrFlowCallxVarArgs i <|
  execInstrFlowRet i <|
  execInstrFlowRetAlt i <|
  execInstrFlowRetBool i <|
  execInstrFlowRetArgs i <|
  execInstrFlowRetVarArgs i <|
  execInstrFlowRetData i <|
  execInstrFlowJmpxVarArgs i <|
  execInstrFlowJmpxData i <|
  execInstrFlowIfjmp i <|
  execInstrFlowIfnotjmp i <|
  execInstrFlowIfelse i <|
  execInstrFlowIfref i <|
  execInstrFlowIfnotref i <|
  execInstrFlowIfjmpref i <|
  execInstrFlowIfnotjmpref i <|
  execInstrFlowIfrefElse i <|
  execInstrFlowIfelseRef i <|
  execInstrFlowIfrefElseRef i <|
  execInstrFlowIfBitJmp i <|
  execInstrFlowCallRef i <|
  execInstrFlowJmpRef i <|
  execInstrFlowCallDict i <|
  execInstrFlowPrepareDict i <|
  execInstrFlowUntil i <|
  execInstrFlowWhile i <|
  execInstrFlowLoopExt i <|
  execInstrFlowBlkdrop2 i <|
  execInstrFlowBlkdrop i <|
  execInstrFlowDrop2 i <|
    next

set_option maxHeartbeats 1000000 in
def execInstrChildNoRunvm (host : Host) (i : Instr) : VM Unit :=
  execInstrStack host i <|
    execInstrCont host i <|
      execInstrCell host i <|
        execInstrFlowChildNoRunvm host i <|
          execInstrArith host i <|
            execInstrTuple host i <|
              execInstrCellOp host i <|
                execInstrTonEnv host i <|
                  execInstrCrypto host i <|
                    execInstrMsg host i <|
                      execInstrMisc host i <|
                      execInstrDebug host i <|
                      execInstrException host i <|
                        execInstrDict host i <|
                          throw .invOpcode

/-- The child VM of `RUNVM` runs with the same `VmState::run` as the parent (C++ `run_child_vm`)
until it halts, which its gas bounds (`GasLimits.stepBound`); `exec` runs its instructions. Returns
the exit code and the final state. -/
def childRun (exec : Instr → VM Unit) (st : VmState) : Int × VmState :=
  match st.runWith exec st.gas.stepBound with
  | .halt exitCode st' => (exitCode, st')
  | .continue st' => (Excno.fatal.toInt, st')

set_option maxHeartbeats 1000000 in
def runChildVm (childExec : Instr → VM Unit) (parent : VmState) (mode : Nat) : VM VmState := do
  if mode ≥ 512 then
    throw .rangeChk

  -- Run on the provided parent state as the VM state.
  set (parent.consumeGas runvmGasPrice)
  if decide ((← get).gas.gasRemaining < 0) then
    throw .outOfGas

  -- Pop args in the same order as C++ `exec_runvm_common`.
  let sameC3 : Bool := (mode &&& 1) = 1
  let push0 : Bool := (mode &&& 2) = 2
  let withData : Bool := (mode &&& 4) = 4
  let returnGas : Bool := (mode &&& 8) = 8
  let loadC7 : Bool := (mode &&& 16) = 16
  let returnActions : Bool := (mode &&& 32) = 32
  let hasHardMax : Bool := (mode &&& 64) = 64
  let isolateGas : Bool := (mode &&& 128) = 128
  let hasRetVals : Bool := (mode &&& 256) = 256

  let gasMax0 : Int ←
    if hasHardMax then
      popGasRange
    else
      pure GasLimits.infty
  let gasLimit0 : Int ←
    if returnGas then
      popGasRange
    else
      pure GasLimits.infty
  let gasMax1 : Int := if hasHardMax then max gasMax0 gasLimit0 else gasLimit0

  let c7Opt : Option (Array Value) ←
    if loadC7 then
      some <$> VM.popTuple
    else
      pure none

  let dataOpt : Option Cell ←
    if withData then
      some <$> VM.popCell
    else
      pure none

  let retValsOpt : Option Nat ←
    if hasRetVals then
      some <$> VM.popNatUpTo (1 <<< 30)
    else
      pure none

  let codeSlice ← VM.popSlice

  let stBeforeSize ← get
  if stBeforeSize.stack.size = 0 then
    throw .stkUnd
  let stackSize : Nat ←
    match (← VM.popInt) with
    | .nan => throw .rangeChk
    | .num n =>
        if n < 0 then
          throw .rangeChk
        else
          pure n.toNat
  let stAfterSize ← get
  if stackSize > stAfterSize.stack.size then
    throw .rangeChk

  let mut childStack : Array Value := Array.replicate stackSize .null
  for i in [0:stackSize] do
    let v ← VM.pop
    childStack := childStack.set! (stackSize - 1 - i) v

  modify fun st => st.consumeStackGas stackSize
  if decide ((← get).gas.gasRemaining < 0) then
    throw .outOfGas

  -- C++ `init_cregs`: `push_0` is honored only when `same_c3` is set.
  if sameC3 && push0 then
    childStack := childStack.push (.int (.num 0))

  let childCc : Continuation := .ordinary codeSlice (.quit 0) OrdCregs.empty OrdCdata.empty
  let childRegs0 : Regs := Regs.initial
  let childRegs1 : Regs := if sameC3 then { childRegs0 with c3 := childCc } else childRegs0
  let childRegs2 : Regs :=
    match c7Opt with
    | none => childRegs1
    | some t => { childRegs1 with c7 := t }
  let childRegs3 : Regs :=
    match dataOpt with
    | none => childRegs2
    | some c => { childRegs2 with c4 := c }

  -- `exec_runvm_common` clamps the child's limits by the gas left (contops.cpp:260-261)
  let parentRem0 : Int := (← get).gas.gasRemaining

  -- C++ `run_child_vm`: with isolated gas the parent pays its free gas now and its counters restart;
  -- the child starts with the parent's counters; from version 10 its gas limits are clamped again by
  -- what is left after that (vm.cpp:752-757).
  if isolateGas then
    VM.consumeGas (← get).freeGasConsumed
    modify fun st => { st with chksgnCounter := 0, getExtraBalanceCounter := 0, freeGasConsumed := 0 }

  let parentAfterPops ← get

  let parentRem : Int :=
    if parentAfterPops.globalVersion ≥ 10 then parentAfterPops.gas.gasRemaining else parentRem0
  let gasMax : Int := min gasMax1 parentRem
  let gasLimit : Int := min gasLimit0 parentRem
  let childGas : GasLimits := GasLimits.ofLimits gasLimit gasMax 0

  let child : VmState :=
    { (VmState.initial codeSlice.cell) with
      stack := childStack
      regs := childRegs3
      cc := childCc
      gas := childGas
      loadedCells := if isolateGas then #[] else parentAfterPops.loadedCells
      chksgnCounter := parentAfterPops.chksgnCounter
      getExtraBalanceCounter := parentAfterPops.getExtraBalanceCounter
      freeGasConsumed := parentAfterPops.freeGasConsumed
      libraries := parentAfterPops.libraries
      maxDataDepth := parentAfterPops.maxDataDepth
      globalVersion := parentAfterPops.globalVersion }

  let (childExit, childFinal) := childRun childExec child
  let mut resCode : Int := ~~~ childExit

  let childConsumed : Int := childFinal.gas.gasConsumed
  let pay : Int := min childConsumed (childFinal.gas.gasLimit + 1)
  let mut parentAfter : VmState := parentAfterPops.consumeGas pay
  parentAfter := { parentAfter with
    steps := parentAfter.steps + childFinal.steps
    libraries := childFinal.libraries
    chksgnCounter := childFinal.chksgnCounter
    getExtraBalanceCounter := childFinal.getExtraBalanceCounter
    freeGasConsumed := childFinal.freeGasConsumed
    loadedCells := if isolateGas then parentAfter.loadedCells else childFinal.loadedCells }
  -- `consume_gas` of the child's gas: out of gas at once, with the payment counted
  if decide (parentAfter.gas.gasRemaining < 0) then
    set parentAfter
    throw .outOfGas

  let depth := childFinal.stack.size
  let mut retCnt : Nat := 0
  if resCode = 0 ∨ resCode = 1 then
    match retValsOpt with
    | some n =>
        if depth ≥ n then
          retCnt := n
        else
          retCnt := 0
          resCode := ~~~ Excno.stkUnd.toInt
          parentAfter := { parentAfter with stack := parentAfter.stack.push (.int (.num 0)) }
    | none =>
        retCnt := depth
  else
    retCnt := Nat.min depth 1

  -- C++ `restore_parent_vm`: charge stack gas for returned value count before pushes.
  parentAfter := parentAfter.consumeStackGas retCnt
  if decide (parentAfter.gas.gasRemaining < 0) then
    set parentAfter
    throw .outOfGas

  for i in List.range retCnt |>.reverse do
    let pos := depth - 1 - i
    parentAfter := { parentAfter with stack := parentAfter.stack.push (childFinal.stack[pos]!) }

  parentAfter := { parentAfter with stack := parentAfter.stack.push (.int (.num resCode)) }

  -- the committed `c4` and `c5` of the child; if it did not commit, null from version 11, before a
  -- cell entry without a cell (the committed state's null cells, vm.cpp:811-826)
  let uncommitted : Value := if parentAfter.globalVersion ≥ 11 then .null else .nullCell
  if withData then
    if childFinal.cstate.committed then
      parentAfter := { parentAfter with stack := parentAfter.stack.push (.cell childFinal.cstate.c4) }
    else
      parentAfter := { parentAfter with stack := parentAfter.stack.push uncommitted }
  if returnActions then
    if childFinal.cstate.committed then
      parentAfter := { parentAfter with stack := parentAfter.stack.push (.cell childFinal.cstate.c5) }
    else
      parentAfter := { parentAfter with stack := parentAfter.stack.push uncommitted }
  if returnGas then
    parentAfter := { parentAfter with stack := parentAfter.stack.push (.int (.num childConsumed)) }

  return parentAfter

/-- `RUNVM` and `RUNVMX`, running the child with the instructions `childExec`. -/
def execInstrFlowRunvmWith (childExec : Instr → VM Unit) (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt (.runvm mode) =>
      -- Match C++ helper canonicalization (`exec_runvm(..., args & 4095)`).
      let mode := mode &&& 0xfff
      let st ← get
      let st' ← runChildVm childExec st mode
      set st'
  | .contExt .runvmx =>
      let mode ← popNatUpToSigned 4095
      let st ← get
      let st' ← runChildVm childExec st mode
      set st'
  | _ =>
      next

/-- The instructions of a child VM `depth` levels above the deepest one `RUNVM` can still create:
its own `RUNVM` runs the child with `execInstrNested (depth - 1)` (C++ nests child VMs without a
limit, `run_child_vm`). A VM at depth `d` has at most `runvmGasPrice * d - 1` gas: `RUNVM` charges
`runvmGasPrice` before the child runs and gives it at most the gas left (contops.cpp:230, 260-261),
so a VM at depth 0 is never run. -/
def execInstrNested : Nat → Host → Instr → VM Unit
  | 0, host => execInstrChildNoRunvm host
  | depth + 1, host => fun i => execInstrFlowRunvmWith (execInstrNested depth host) i (execInstrChildNoRunvm host i)

-- Leaf module hook used by `TvmLean.Semantics.Exec.Flow`.
/-- `RUNVM` and `RUNVMX` of the VM: the child gets at most the gas left, so it runs at depth
`gas left / runvmGasPrice + 1` (`execInstrNested`). -/
def execInstrFlowRunvm (host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
  let depth := (← get).gas.gasRemaining.toNat / runvmGasPrice.toNat + 1
  execInstrFlowRunvmWith (execInstrNested depth host) i next

end TvmLean

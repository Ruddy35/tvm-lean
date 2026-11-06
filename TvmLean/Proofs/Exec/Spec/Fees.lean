import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: the fee getters (`GETSTORAGEFEE`, `GETFORWARDFEE`, `GETFORWARDFEESIMPLE`, `GETORIGINALFWDFEE`, `GETGASFEE`, `GETGASFEESIMPLE`)

The fee getters (C++ `exec_get_storage_fee`, `exec_get_forward_fee`, `exec_get_forward_fee_simple`,
`exec_get_original_fwd_fee`, `exec_get_gas_fee`, `exec_get_gas_fee_simple`, tonops.cpp) read the
prices from the configuration's tuple (`c7[0][14]`, `VM.getUnpackedConfigTuple`) and parse them
(`parseMsgPrices`, the parsers of `VM.getGasPrices`, the fields of the storage prices read one by
one): on prices a run does not know, the parse of 64-bit fields of an unknown slice. Here the parses
are `Fee.parseMsg`, `Fee.parseGas` and `Fee.take`, irreducible (the same functions): a run leaves
their result a term, and `vm_split` splits the `match` on it (prices found, any; or an exception).
The handlers are written again with them (`Fee.getMsgPrices`, `Fee.getGasPrices`,
`Fee.storageFeeProg`), the same programs:

* `Fee.getMsgPrices_eq`, `Fee.getGasPrices_eq`: `VM.getMsgPrices`, `VM.getGasPrices` are them;
* `Spec.getStorageFee`, `Spec.getForwardFee`, `Spec.getForwardFeeSimple`, `Spec.getOriginalFwdFee`,
  `Spec.getGasFee`, `Spec.getGasFeeSimple` (`vm_spec`): the instructions run as `Fee.storageFeeProg`,
  `Fee.forwardFeeProg`, ... .
-/

namespace TvmLean

namespace Fee

/-- `parseMsgPrices` (C++ `Config::do_get_msg_prices`), irreducible. -/
@[irreducible] def parseMsg (pricesCs : Slice) : Except Excno (Int × Int × Int × Nat × Nat) :=
  parseMsgPrices pricesCs

/-- `VM.getMsgPrices` with the parse `parseMsg`: the same code. -/
def getMsgPrices (isMasterchain : Bool) : VM (Int × Int × Int × Nat × Nat) := do
  let unpacked ← VM.getUnpackedConfigTuple
  let idx : Nat := if isMasterchain then 4 else 5
  match unpacked[idx]? with
  | some (.slice pricesCs) =>
      match parseMsg pricesCs with
      | .ok p => return p
      | .error e => throw e
  | some .null => throw .typeChk
  | some _ => throw .typeChk
  | none => throw .rangeChk

theorem getMsgPrices_eq (isMasterchain : Bool) : VM.getMsgPrices isMasterchain = getMsgPrices isMasterchain := by
  unfold VM.getMsgPrices getMsgPrices parseMsg
  rfl

/-- The parse of the gas prices of `VM.getGasPrices` (C++ `Config::do_get_gas_limits_prices`),
irreducible: the same code. -/
@[irreducible] def parseGas (cs : Slice) : Except Excno (Nat × Nat × Nat) :=
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
  parseGasLimitsPrices cs

/-- `VM.getGasPrices` with the parse `parseGas`: the same code. -/
def getGasPrices (isMasterchain : Bool) : VM (Nat × Nat × Nat) := do
  let unpacked ← VM.getUnpackedConfigTuple
  let idx : Nat := if isMasterchain then 2 else 3
  match unpacked[idx]? with
  | some (.slice pricesCs) =>
      match (parseGas pricesCs : Except Excno (Nat × Nat × Nat)) with
      | .ok (gasPrice, flatGasLimit, flatGasPrice) => return (gasPrice, flatGasLimit, flatGasPrice)
      | .error e => throw e
  | some .null => throw .typeChk
  | some _ => throw .typeChk
  | none => throw .rangeChk

theorem getGasPrices_eq (isMasterchain : Bool) : VM.getGasPrices isMasterchain = getGasPrices isMasterchain := by
  unfold VM.getGasPrices getGasPrices parseGas
  rfl

/-- A field of the storage prices (`Slice.takeBitsAsNatCellUnd`), irreducible. -/
@[irreducible] def take (s : Slice) (n : Nat) : Except Excno (Nat × Slice) :=
  s.takeBitsAsNatCellUnd n

theorem takeBitsAsNatCellUnd_eq (s : Slice) (n : Nat) : s.takeBitsAsNatCellUnd n = take s n := by
  unfold take
  rfl

/-- The read of a field by `take` in the VM: its result, a term (`vm_split` splits the `match`). -/
@[vm_run] theorem run_take (s : Slice) (n : Nat) (st : VmState) :
    ExceptT.run (liftM (take s n) : VM (Nat × Slice)) st =
      match take s n with
      | .ok a => (.ok a, st)
      | .error e => (.error e, st) := by
  cases take s n <;> rfl

/-- `GETSTORAGEFEE` (`execInstrTonEnvGetStorageFee`) with the fields of the prices read by `take`. -/
def storageFeeProg : VM Unit := do
  if (← get).globalVersion ≥ 9 then
    VM.checkUnderflow 4
  let isMasterchain ← VM.popBool
  let max63 : Nat := (1 <<< 63) - 1
  let delta ← VM.popNatUpTo max63
  let bits ← VM.popNatUpTo max63
  let cells ← VM.popNatUpTo max63
  let unpacked ← VM.getUnpackedConfigTuple
  match unpacked[0]? with
  | some Value.null =>
      VM.pushSmallInt 0
  | some (Value.slice pricesCs) =>
      let (tag, s1) ← take pricesCs 8
      if tag != 0xcc then
        throw .cellUnd
      let (_, s2) ← take s1 32
      let (bitPrice, s3) ← take s2 64
      let (cellPrice, s4) ← take s3 64
      let (mcBitPrice, s5) ← take s4 64
      let (mcCellPrice, _) ← take s5 64
      let bitP : Nat := if isMasterchain then mcBitPrice else bitPrice
      let cellP : Nat := if isMasterchain then mcCellPrice else cellPrice
      let total : Int :=
        (Int.ofNat cells * int64Wrap (Int.ofNat cellP) + Int.ofNat bits * int64Wrap (Int.ofNat bitP)) * Int.ofNat delta
      let fee : Int := ceilDivPow2 total 16
      VM.pushIntQuiet (.num fee) false
  | some _ =>
      VM.pushSmallInt 0
  | none =>
      throw .rangeChk

/-- `GETFORWARDFEE` (`execInstrTonEnvGetForwardFee`) with `Fee.getMsgPrices`. -/
def forwardFeeProg : VM Unit := do
  if (← get).globalVersion ≥ 9 then
    VM.checkUnderflow 3
  let isMasterchain ← VM.popBool
  let max63 : Nat := (1 <<< 63) - 1
  let bits ← VM.popNatUpTo max63
  let cells ← VM.popNatUpTo max63
  let (lumpPrice, bitPrice, cellPrice, _, _) ← getMsgPrices isMasterchain
  let x : Int := bitPrice * Int.ofNat bits + cellPrice * Int.ofNat cells
  let res : Int := lumpPrice + ceilDivPow2 x 16
  VM.pushIntQuiet (.num res) false

/-- `GETFORWARDFEESIMPLE` (`execInstrTonEnvGetForwardFeeSimple`) with `Fee.getMsgPrices`. -/
def forwardFeeSimpleProg : VM Unit := do
  if (← get).globalVersion ≥ 9 then
    VM.checkUnderflow 3
  let isMasterchain ← VM.popBool
  let max63 : Nat := (1 <<< 63) - 1
  let bits ← VM.popNatUpTo max63
  let cells ← VM.popNatUpTo max63
  let (_, bitPrice, cellPrice, _, _) ← getMsgPrices isMasterchain
  let x : Int := bitPrice * Int.ofNat bits + cellPrice * Int.ofNat cells
  let res : Int := ceilDivPow2 x 16
  VM.pushIntQuiet (.num res) false

/-- `GETORIGINALFWDFEE` (`execInstrTonEnvGetOriginalFwdFee`) with `Fee.getMsgPrices`. -/
def originalFwdFeeProg : VM Unit := do
  if (← get).globalVersion ≥ 9 then
    VM.checkUnderflow 2
  let isMasterchain ← VM.popBool
  let fwdFee ← VM.popIntFinite
  if fwdFee < 0 then
    throw .rangeChk
  let (_, _, _, _, firstFrac) ← getMsgPrices isMasterchain
  if (1 <<< 16) ≤ firstFrac then
    throw .cellUnd
  let denom : Int := Int.ofNat ((1 <<< 16) - firstFrac)
  let res : Int := (fwdFee * intPow2 16) / denom
  VM.pushIntQuiet (.num res) false

/-- `GETGASFEE` (`execInstrTonEnvGetGasFee`) with `Fee.getGasPrices`. -/
def gasFeeProg : VM Unit := do
  if (← get).globalVersion ≥ 9 then
    VM.checkUnderflow 2
  let isMasterchain ← VM.popBool
  let max63 : Nat := (1 <<< 63) - 1
  let gasUsed ← VM.popNatUpTo max63
  let (gasPrice, flatGasLimit, flatGasPrice) ← getGasPrices isMasterchain
  let fee : Int :=
    if gasUsed ≤ flatGasLimit then
      Int.ofNat flatGasPrice
    else
      let varPart : Int := Int.ofNat gasPrice * Int.ofNat (gasUsed - flatGasLimit);
      refIntAddLong (ceilDivPow2 varPart 16) (int64Wrap (Int.ofNat flatGasPrice))
  VM.pushIntQuiet (.num fee) false

/-- `GETGASFEESIMPLE` (`execInstrTonEnvGetGasFeeSimple`) with `Fee.getGasPrices`. -/
def gasFeeSimpleProg : VM Unit := do
  if (← get).globalVersion ≥ 9 then
    VM.checkUnderflow 2
  let isMasterchain ← VM.popBool
  let max63 : Nat := (1 <<< 63) - 1
  let gasUsed ← VM.popNatUpTo max63
  let (gasPrice, _, _) ← getGasPrices isMasterchain
  let fee : Int := ceilDivPow2 (Int.ofNat gasPrice * Int.ofNat gasUsed) 16
  VM.pushIntQuiet (.num fee) false

end Fee

namespace Spec

set_option maxHeartbeats 4000000 in
/-- `GETSTORAGEFEE` runs as `Fee.storageFeeProg`. -/
@[vm_spec] theorem getStorageFee (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .getStorageFee)) st = ExceptT.run Fee.storageFeeProg st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, Fee.storageFeeProg, Fee.takeBitsAsNatCellUnd_eq, VM.run_bind, VM.run_get,
    VM.bindRes_ok]
  try rfl

set_option maxHeartbeats 4000000 in
/-- `GETFORWARDFEE` runs as `Fee.forwardFeeProg`. -/
@[vm_spec] theorem getForwardFee (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .getForwardFee)) st = ExceptT.run Fee.forwardFeeProg st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, Fee.forwardFeeProg, Fee.getMsgPrices_eq, VM.run_bind, VM.run_get,
    VM.bindRes_ok]
  try rfl

set_option maxHeartbeats 4000000 in
/-- `GETFORWARDFEESIMPLE` runs as `Fee.forwardFeeSimpleProg`. -/
@[vm_spec] theorem getForwardFeeSimple (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .getForwardFeeSimple)) st = ExceptT.run Fee.forwardFeeSimpleProg st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, Fee.forwardFeeSimpleProg, Fee.getMsgPrices_eq, VM.run_bind, VM.run_get,
    VM.bindRes_ok]
  try rfl

set_option maxHeartbeats 4000000 in
/-- `GETORIGINALFWDFEE` runs as `Fee.originalFwdFeeProg`. -/
@[vm_spec] theorem getOriginalFwdFee (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .getOriginalFwdFee)) st = ExceptT.run Fee.originalFwdFeeProg st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, Fee.originalFwdFeeProg, Fee.getMsgPrices_eq, VM.run_bind, VM.run_get,
    VM.bindRes_ok]
  try rfl

set_option maxHeartbeats 4000000 in
/-- `GETGASFEE` runs as `Fee.gasFeeProg`. -/
@[vm_spec] theorem getGasFee (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .getGasFee)) st = ExceptT.run Fee.gasFeeProg st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, Fee.gasFeeProg, Fee.getGasPrices_eq, VM.run_bind, VM.run_get,
    VM.bindRes_ok]
  try rfl

set_option maxHeartbeats 4000000 in
/-- `GETGASFEESIMPLE` runs as `Fee.gasFeeSimpleProg`. -/
@[vm_spec] theorem getGasFeeSimple (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp .getGasFeeSimple)) st = ExceptT.run Fee.gasFeeSimpleProg st := by
  simp only [TvmLean.Exec.reduceExecInstrRun, Fee.gasFeeSimpleProg, Fee.getGasPrices_eq, VM.run_bind, VM.run_get,
    VM.bindRes_ok]
  try rfl

end Spec

end TvmLean

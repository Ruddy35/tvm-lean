import TvmLean.Proofs.Tx.Phases

/-!
# A transaction, phase by phase

`emulate` and `emulateTickTock` (`TvmLean/Transaction/Emulate.lean`) run the phases of a transaction
one after the other and end with `Tx.computeState`, which writes the new account. `EmulateFinal`
and `TickTockFinal` name the state of the transaction before `computeState`, with the phases that
led to it; `emulate_final` and `emulateTickTock_final` show that every transaction the model
returns has such a decomposition. `newTx_spec` describes the state the transaction starts from: the
account read from the shard account (`Account.unpack`).
-/

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-- What the model returns, when it returns a transaction, satisfies `R tx account`. -/
def OKout (R : Cell → Cell → Prop) : Outcome → Prop
  | .ok tx acc => R tx acc
  | _ => True

/-- The state a transaction starts from (the `Transaction` constructor, `Account::unpack`): the
account of the shard account, its code, data and status, nothing taken from a message yet. -/
def StartsFrom (shardAccount : Cell) (cfg : Config) (wc : Int) (addr : BitString) (kind : TxKind) (t : Tx) : Prop :=
  ∃ a, Account.unpack shardAccount wc addr (wc == -1 && cfg.isSpecialSmc addr) = some a ∧
    t.account = { a with blockLt := t.account.blockLt } ∧ t.newCode = a.code ∧ t.newData = a.data ∧
    t.accStatus = (if a.status == .nonexist then .uninit else a.status) ∧ t.useMsgState = false ∧
    t.wasActivated = false ∧ t.wasFrozen = false ∧ t.computePhase.success = false ∧ t.inMsgState = none ∧
    t.kind = kind ∧ t.cfg = cfg

theorem newTx_spec (cfg : Config) (shardAccount inMsg : Cell) (kind : TxKind) (wc : Int) (addr addrBits : BitString)
    (lt now : Nat) (libs : Option Cell) :
    OKe (fun r : Tx × Array StoragePrices × SizeLimits × GasPrices × MsgPrices => StartsFrom shardAccount cfg wc addr kind r.1)
      (newTx cfg shardAccount inMsg kind wc addr addrBits lt now libs) := by
  unfold newTx
  tx_vcg
  all_goals tx_solve

/-- The storage and credit phases of an ordinary transaction: credit first unless the message
bounces (`needCredit`: the message is internal). -/
def StorageCredit (pricing : Array StoragePrices) (gas : GasPrices) (needCredit : Bool) (t1 t2 : Tx) : Prop :=
  (∃ ts, t1.storagePhaseRun pricing gas false = some ts ∧
    ((¬needCredit = true ∧ t2 = ts) ∨ (needCredit = true ∧ ts.creditPhaseRun = .ok (some t2)))) ∨
  (∃ tc, tc.storagePhaseRun pricing gas needCredit = some t2 ∧
    ((¬needCredit = true ∧ tc = t1) ∨ (needCredit = true ∧ t1.creditPhaseRun = .ok (some tc))))

/-- The state `tf` of an ordinary transaction before `computeState` (with the size limits `sl` it
writes the account with), and the phases that led to it: the start (`newTx`), the inbound message,
the storage and credit phases, the compute phase, the action phase if the compute phase succeeded,
the bounce phase if any. -/
def EmulateFinal (configRoot shardAccount inMsg : Cell) (now lt : Nat) (randSeed : BitString) (libs : Option Cell)
    (tf : Tx) (sl : SizeLimits) : Prop :=
  ∃ cfg wc addr addrBits t0 pricing gas fwd t1 t2 t3 t4,
    Config.decode configRoot = some cfg ∧
    newTx cfg shardAccount inMsg .ord wc addr addrBits lt now libs = .ok (t0, pricing, sl, gas, fwd) ∧
    t0.unpackInputMsg sl fwd = some (.ok t1) ∧
    (∃ needCredit, StorageCredit pricing gas needCredit t1 t2) ∧
    t2.computePhaseRun gas sl randSeed = .ok (some t3) ∧
    ((t3.computePhase.success = true ∧ t3.actionPhaseRun sl = .ok (some t4)) ∨
      (¬t3.computePhase.success = true ∧ t4 = t3)) ∧
    (tf = t4 ∨ t4.bouncePhaseRun = .ok (some tf))

set_option maxHeartbeats 2000000 in
/-- **Decomposition of `emulate`.** Every transaction the model returns ends with a state `tf` of
`EmulateFinal`, and the new account is the one `Tx.computeState` writes from it. -/
theorem emulate_final (configRoot shardAccount inMsg : Cell) (now lt : Nat) (randSeed : BitString)
    (libs : Option Cell) :
    OKp (OKout fun _ acc => ∃ tf sl t', tf.computeState sl = some (t', acc) ∧
        EmulateFinal configRoot shardAccount inMsg now lt randSeed libs tf sl)
      (emulate configRoot shardAccount inMsg now lt randSeed libs) := by
  unfold emulate
  tx_vcg
  all_goals try trivial
  all_goals tx_split_hyps
  all_goals tx_solve

/-- The state `tf` of a tick-tock transaction before `computeState` (with the size limits `sl`), and
the phases that led to it: the start (`newTx`, no message), the storage phase, the compute phase,
the action phase if the compute phase succeeded. -/
def TickTockFinal (configRoot shardAccount : Cell) (isTock : Bool) (now lt : Nat) (randSeed : BitString)
    (libs : Option Cell) (tf : Tx) (sl : SizeLimits) : Prop :=
  ∃ cfg kind wc addr addrBits t0 pricing gas fwd t2 t3,
    Config.decode configRoot = some cfg ∧
    newTx cfg shardAccount Cell.empty kind wc addr addrBits lt now libs = .ok (t0, pricing, sl, gas, fwd) ∧
    ((isTock = true ∧ kind = .tock) ∨ (¬isTock = true ∧ kind = .tick)) ∧
    t0.storagePhaseRun pricing gas false = some t2 ∧
    t2.computePhaseRun gas sl randSeed = .ok (some t3) ∧
    ((t3.computePhase.success = true ∧ t3.actionPhaseRun sl = .ok (some tf)) ∨
      (¬t3.computePhase.success = true ∧ tf = t3))

set_option maxHeartbeats 2000000 in
/-- **Decomposition of `emulateTickTock`.** -/
theorem emulateTickTock_final (configRoot shardAccount : Cell) (isTock : Bool) (now lt : Nat)
    (randSeed : BitString) (libs : Option Cell) :
    OKp (OKout fun _ acc => ∃ tf sl t', tf.computeState sl = some (t', acc) ∧
        TickTockFinal configRoot shardAccount isTock now lt randSeed libs tf sl)
      (emulateTickTock configRoot shardAccount isTock now lt randSeed libs) := by
  unfold emulateTickTock
  tx_vcg
  all_goals try trivial
  all_goals tx_split_hyps
  all_goals tx_solve

end TvmLean.Tx

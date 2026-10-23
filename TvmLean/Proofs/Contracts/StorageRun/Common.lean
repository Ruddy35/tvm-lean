import TvmLean.Proofs.Contracts.Wallet3Run.Common
import TvmLean.Proofs.Contracts.StorageCode
import TvmLean.Proofs.Contracts.StorageRun.Read
import TvmLean.Proofs.Exec.Framed
import TvmLean.Proofs.Exec.Spec.MsgAddr
import TvmLean.Proofs.Exec.Spec.MsgExt
import TvmLean.Proofs.Exec.Spec.ArithExt
import TvmLean.Proofs.Exec.Spec.CellExt
import TvmLean.Proofs.Exec.Spec.StackExt
import TvmLean.Proofs.Exec.Spec.Tuple
import TvmLean.Proofs.Tx.NoSetCode

/-!
# TON Storage from every state the compute phase starts from: the statements

The runs of `storageCode` that `TvmLean/Proofs/Contracts/StorageInduction.lean` needs, stated on
`Run.start`: the state of `TvmLean.Tx.VmStart` (the compute phase's `computePhaseInit` of the code,
`c7 = #[c7]`, any gas limits `gl gm gc`, global version `gv`, libraries, `max_data_depth` and
`max_library_loads`), with any set of loaded cells `lc`.

The outcome of a committed run of `recv_internal` (`Run.Outcome`), by path of
`storage-contract.fc`:
* `keep`: the data and no action (a bounced message, an operation the contract does not know);
* `credit`: `add_to_balance(msg_value)`, no action (an empty body, operation 0);
* `deploy`: `add_to_balance(msg_value - 2 * fee::receipt_value)`, one message (mode 0);
* `accept`: the flag `active` set, one message (mode 0);
* `closeInactive`, `closeActive`: the data kept, one message (mode 128 + 32), or two (64, then
  128 + 32);
* `withdraw`, `withdrawReserve`: the data kept, one message (mode 128 + 32), after a
  `RAWRESERVE` (mode 2) when the balance is positive;
* `proof`: the balance, the next byte to prove and the time of the proof changed, one message
  (mode 64 + 2).

`Run.Outcome.weak`: every outcome keeps the fixed fields (`Data.Fixed`), the widths, the flag
`active` once set, and an action list of `SENDRAWMSG` and `RAWRESERVE` actions only
(`SafeActs`, TvmLean/Proofs/Tx/NoSetCode.lean).

The tactics the runs use: `storage_dead` (a path ended by an exception: dead), `storage_commit`
(a path that halts normally: the commit), `storage_no_commit`, `storage_step` (`vm_step` with the
reads of the data, `StorageRun/Read.lean`, builders written as bit strings whose sizes `omega`
bounds, the data `add_to_balance` writes as `Data.encode`, and the long `PUSHCONT` bodies by name,
`storageFoldCode`), `vm_forget` (the gas, loaded cells and step count of the run become variables:
the terms of a long run stay small), `storage_run_to n` (the run up to bit `n` of the current
cell, through every branch), `vm_loop_keep_c5` (the loop rule for a loop that sends nothing).
-/

/-! ## The closed facts of the code, over the fast twins -/

set_option Elab.async false in
fast_twin TvmLean.Contracts.storageCode

namespace TvmLean.Contracts.Storage

open TvmLean

/-! ## The code `PUSHCONT` makes, by name

`PUSHCONT` makes a new cell of the bits of its body (and the references it takes). Decoded from the
code (`Exec.stepCode`), that cell is a literal of its bits; a run then carries the literal in every
state until the body returns, and every `simp` of a step goes through it. The two long bodies the
runs enter are named here, and `storageFoldCode` puts the name back for the literal (they are
definitionally equal: the name unfolds to the same literal). -/

/-- The body of `accept_storage_contract` (the `PUSHCONT` at bit 0 of `storageCode_c9`, 632 bits). -/
def acceptCode : Cell :=
  Cell.mkOrdinary (cellBits! "ED44D0D200FA00FA4003B3F2E3EF5350C705F2E1917FC8CA0058FA0201CF1621CF16C9ED54F003F8258210D4CAEDCD708018C8CB055005CF168209312D00FA0214CB6A13CB1F12CB3FCBFFC970FB00") #[]

/-- The body of `deploy_storage_contract` (the `PUSHCONT` at bit 370 of `recv_internal`'s cell, 424
bits and the reference `storageCode_c8`, `add_to_balance`). -/
def deployCode : Cell :=
  Cell.mkOrdinary (cellBits! "04820A625A00A1DB3CED44D0F0038210BF7BD0C1708018C8CB055004CF168209312D00FA0213CB6A12CB1F5220CB3FCBFFC970FB00") #[storageCode_c8]

-- the two bodies are the bits of the code at those places
#guard acceptCode.bits = storageCode_c9.bits.extract 16 648
#guard deployCode.bits = (storageCode.refs[0]!.refs[0]!.refs[0]!.refs[0]!).bits.extract 386 810

set_option Elab.async false in
fast_twin TvmLean.Contracts.Storage.acceptCode TvmLean.Contracts.Storage.deployCode

open Lean Meta Simp in
/-- A literal cell of the code that `PUSHCONT` made (`Cell.mk` of a bit array of the length of
`acceptCode` or `deployCode`): that name, when definitionally equal. -/
simproc ↓ storageFoldCode (Cell.mk _ _ _ _) := fun e => do
  unless !e.hasFVar && !e.hasMVar do return .continue
  let some n := (e.getArg! 0).arrayLit?.map (·.2.length) | return .continue
  for (c, k) in [(``acceptCode, 632), (``deployCode, 424)] do
    if n == k then
      if ← withDefault (isDefEq e (mkConst c)) then
        return .done { expr := mkConst c }
  return .continue

/-- The data `add_to_balance` writes (`NEWC 1 STI STGRAMS STSLICER ENDC`: the flag, the new balance
`x`, the rest of the data; the builder as `storage_step` writes it) is the data with the balance
`x`: the run goes on with `Data.encode`, which the reads of `StorageRun/Read.lean` know. -/
theorem Data.credit_cell (d : Data) (x : Nat) :
    Builder.finalize
      { bits := #[d.active] ++ (natToBits ((natLenBits x + 7) / 8) 4 ++ (natToBits x ((natLenBits x + 7) / 8 * 8) ++
          (d.provider ++ (natToBits d.merkleHash 256 ++ (natToBits d.fileSize 64 ++ (natToBits d.nextProof 64 ++
            (natToBits (coinsLen d.ratePerMbDay) 4 ++ (natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++
              (natToBits d.maxSpan 32 ++ natToBits d.lastProofTime 32))))))))),
        refs := #[d.clientCell] } =
      Data.encode { d with balance := x } := by
  simp only [Builder.finalize, Data.encode, Data.bits, coinsBits, coinsLen, Data.clientCell, Array.append_assoc]

/-- `CTOS` of the data cell of any `d` (`Spec.ctos` with `Data.encode_special`): also of the data a
run wrote itself (`deploy_storage_contract` reads the data `add_to_balance` wrote). -/
@[vm_spec] theorem ctos_encode (st : VmState) (s : Stack) (d : Data) (hs : st.stack = s.push (.cell (Data.encode d))) :
    ExceptT.run (execInstr .ctos) st =
      if ({ st with stack := s }.registerCellLoad (Data.encode d)).gasExhaustedNow then
        (.error .outOfGas, { st with stack := s }.registerCellLoad (Data.encode d))
      else
        (.ok (), { { st with stack := s }.registerCellLoad (Data.encode d) with
          stack := s.push (.slice (Slice.ofCell (Data.encode d))) }) :=
  Spec.ctos st s _ hs (Data.encode_special d)

theorem Data.clientCell_balance (d : Data) (x : Nat) : Data.clientCell { d with balance := x } = d.clientCell := rfl

/-- The binary length of `n` is at most `k` when `n < 2 ^ k`. -/
theorem natLenBits_le_of_lt {n k : Nat} (h : n < 2 ^ k) : natLenBits n ≤ k := by
  unfold natLenBits
  split
  · omega
  · have := (Nat.log2_lt (by assumption)).2 h
    omega

/-- `VmState.callTo` (the call of `IF`, `IFELSE`, `IFREFELSE`, ...) is the call `VM.call` makes:
`c0` becomes the return continuation `VmState.retCont`. -/
theorem callTo_eq (st : VmState) (k : Continuation) :
    st.callTo k = { st with regs := { st.regs with c0 := st.retCont }, cc := k } := by
  unfold VmState.callTo VmState.callToWithFrame VmState.retCont
  cases st.cc <;> rfl

/-- The fields the contract never changes: the provider, the Merkle root and the size of the file,
the rate, the longest span paid, the client and the torrent hash. -/
def Data.Fixed (d d' : Data) : Prop :=
  d'.provider = d.provider ∧ d'.merkleHash = d.merkleHash ∧ d'.fileSize = d.fileSize ∧
    d'.ratePerMbDay = d.ratePerMbDay ∧ d'.maxSpan = d.maxSpan ∧ d'.client = d.client ∧
    d'.torrentHash = d.torrentHash

namespace Run

/-- The state the compute phase starts `storageCode` from (`TvmLean.Tx.VmStart`, the code loaded as
itself), with the loaded cells `lc`. -/
def start (data : Cell) (stack : Stack) (c7 : Value) (gl gm gc : Int) (gv : Nat) (libs : Array Cell)
    (mdd : Nat) (mll : Option Nat) (lc : Array (Array UInt8)) : VmState :=
  { computePhaseInit storageCode data stack #[c7] gl gm gc gv with
    libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll, loadedCells := lc }

/-- The outcome of a committed run of `recv_internal` on the data `d` with the message value `val`,
by path of `storage-contract.fc` (the messages sent are any cells). -/
inductive Outcome (d : Data) (val : Int) : Cell → Cell → Prop
  /-- A bounced message, or an operation the contract does not know: nothing changes. -/
  | keep : Outcome d val d.encode Cell.empty
  /-- An empty body or operation 0: `add_to_balance(msg_value)`. -/
  | credit (b : Nat) : (b : Int) = d.balance + val → coinsLen b < 16 →
      Outcome d val (Data.encode { d with balance := b }) Cell.empty
  /-- `deploy_storage_contract`: `add_to_balance(msg_value - 2 * fee::receipt_value)`, then the
  message `contract_deployed` to the client (mode 0). -/
  | deploy (b : Nat) (msg : Cell) : (b : Int) = d.balance + (val - 40000000) → coinsLen b < 16 →
      Outcome d val (Data.encode { d with balance := b }) (OutAction.sendMsg 0 Cell.empty msg)
  /-- `accept_storage_contract` (from the provider, the contract not active): the contract becomes
  active, the message `storage_contract_confirmed` to the client (mode 0). -/
  | accept (msg : Cell) : d.active = false →
      Outcome d val (Data.encode { d with active := true }) (OutAction.sendMsg 0 Cell.empty msg)
  /-- `close_contract` of a contract not active (from the provider or the client): the message
  `storage_contract_terminated` with all the balance to the client (mode 128 + 32). -/
  | closeInactive (msg : Cell) : d.active = false → Outcome d val d.encode (OutAction.sendMsg 160 Cell.empty msg)
  /-- `close_contract` of an active contract: the client gets its part (mode 64), the provider the
  rest (mode 128 + 32). -/
  | closeActive (m1 m2 : Cell) : d.active = true →
      Outcome d val d.encode (OutAction.sendMsg 160 (OutAction.sendMsg 64 Cell.empty m1) m2)
  /-- `withdraw` (from the provider, active, nothing earned yet): `reward_withdrawal` with all the
  balance to the provider (mode 128 + 32). -/
  | withdraw (msg : Cell) : d.active = true → d.balance = 0 →
      Outcome d val d.encode (OutAction.sendMsg 160 Cell.empty msg)
  /-- `withdraw` with a balance: `raw_reserve(balance + fee::storage, 2)`, then `reward_withdrawal`
  with the rest to the provider (mode 128 + 32). -/
  | withdrawReserve (msg : Cell) : d.active = true → 0 < d.balance →
      Outcome d val d.encode
        (OutAction.sendMsg 160 (OutAction.reserve 2 (d.balance + 10000000) Cell.empty) msg)
  /-- `proof_storage` (from the provider, active, the proof checked): the balance less the bounty
  `b`, the next byte to prove `n` (`rand(file_size)`), the time of the proof `t` (`now()`), the
  rest of the message value back to the sender (mode 64 + 2). -/
  | proof (b n t : Nat) (msg : Cell) : d.active = true → coinsLen b < 16 → n < 2 ^ 64 → t < 2 ^ 32 →
      Outcome d val (Data.encode { d with balance := b, nextProof := n, lastProofTime := t })
        (OutAction.sendMsg 66 Cell.empty msg)

/-- The weak outcome: data `encode d'` of a `d'` within its widths that keeps the fixed fields and
the flag `active` once set, and an action list of `SENDRAWMSG` and `RAWRESERVE` actions only. -/
def Weak (d : Data) (c4 c5 : Cell) : Prop :=
  ∃ d', c4 = d'.encode ∧ d'.WF ∧ Data.Fixed d d' ∧ (d.active = true → d'.active = true) ∧ SafeActs c5

/-- What a committed run leaves from the data `d` and a message of value `val`. -/
def Post (d : Data) (val : Int) (r : StepResult) : Prop :=
  r.state.cstate.committed = true → Outcome d val r.state.cstate.c4 r.state.cstate.c5

/-- **Every outcome keeps the fixed fields**, the widths, and the flag `active` once set, and its
actions are `SENDRAWMSG` and `RAWRESERVE` only. -/
theorem Outcome.weak {d : Data} {val : Int} {c4 c5 : Cell} (hwf : d.WF) (h : Outcome d val c4 c5) :
    Weak d c4 c5 := by
  obtain ⟨hb, hp, hm, hf, hn, hr, hs, hl, hc, ht⟩ := hwf
  have fx : ∀ d' : Data, d'.provider = d.provider → d'.merkleHash = d.merkleHash → d'.fileSize = d.fileSize →
      d'.ratePerMbDay = d.ratePerMbDay → d'.maxSpan = d.maxSpan → d'.client = d.client →
      d'.torrentHash = d.torrentHash → Data.Fixed d d' :=
    fun _ h1 h2 h3 h4 h5 h6 h7 => ⟨h1, h2, h3, h4, h5, h6, h7⟩
  cases h with
  | keep => exact ⟨d, rfl, ⟨hb, hp, hm, hf, hn, hr, hs, hl, hc, ht⟩, fx d rfl rfl rfl rfl rfl rfl rfl, id, .empty⟩
  | credit b _ hb' =>
    exact ⟨_, rfl, ⟨hb', hp, hm, hf, hn, hr, hs, hl, hc, ht⟩, fx _ rfl rfl rfl rfl rfl rfl rfl, id, .empty⟩
  | deploy b msg _ hb' =>
    exact ⟨_, rfl, ⟨hb', hp, hm, hf, hn, hr, hs, hl, hc, ht⟩, fx _ rfl rfl rfl rfl rfl rfl rfl, id,
      .send _ _ .empty⟩
  | accept msg _ =>
    exact ⟨_, rfl, ⟨hb, hp, hm, hf, hn, hr, hs, hl, hc, ht⟩, fx _ rfl rfl rfl rfl rfl rfl rfl, fun _ => rfl,
      .send _ _ .empty⟩
  | closeInactive msg _ =>
    exact ⟨d, rfl, ⟨hb, hp, hm, hf, hn, hr, hs, hl, hc, ht⟩, fx d rfl rfl rfl rfl rfl rfl rfl, id, .send _ _ .empty⟩
  | closeActive m1 m2 _ =>
    exact ⟨d, rfl, ⟨hb, hp, hm, hf, hn, hr, hs, hl, hc, ht⟩, fx d rfl rfl rfl rfl rfl rfl rfl, id,
      .send _ _ (.send _ _ .empty)⟩
  | withdraw msg _ _ =>
    exact ⟨d, rfl, ⟨hb, hp, hm, hf, hn, hr, hs, hl, hc, ht⟩, fx d rfl rfl rfl rfl rfl rfl rfl, id, .send _ _ .empty⟩
  | withdrawReserve msg _ _ =>
    exact ⟨d, rfl, ⟨hb, hp, hm, hf, hn, hr, hs, hl, hc, ht⟩, fx d rfl rfl rfl rfl rfl rfl rfl, id,
      .send _ _ (.reserve _ _ .empty)⟩
  | proof b n t msg ha hb' hn' ht' =>
    exact ⟨_, rfl, ⟨hb', hp, hm, hf, hn', hr, hs, ht', hc, ht⟩, fx _ rfl rfl rfl rfl rfl rfl rfl,
      fun _ => ha, .send _ _ .empty⟩

theorem post_of_not_committed (d : Data) (val : Int) (r : StepResult) (h : r.state.cstate.committed = false) :
    Post d val r := by
  intro h'; rw [h] at h'; cases h'

/-- A run after a dead step result (`TvmLean.Framed.Dead`) satisfies `Post`. -/
theorem post_of_dead {d : Data} {val : Int} {r : StepResult} (h : Framed.Dead r) (n : Nat) :
    Post d val (VmState.runCont execInstr n r) :=
  post_of_not_committed d val _ (h n)

/-- The state of `recv_internal` at bit 306 of its cell, after `32 LDU` and `64 LDU` read the
operation `op` and the query id `qid` of the body (`rest` the rest of the body), on the data `d`:
the stack `balance, msg_value, sender, op, qid, rest`, `c4` the data, no action, and any gas `g`,
loaded cells `lc` and libraries `ll`, steps and `c7`. -/
def atOps (d : Data) (bal val : Int) (sender : Slice) (op qid : Int) (rest : Slice) (c7 : Value) (g : GasLimits)
    (lc : Array (Array UInt8)) (ll : Array BitString) (libs : Array Cell) (mdd gv steps : Nat)
    (mll : Option Nat) : VmState :=
  { stack := (((((#[].push (.int (.num bal))).push (.int (.num val))).push (.slice sender)).push (.int (.num op))).push
      (.int (.num qid))).push (.slice rest),
    regs := { c0 := .quit 0, c1 := .quit 1, c2 := .excQuit,
              c3 := .ordinary (Slice.ofCell storageCode) (.quit 0) OrdCregs.empty OrdCdata.empty,
              c4 := d.encode, c5 := Cell.empty, c7 := #[].push c7 },
    cc := .plain { cell := storageCode.refs[0]!.refs[0]!.refs[0]!.refs[0]!, bitPos := 306, refPos := 2 },
    cp := 0, gas := g, chksgnCounter := 0, loadedCells := lc, libraries := libs, callStack := #[],
    cstate := CommittedState.empty, maxDataDepth := mdd, globalVersion := gv, steps := steps,
    maxLibraryLoads := mll, loadedLibraries := ll }

/-- The outcome of `add_to_balance(msg_value)`: the data written (`c4`, given by an equation) with
the new balance, no action. -/
theorem Outcome.credit_of (d : Data) (val : Int) (c4 : Cell) (h0 : ¬ (d.balance : Int) + val < 0)
    (h16 : ¬ 16 ≤ (natLenBits ((d.balance : Int) + val).toNat + 7) / 8)
    (hc : c4 = Data.encode { d with balance := ((d.balance : Int) + val).toNat }) :
    Outcome d val c4 Cell.empty :=
  hc ▸ Outcome.credit _ (by omega) (by unfold coinsLen; omega)

/-- The outcome of `deploy_storage_contract`: `add_to_balance(msg_value - 2 * fee::receipt_value)`
(the data written, `c4`, given by an equation), then the message `msg` (mode 0). -/
theorem Outcome.deploy_of (d : Data) (val : Int) (c4 msg : Cell) (h0 : ¬ (d.balance : Int) + (val - 40000000) < 0)
    (h16 : ¬ 16 ≤ (natLenBits ((d.balance : Int) + (val - 40000000)).toNat + 7) / 8)
    (hc : c4 = Data.encode { d with balance := ((d.balance : Int) + (val - 40000000)).toNat }) :
    Outcome d val c4 (OutAction.sendMsg 0 Cell.empty msg) :=
  hc ▸ Outcome.deploy _ msg (by omega) (by unfold coinsLen; omega)

/-- The outcome of `accept_storage_contract`, the data written given by an equation. -/
theorem Outcome.accept_of {d : Data} {val : Int} (c4 msg : Cell) (h : d.active = false)
    (hc : c4 = Data.encode { d with active := true }) :
    Outcome d val c4 (OutAction.sendMsg 0 Cell.empty msg) := hc ▸ Outcome.accept msg h

/-- The outcome of `withdraw` with a positive balance: the reserve `balance + fee::storage`. -/
theorem Outcome.withdrawReserve_of {d : Data} {val : Int} (msg : Cell) (h : d.active = true)
    (hb : 0 < (d.balance : Int)) :
    Outcome d val d.encode
      (OutAction.sendMsg 160 (OutAction.reserve 2 ((d.balance : Int) + 10000000).toNat Cell.empty) msg) := by
  have e : ((d.balance : Int) + 10000000).toNat = d.balance + 10000000 := by omega
  rw [e]
  exact Outcome.withdrawReserve msg h (by omega)

/-- The outcome of `withdraw` with no balance. -/
theorem Outcome.withdraw_of {d : Data} {val : Int} (msg : Cell) (h : d.active = true)
    (hb : ¬ 0 < (d.balance : Int)) : Outcome d val d.encode (OutAction.sendMsg 160 Cell.empty msg) :=
  Outcome.withdraw msg h (by omega)

/-- The outcome of `proof_storage`: the data written (`c4`, given by an equation) with the balance
`b`, the next byte to prove `n.toNat` and the time `t.toNat`, within the widths the stores check
(`STGRAMS`, `64 STU`, `32 STU`: the hypotheses as the run leaves them), then the message `msg`
(mode 64 + 2). -/
theorem Outcome.proof_of {d : Data} {val : Int} (c4 msg : Cell) (b : Nat) (n t : Int) (ha : d.active = true)
    (h16 : ¬ 16 ≤ (natLenBits b + 7) / 8) (hn : ¬ (n < 0 ∨ 18446744073709551616 ≤ n))
    (ht : ¬ (t < 0 ∨ 4294967296 ≤ t))
    (hc : c4 = Data.encode { d with balance := b, nextProof := n.toNat, lastProofTime := t.toNat }) :
    Outcome d val c4 (OutAction.sendMsg 66 Cell.empty msg) :=
  hc ▸ Outcome.proof _ _ _ msg ha (by unfold coinsLen; omega) (by omega) (by omega)

end Run

/-- Proves that a cell the contract builds (`Builder.finalize` of the builder of its stores) is the
data `Data.encode` of the fields stored: both written out as `Cell.mkOrdinary` of one bit string. -/
macro "storage_encode" : tactic => `(tactic| (
  simp only [Builder.finalize, Builder.storeBits, Builder.empty, Data.encode, Data.bits, coinsBits, coinsLen,
    Data.clientCell, Array.append_assoc, Array.empty_append, Array.append_empty, Int.toNat_natCast]))

open Lean Meta Elab Tactic in
/-- Closes a path ended by an exception the handler `excQuit` ends (`VmState.raiseDead`): the goal
`Post d val (VmState.runCont execInstr n (VmState.stepFinish execInstr S (st.raiseDead x)))`, or
the same run's `state.cstate.committed = false`. Fails at once on any other goal. -/
elab "storage_dead" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let isDead (r : Expr) : Bool :=
    r.isAppOfArity ``VmState.runCont 3 && (r.getArg! 2).isAppOfArity ``VmState.stepFinish 3 &&
      ((r.getArg! 2).getArg! 2).isAppOfArity ``VmState.raiseDead 2
  if t.isAppOfArity ``Run.Post 3 && isDead (t.getArg! 2) then
    evalTactic (← `(tactic|
      exact Run.post_of_dead (Framed.dead_stepFinish_raiseDead _ _ _ rfl rfl (by decide) rfl rfl) _))
  else if let some (_, lhs, _) := t.eq? then
    -- `(VmState.runCont ... ).state.cstate.committed = false`
    let some r := lhs.find? isDead | throwError "storage_dead: not an exception"
    let _ := r
    evalTactic (← `(tactic|
      exact (Framed.dead_stepFinish_raiseDead _ _ _ rfl rfl (by decide) rfl rfl) _))
  else throwError "storage_dead: not an exception"

open Lean Meta Elab Tactic in
/-- `storage_clear_gas`: of the hypotheses about the gas left (`GasLimits.gasRemaining`), keeps the
newest only (the gas left only decreases along a run of the contract, so the newest bound implies
the others); keeps the context of a run small for `omega`. -/
elab "storage_clear_gas" : tactic => withMainContext do
  let g ← getMainGoal
  let mut gasHyps : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun x => x.isAppOf ``GasLimits.gasRemaining).isSome then
      if ← isProp ty then gasHyps := gasHyps.push d.fvarId
  if gasHyps.size ≤ 1 then return
  replaceMainGoal [← g.tryClearMany gasHyps.pop]

namespace Exec

open Lean Meta

/-- `TvmLean.Exec.loopHoles` without the hole of `c5`: the gas, the loaded cells, the counters of
jumps and steps, and the payloads of the top `k` stack entries. -/
def loopHolesKeepC5 (S : Expr) (k : Nat) : MetaM (Array Expr × (Array Expr → Expr) × Nat) := do
  unless S.isAppOfArity ``VmState.mk 20 do throwError "vm_loop_keep_c5: the state is not written out"
  let fields := getStructureFields (← getEnv) ``VmState
  let idx (n : Name) : MetaM Nat := do
    let some i := fields.idxOf? n | throwError "vm_loop_keep_c5: no field {n}"
    return i
  let args := S.getAppArgs
  let plainNames := [`gas, `loadedCells, `chainJumps, `steps]
  let plain ← plainNames.mapM idx
  let mut vals : Array Expr := plain.toArray.map (args[·]!)
  let iStack ← idx `stack
  let mut stk := args[iStack]!
  let mut entries : Array (Expr → Expr) := #[]
  for _ in [0:k] do
    unless stk.isAppOfArity ``Array.push 3 do throwError "vm_loop_keep_c5: fewer than {k} stack entries written out"
    let some (p, f) := TvmLean.Exec.stackPayload? (stk.getArg! 2) | throwError "vm_loop_keep_c5: a top stack entry is not a slice, cell, builder or integer"
    vals := vals.push p
    entries := entries.push f
    stk := stk.getArg! 1
  let nPlain := plain.length
  let top := vals.extract nPlain vals.size
  vals := (vals.extract 0 nPlain) ++ top.reverse
  let es := entries.reverse
  let base := stk
  let fill (xs : Array Expr) : Expr := Id.run do
    let mut a := args
    for j in [0:nPlain] do a := a.set! plain[j]! xs[j]!
    let mut s := base
    for j in [0:es.size] do
      s := mkApp3 (mkConst ``Array.push [0]) (mkConst ``Value) s (es[j]! xs[nPlain + j]!)
    a := a.set! iStack s
    return mkAppN S.getAppFn a
  return (vals, fill, 2)

end Exec

open Lean Meta in
/-- `vm_loop_keep_c5 k`: `vm_loop k` (`TvmLean/Proofs/Exec/Tactic.lean`) whose invariant keeps the
action list `c5` of the loop head (a loop that sends nothing): the loop head but for the gas, the
loaded cells, the counters of jumps (fewer than `freeNestedContJump`) and steps, and the payloads of
the top `k` stack entries. -/
elab "vm_loop_keep_c5" k:(num)? : tactic => Lean.Elab.Tactic.withMainContext do
  let k := (k.map (·.getNat)).getD 1
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_loop_keep_c5: no run in the goal"
  let exec := r.getArg! 0
  let n := r.getArg! 1
  let S := r.getArg! 2
  let (vals, fill, iChain) ← Exec.loopHolesKeepC5 S k
  let tys ← vals.mapM fun v => (inferType v : MetaM Expr)
  let stTy := mkConst ``VmState
  let inv ← withLocalDeclD `st stTy fun st => do
    let decls := (List.range vals.size).toArray.map fun i =>
      (Name.mkSimple s!"x{i}", fun (_ : Array Expr) => pure tys[i]!)
    let body ← withLocalDeclsD decls fun xs => do
      let bound ← mkAppM ``LT.lt #[xs[iChain]!, mkConst ``freeNestedContJump]
      let mut e ← mkAppM ``And #[← mkEq st (fill xs), bound]
      for x in xs.reverse do
        e ← mkAppM ``Exists #[← mkLambdaFVars #[x] e]
      return e
    mkLambdaFVars #[st] body
  let motive ← withLocalDeclD `r (mkConst ``StepResult) fun rv => do
    mkLambdaFVars #[rv] ((← kabstract t r).instantiate1 rv)
  let hzTy ← withLocalDeclD `st stTy fun st => do
    mkForallFVars #[st] (← mkArrow (mkApp inv st).headBeta
      (mkApp motive (← mkAppM ``VmState.runWith #[exec, mkNatLit 0, st])).headBeta)
  let hz ← mkFreshExprSyntheticOpaqueMVar hzTy
  let hinv ← mkFreshExprMVar (mkApp inv S).headBeta
  TvmLean.Exec.solveInvExists hinv.mvarId!
  let rule ← mkAppOptM ``VmState.runWith_inv #[exec, inv, motive, hz]
  let .forallE _ hsTy _ _ ← whnf (← inferType rule) | throwError "vm_loop_keep_c5: the loop rule"
  let hs ← mkFreshExprSyntheticOpaqueMVar hsTy
  let pf ← mkAppOptM ``VmState.runWith_inv #[exec, inv, motive, hz, hs, n, S, hinv]
  unless ← isDefEq (← inferType pf) t do throwError "vm_loop_keep_c5: the goal is not a property of the run"
  g.assign pf
  let (_, gz) ← hz.mvarId!.intro `st
  let (h0, gz) ← gz.intro `hinv
  let gz ← TvmLean.Exec.destructInv gz h0
  let (_, gs) ← hs.mvarId!.intro `n
  let (_, gs) ← gs.intro `st
  let (h1, gs) ← gs.intro `hinv
  let (_, gs) ← gs.intro `ih
  let gs ← TvmLean.Exec.destructInv gs h1
  Lean.Elab.Tactic.replaceMainGoal [gz, gs]

open Lean Meta Elab Tactic in
/-- `vm_forget`: the gas, the loaded cells and the step counter of the run in the goal
(`VmState.runWith exec fuel S`, `S` written out) become variables (`generalize`), and the
hypotheses about what they were are cleared (`vm_clear_unused`). A goal about every gas, set of
loaded cells and step count implies the goal about those of the run, so this is sound; it keeps
the state of a long run small (each step adds to the gas and loaded cells terms otherwise). For
runs whose outcome does not depend on the gas: the run out of gas is a path of its own either
way. Fails if there is nothing to forget. -/
elab "vm_forget" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_forget: no run in the goal"
  let S := r.getArg! 2
  unless S.isAppOfArity ``VmState.mk 20 do throwError "vm_forget: the state is not written out"
  let fields := getStructureFields (← getEnv) ``VmState
  let mut idxs : Array Nat := #[]
  for n in [`gas, `loadedCells, `steps] do
    let some i := fields.idxOf? n | throwError "vm_forget: no field {n}"
    let e := S.getArg! i
    -- a variable already, or a closed value (the start of a run): nothing to forget
    unless e.isFVar || !e.hasFVar do idxs := idxs.push i
  if idxs.isEmpty then throwError "vm_forget: nothing to forget"
  let args := S.getAppArgs
  let tys ← idxs.mapM fun i => inferType args[i]!
  -- `∀ xs, t` with the fields of this state (only) replaced by `xs`, applied to their values
  let ty ← withLocalDeclsD (idxs.mapIdx fun k i => (fields[i]!, fun _ => pure tys[k]!)) fun xs => do
    let mut a := args
    for k in [0:idxs.size] do a := a.set! idxs[k]! xs[k]!
    let S' := mkAppN S.getAppFn a
    mkForallFVars xs (t.replace fun y => if y == S then some S' else none)
  let g' ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  g.assign (mkAppN g' (idxs.map (args[·]!)))
  let (_, g'') ← g'.mvarId!.introN idxs.size (idxs.toList.map (fields[·]!))
  replaceMainGoal [g'']
  evalTactic (← `(tactic| vm_clear_unused))

open Lean Meta Elab Tactic in
/-- `vm_forget_c7`: the parameter tuple of `c7` (`c7 = #[.tuple params]`) of the run in the goal
becomes a variable, when it is a term of the run (`RAND` writes its seed back): the run after it
reads `c7` as any tuple (`NOW`, `LTIME`), and the terms of the seed do not go along. Sound as
`vm_forget`. Fails if there is nothing to forget. -/
elab "vm_forget_c7" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_forget_c7: no run in the goal"
  let S := r.getArg! 2
  unless S.isAppOfArity ``VmState.mk 20 do throwError "vm_forget_c7: the state is not written out"
  let fields := getStructureFields (← getEnv) ``VmState
  let some iR := fields.idxOf? `regs | throwError "vm_forget_c7: no field regs"
  let regs := S.getArg! iR
  unless regs.isAppOfArity ``Regs.mk 7 do throwError "vm_forget_c7: the registers are not written out"
  let c7 := regs.getArg! 6
  unless c7.isAppOfArity ``Array.push 3 do throwError "vm_forget_c7: c7 is not #[.tuple params]"
  let v := c7.getArg! 2
  unless v.isAppOfArity ``Value.tuple 1 do throwError "vm_forget_c7: c7 is not #[.tuple params]"
  let P := v.appArg!
  if P.isFVar then throwError "vm_forget_c7: nothing to forget"
  let ty ← withLocalDeclD `params (← inferType P) fun x => do
    let c7' := mkApp3 c7.getAppFn (c7.getArg! 0) (c7.getArg! 1) (mkApp v.appFn! x)
    let regs' := mkAppN regs.getAppFn (regs.getAppArgs.set! 6 c7')
    let S' := mkAppN S.getAppFn (S.getAppArgs.set! iR regs')
    mkForallFVars #[x] (t.replace fun y => if y == S then some S' else none)
  let g' ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  g.assign (mkApp g' P)
  let (_, g'') ← g'.mvarId!.intro `params
  replaceMainGoal [g'']
  evalTactic (← `(tactic| vm_clear_unused))

open Lean Meta Elab Tactic in
/-- `vm_forget_stack`: the integers on the stack of the run in the goal that are terms of the run
(computed: not a variable, a literal or a field of a variable cast to `Int`), and the entries that
are a value the run has not looked at (not a constructor application), become variables. Sound as
`vm_forget`: for a run whose outcome does not depend on what they are, only on the checks the run
still makes of them (a store's range check, a `match` on a value). Fails if there is nothing to
forget. -/
elab "vm_forget_stack" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_forget_stack: no run in the goal"
  let S := r.getArg! 2
  unless S.isAppOfArity ``VmState.mk 20 do throwError "vm_forget_stack: the state is not written out"
  let fields := getStructureFields (← getEnv) ``VmState
  let some iS := fields.idxOf? `stack | throwError "vm_forget_stack: no field stack"
  -- the entries, top first
  let mut stk := S.getArg! iS
  let mut entries : Array Expr := #[]
  while stk.isAppOfArity ``Array.push 3 do
    entries := entries.push (stk.getArg! 2)
    stk := stk.getArg! 1
  let base := stk
  let simple (e : Expr) : Bool :=
    e.isFVar || e.isRawNatLit || (e.isAppOf ``OfNat.ofNat) || (e.isAppOf ``Neg.neg && (e.getArg! 2).isAppOf ``OfNat.ofNat) ||
      (e.isAppOfArity ``Nat.cast 3 && ((e.getArg! 2).isFVar || (e.getArg! 2).getAppFn.isProj ||
        ((e.getArg! 2).getAppFn.isConst && (e.getArg! 2).getAppNumArgs == 1 && (e.getArg! 2).appArg!.isFVar)))
  -- for each entry: `some (value, rebuild)` when it is forgotten
  let mut holes : Array (Expr × Expr × (Expr → Expr)) := #[]
  for v in entries do
    if v.isAppOfArity ``Value.int 1 && v.appArg!.isAppOfArity ``IntVal.num 1 then
      let x := v.appArg!.appArg!
      unless simple x do
        holes := holes.push (x, mkConst ``Int, fun y => mkApp v.appFn! (mkApp v.appArg!.appFn! y))
    else if !(v.getAppFn.isConst && (v.getAppFn.constName!.getPrefix == ``Value)) && !v.isFVar then
      holes := holes.push (v, mkConst ``Value, fun y => y)
  if holes.isEmpty then throwError "vm_forget_stack: nothing to forget"
  let ty ← withLocalDeclsD (holes.mapIdx fun k h => (Name.mkSimple s!"x{k}", fun _ => pure h.2.1)) fun xs => do
    let mut k := 0
    let mut newEntries : Array Expr := #[]
    for v in entries do
      if k < holes.size && holes[k]!.1 == (if v.isAppOfArity ``Value.int 1 && v.appArg!.isAppOfArity ``IntVal.num 1 then v.appArg!.appArg! else v) then
        newEntries := newEntries.push (holes[k]!.2.2 xs[k]!)
        k := k + 1
      else
        newEntries := newEntries.push v
    let mut s := base
    for v in newEntries.reverse do
      s := mkApp3 (mkConst ``Array.push [0]) (mkConst ``Value) s v
    let S' := mkAppN S.getAppFn (S.getAppArgs.set! iS s)
    mkForallFVars xs (t.replace fun y => if y == S then some S' else none)
  let g' ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  g.assign (mkAppN g' (holes.map (·.1)))
  let (_, g'') ← g'.mvarId!.introN holes.size
  replaceMainGoal [g'']
  evalTactic (← `(tactic| vm_clear_unused))

/-- Fails unless the run in the goal is at a loop head (`vm_not_at_loop_head` fails there). -/
macro "vm_at_loop_head" : tactic => `(tactic| (vm_has_run; fail_if_success vm_not_at_loop_head))

/-- The facts about the data `d` a run of the storage contract uses, from `hwf : d.WF`, as
hypotheses (found by `vm_run`'s discharger and `omega`). -/
macro "storage_setup " d:ident h:ident : tactic => `(tactic| (
  have ⟨hb, hp, hm, hf, hn, hr, hs, hl, hc, ht⟩ := $h
  have hbal := lt_of_coinsLen_lt hb
  have hrate := lt_of_coinsLen_lt hr
  have hes : (Data.encode $d).special = false := rfl
  have hcs : (Data.clientCell $d).special = false := rfl
  have hps := MsgAddr.Valid.size_le hp
  have hps2 := MsgAddr.Valid.two_le hp
  have hcls := MsgAddr.Valid.size_le hc
  have hflag := flagInt_bounds ($d).active
  have hbl : (natLenBits ($d).balance + 7) / 8 < 16 := hb
  have hrl : (natLenBits ($d).ratePerMbDay + 7) / 8 < 16 := hr
  have hlen20 : natLenBits 20000000 ≤ 25 := natLenBits_le_of_lt (by decide)))

/-- The end of a path that halts normally: the commit (`VmState.tryCommit`, which succeeds or
commits nothing), then `t` on the outcome of the committed data and actions. -/
macro "storage_commit " t:tacticSeq : tactic => `(tactic| (
  unfold Run.Post VmState.haltResult
  simp only [Int.reduceEq, or_false, or_true, if_true]
  unfold VmState.tryCommit
  split
  · simp only [if_true, StepResult.state_halt]
    intro _
    ($t)
  · simp only [Bool.false_eq_true, if_false, StepResult.state_halt, CommittedState.empty]
    intro h
    cases h))

/-- The end of a path that does not halt normally (out of gas, an exception, out of fuel). -/
macro "storage_no_commit" : tactic => `(tactic| (
  simp only [Run.Post, VmState.haltResult, VmState.runWith_zero, Excno.toInt, Int.reduceEq,
    Int.reduceNeg, or_self, or_false, false_or, if_false, ite_false, StepResult.state_halt,
    CommittedState.empty, Bool.false_eq_true, false_implies, not_false_eq_true]; done))

/-- `vm_step` with the lemmas of a run of the storage contract: those of `wallet_step`
(`TvmLean/Proofs/Contracts/Wallet3Run/Common.lean`), the return continuation of a call
(`VmState.retCont`), the reads of the data (`StorageRun/Read.lean`) and `args`. -/
syntax "storage_step" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| storage_step [$args,*]) => `(tactic| vm_step [Spec.dictJump, Slice.haveBits, Slice.advanceBits,
      ↓ VmState.stepWith_finish, VmState.stepFinish_continue, VmState.stepFinish_halt,
      VmState.stepFinish_ite, VmState.stepFinish_dite, GasLimits.changeLimit_infty_min,
      ↓ VmState.instrEnd_error_dead, callTo_eq, VmState.retCont, Spec.loadIntValue,
      Data.encode_bits_size, Data.encode_refs_size, Data.encode_ref0, Data.clientCell_bits_size,
      Data.clientCell_refs_size, Data.read_flag, Data.read_balanceLen, Data.read_balance,
      Data.skip_provider, Data.prefix_provider, Data.read_merkleHash, Data.read_fileSize,
      Data.read_nextProof, Data.read_rateLen, Data.read_rate, Data.read_maxSpan, Data.read_lastProofTime,
      Data.rest_afterBalance, Data.rest_afterProvider, Data.skip_client, Data.prefix_client,
      Data.read_torrentHash, readBits_ofCell_all, toCellRemaining_ofCell_mkOrdinary,
      bitsToIntSignedTwos_flag, twosBits_flag, twosBits_true, flag_fits257, storageFoldCode,
      Builder.canExtendBy, Builder.storeBits, Builder.empty, Array.size_append, natToBits_size,
      List.size_toArray, List.length_cons, List.length_nil, Array.empty_append, Array.append_empty,
      Array.append_assoc, Data.credit_cell, Data.encode_special, Data.clientCell_balance,
      VmState.consumeTupleGas, $args,*])

/-- `vm_step_simp` with the lemmas of `storage_step`. -/
syntax "storage_step_simp" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| storage_step_simp [$args,*]) => `(tactic| vm_step_simp [Spec.dictJump, Slice.haveBits,
      Slice.advanceBits, ↓ VmState.stepWith_finish, VmState.stepFinish_continue, VmState.stepFinish_halt,
      VmState.stepFinish_ite, VmState.stepFinish_dite, GasLimits.changeLimit_infty_min,
      ↓ VmState.instrEnd_error_dead, callTo_eq, VmState.retCont, Spec.loadIntValue,
      Data.encode_bits_size, Data.encode_refs_size, Data.encode_ref0, Data.clientCell_bits_size,
      Data.clientCell_refs_size, Data.read_flag, Data.read_balanceLen, Data.read_balance,
      Data.skip_provider, Data.prefix_provider, Data.read_merkleHash, Data.read_fileSize,
      Data.read_nextProof, Data.read_rateLen, Data.read_rate, Data.read_maxSpan, Data.read_lastProofTime,
      Data.rest_afterBalance, Data.rest_afterProvider, Data.skip_client, Data.prefix_client,
      Data.read_torrentHash, readBits_ofCell_all, toCellRemaining_ofCell_mkOrdinary,
      bitsToIntSignedTwos_flag, twosBits_flag, twosBits_true, flag_fits257, storageFoldCode,
      Builder.canExtendBy, Builder.storeBits, Builder.empty, Array.size_append, natToBits_size,
      List.size_toArray, List.length_cons, List.length_nil, Array.empty_append, Array.append_empty,
      Array.append_assoc, Data.credit_cell, Data.encode_special, Data.clientCell_balance,
      VmState.consumeTupleGas, $args,*])

/-- The run of the storage contract up to the code at bit `n` (`vm_not_at_pos`), with the lemmas of
`storage_step`. -/
syntax "storage_run_to " num " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| storage_run_to $n [$args,*]) => `(tactic| set_option maxRecDepth 100000 in repeat' (first
      | storage_dead
      | ((vm_split <;> try vm_prune_cheap) <;> try storage_clear_gas)
      | (vm_not_at_loop_head; vm_not_at_pos $n; (try vm_forget); storage_step [$args,*])
      | (vm_not_at_loop_head; vm_not_at_pos $n; vm_fuel <;> try simp only [VmState.runWith_zero, Excno.toInt])
      | (vm_has_run; storage_step_simp [$args,*])
      | vm_loop_close))

end TvmLean.Contracts.Storage

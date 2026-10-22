import TvmLean.Proofs.Tx.Phases

/-!
# The compute phase of a transaction

`Tx.computePhaseRun` (C++ `Transaction::prepare_compute_phase`) decides which code and data the
account runs with (its own, or those of the inbound message's `StateInit` when it activates an
uninitialized or frozen account), runs the VM (`Tx.runVm`: `computePhaseInit` of the code and the
data) and keeps what the run committed (`ComputeOutcome.ofHalt`). This module states that in terms a
contract proof uses:
* `VmStart code data st`: `st` is a VM state the compute phase starts the code `code` from, with the
  data `data`, whatever the rest (stack of an inbound message or of tick-tock, `c7`, gas, libraries);
* `vmFinal st`: the state the run of the compute phase ends in;
* `computePhaseRun_spec`: after the compute phase, an active account runs either its own code and
  data, or those of the message's `StateInit` (then activated); if the phase succeeded, the data and
  the action list it hands on are what a run from `VmStart` of that code and data committed.
-/

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-- The initial stack of the compute phase: `recv_internal` / `recv_external` (balance, value,
message, body, selector) or `run_ticktock` (balance, address, whether tock, `-2`). -/
def ComputeStack (stack : Stack) : Prop :=
  (∃ balance value msg body ext, stack = computePhaseStack balance value msg body ext) ∨
    ∃ balance addr tock : Int, stack = #[.int (.num balance), .int (.num addr), .int (.num tock), .int (.num (-2))]

/-- `st` is a state the compute phase starts the code `code` from with the data `data`
(`Tx.runVm`): `computePhaseInit` of the code as the VM loads it (`convertCodeCell`, the code itself
for an ordinary cell), with any stack of `ComputeStack`, any `c7`, gas limits, libraries and
limits. -/
def VmStart (code data : Cell) (st : VmState) : Prop :=
  ∃ (gv : Nat) (libs : Array Cell) (stack : Stack) (c7 : Value) (gl gm gc : Int) (mdd : Nat)
    (mll : Option Nat), ComputeStack stack ∧
    st = { computePhaseInit (convertCodeCell code gv libs) data stack #[c7] gl gm gc gv with
           libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll }

/-- The state the run of the compute phase from `st` ends in (`Tx.runVm`: at most the gas bound of
steps). -/
def vmFinal (st : VmState) : VmState :=
  match VmState.run (st.gas.stepBound + 16) st with
  | .halt _ stF => stF
  | .continue stF => stF

/-- The state the run of the compute phase ends in (`vmFinal`) is that of the run. -/
theorem vmFinal_eq (st : VmState) :
    vmFinal st = (VmState.runWith execInstr (st.gas.stepBound + 16) st).state := by
  unfold vmFinal
  rw [show VmState.runWith execInstr (st.gas.stepBound + 16) st = VmState.run (st.gas.stepBound + 16) st
    from rfl]
  cases VmState.run (st.gas.stepBound + 16) st <;> rfl

/-- An ordinary code cell is run as it is. -/
theorem convertCodeCell_ordinary (code : Cell) (gv : Nat) (libs : Array Cell) (h : code.special = false) :
    convertCodeCell code gv libs = code := by
  unfold convertCodeCell
  split
  · unfold libraryResolveLoads
    cases hb : libraryChainBound with
    | zero => simp [libraryChainBound] at hb
    | succ n => simp [libraryResolveLoadsAux, h]
  · simp [h]

/-- The run of `Tx.runVm`: from a state of `VmStart` of the code and the account's data. -/
theorem runVm_spec (t : Tx) (code : Cell) (gl gm gc : Nat) (seed : BitString) (sl : SizeLimits) :
    OKp (fun r : VmState × Int => ∃ st, VmStart code (t.newData.getD Cell.empty) st ∧ r.1 = vmFinal st)
      (t.runVm code gl gm gc seed sl) := by
  unfold OKp Tx.runVm
  extract_lets stack libs st0 st fuel
  refine ⟨st, ⟨t.gv, libs, stack, t.c7 seed, _, _, _, sl.maxVmDataDepth, sl.maxTransactionLibraryLoads, ?_, rfl⟩, ?_⟩
  · simp only [stack]
    split
    · exact Or.inr ⟨_, _, _, rfl⟩
    · exact Or.inl ⟨_, _, _, _, _, rfl⟩
  · simp only [vmFinal, fuel]
    cases VmState.run (st.gas.stepBound + 16) st <;> rfl

/-- After the compute phase, an active account runs its own code and data (it was active) or those
of the message's `StateInit` (it is activated with them). -/
def ActiveFrom (t₀ u : Tx) : Prop :=
  (t₀.accStatus = .active ∧ u.newCode = t₀.newCode ∧ u.newData = t₀.newData) ∨
    (u.useMsgState = true ∧ u.wasActivated = true ∧
      ∃ si, msgStateInit? t₀ = some si ∧ u.newCode = si.code ∧ u.newData = si.data)

/-- A successful compute phase: the VM ran the account's code `code` on its data from a state of
`VmStart`, the run committed, and the committed `c4` and `c5` are handed on. -/
def RunFacts (u : Tx) : Prop :=
  ∃ code st, u.newCode = some code ∧ VmStart code (u.newData.getD Cell.empty) st ∧
    (vmFinal st).cstate.committed = true ∧ (vmFinal st).gas.gasCredit = 0 ∧
    u.computePhase.newData = some (vmFinal st).cstate.c4 ∧ u.computePhase.actions = some (vmFinal st).cstate.c5

/-- What the compute phase leaves: see the module docstring. -/
def ComputeResult (t₀ u : Tx) : Prop :=
  t₀.Fixed u ∧ u.inMsgState = t₀.inMsgState ∧ (u.accStatus = .active → ActiveFrom t₀ u) ∧
    (u.computePhase.success = true → RunFacts u)

/-- Invariant of the compute phase before it looks at the message's `StateInit`. -/
@[reducible] def CpInv0 (t₀ u : Tx) : Prop :=
  t₀.Fixed u ∧ u.inMsgState = t₀.inMsgState ∧ t₀.SameState u ∧ u.computePhase.success = false

/-- Invariant of the compute phase once it looked at the message's `StateInit`. -/
@[reducible] def CpInv (t₀ u : Tx) : Prop :=
  t₀.Fixed u ∧ u.inMsgState = t₀.inMsgState ∧ u.wasActivated = false ∧ u.computePhase.success = false ∧
    u.accStatus = t₀.accStatus ∧
    ((u.useMsgState = false ∧ u.newCode = t₀.newCode ∧ u.newData = t₀.newData) ∨
      (u.useMsgState = true ∧ t₀.accStatus ≠ .active ∧
        ∃ si, msgStateInit? t₀ = some si ∧ u.newCode = si.code ∧ u.newData = si.data))

/-- The commit rule of the compute phase (`ComputeOutcome.ofHalt`): a run that committed, with no
gas credit left, hands on its `c4` and `c5`. -/
theorem ofHalt_spec (ec : Int) (stF : VmState) (data0 : Cell) :
    OKp (fun o : ComputeOutcome => (stF.gas.gasCredit == 0 && stF.cstate.committed) = true →
      o.c4 = stF.cstate.c4 ∧ o.c5 = stF.cstate.c5) (ComputeOutcome.ofHalt ec stF data0) := by
  unfold OKp ComputeOutcome.ofHalt
  intro h
  simp [h]

/-- The message's `StateInit` is used (`state_hash` matches) only for an account that is not active. -/
theorem stateHashOk_spec (t : Tx) :
    OKp (fun b : Bool => b = true → t.accStatus ≠ .active)
      (match t.inMsgState with
       | some c => t.accStatus == .uninit ||
           (!t.wasFrozen && t.accStatus == .frozen && t.account.stateHash == bytesToBits c.hashBytes)
       | none => false) := by
  unfold OKp
  split
  · intro h hc
    rw [hc] at h
    revert h
    simp only [show (AccStatus.active == AccStatus.uninit) = false from rfl,
      show (AccStatus.active == AccStatus.frozen) = false from rfl]
    simp
  · intro h; cases h

set_option maxHeartbeats 4000000 in
/-- **The compute phase** (`Transaction::prepare_compute_phase`): from a transaction that has not
used the message's `StateInit` yet, the result satisfies `ComputeResult`. -/
theorem computePhaseRun_spec (t₀ : Tx) (gas : GasPrices) (sl : SizeLimits) (seed : BitString)
    (h1 : t₀.useMsgState = false) (h2 : t₀.wasActivated = false) (h3 : t₀.computePhase.success = false) :
    OKe (OKo (ComputeResult t₀)) (t₀.computePhaseRun gas sl seed) := by
  unfold Tx.computePhaseRun
  tx_vcg keep_jps
  tx_jp_spec [CpInv0 t₀]
  all_goals tx_vcg_inv [CpInv t₀]
  all_goals try trivial
  all_goals tx_specs [payGas_spec, checkInMsgStateHash_spec, unpackMsgState_spec, runVm_spec, ofHalt_spec,
    stateHashOk_spec]
  all_goals tx_close [Tx.account, Tx.kind, Tx.cfg, Tx.gv, Tx.globalLibs, Tx.inMsgState, Tx.accStatus,
    Tx.newCode, Tx.newData, Tx.useMsgState, Tx.wasActivated, Tx.computePhase, ComputePhase.success,
    ComputePhase.newData, ComputePhase.actions]
    [ComputeResult, ActiveFrom, RunFacts, CpInv, CpInv0, Tx.Fixed, Tx.SameState, msgStateInit?]

/-! ## What the compute phase guarantees of the VM it starts

`VmStart` leaves the stack, `c7` and the gas limits free. `VmStart.Facts gas seed u st` is what the
compute phase of the transaction `u` (as it is after the phase) fixes of the state `st` it started
the VM from, and `computePhaseRun_facts` proves it for the state of every successful compute phase,
the state of `RunFacts`. -/

/-- The stack `Tx.runVm` starts the VM with, for the balance `bal` (`Transaction::prepare_vm_stack`,
transaction.cpp:1460-1484): tick-tock gets the balance, the address (its 256 bits signed), -1 for
tock or 0 for tick, and -2; an ordinary transaction `computePhaseStack` of the balance, the
message's remaining value, the message, its body and the selector (-1 for an external message, 0
for an internal one). -/
def Tx.vmStack (t : Tx) (bal : Nat) : Stack :=
  if t.kind != .ord then
    #[.int (.num (Int.ofNat bal)), .int (.num (bitsToIntSignedTwos t.account.addr)),
      .int (.num (if t.kind == .tock then -1 else 0)), .int (.num (-2))]
  else
    computePhaseStack (Int.ofNat bal) (Int.ofNat t.msgBalanceRemaining) t.inMsg t.inMsgBody t.inMsgExtern

/-- The balance the compute phase of `u` ran the VM with: the balance after the phase and its gas
fees. -/
def Tx.vmBalance (u : Tx) : Nat := u.balance + u.computePhase.gasFees

/-- The gas limit, maximum and credit (`td::uint64`) the VM of the compute phase of `u` gets: those
of `compute_gas_limits`, or for a precompiled code the configuration's gas limit (transaction.cpp:
1938, 1955-1956). -/
def Tx.vmGas (u : Tx) (gas : GasPrices) : Nat × Nat × Nat :=
  match u.computePhase.precompiledGasUsage with
  | none => (u.computePhase.gasLimit, u.computePhase.gasMax, u.computePhase.gasCredit)
  | some _ =>
      let limit := if u.account.isSpecial then gas.specialGasLimit else gas.gasLimit
      (limit, limit, if u.computePhase.gasCredit ≠ 0 then limit else 0)

/-- The gas limits of the compute phase of `u` as `compute_gas_limits` sets them for the balance
`bal`, with `buy n` the gas `n` nanotons buy (transaction.cpp:1427-1450): the maximum is the gas the
balance buys (a special account's limit), the limit the gas the message's value buys, at most the
maximum (tick-tock and, from version 5, a special account: the maximum), the credit only for an
external message. -/
def GasLims (gas : GasPrices) (buy : Nat → Nat) (u : Tx) (bal : Nat) : Prop :=
  u.computePhase.gasMax = (if u.account.isSpecial then gas.specialGasLimit else buy bal) ∧
    u.computePhase.gasLimit = (if u.kind != .ord || (u.account.isSpecial && u.gv ≥ 5) then u.computePhase.gasMax
      else Nat.min (buy u.msgBalanceRemaining) u.computePhase.gasMax) ∧
    u.computePhase.gasCredit = (if u.inMsgExtern then Nat.min gas.gasCredit u.computePhase.gasMax else 0)

/-- What the compute phase of `u` fixes of the state `st` it started the VM from (`Tx.runVm`): the
stack of the message or of tick-tock for the balance of the phase, `c7` of `prepare_vm_c7` for that
balance, the gas limits of `compute_gas_limits` as the VM's `long long`, the global version. -/
structure VmStart.Facts (gas : GasPrices) (seed : BitString) (u : Tx) (st : VmState) : Prop where
  stack : st.stack = u.vmStack u.vmBalance
  c7 : st.regs.c7 = #[({ u with balance := u.vmBalance }).c7 seed]
  gasLimits : st.gas = GasLimits.ofLimits (int64OfUInt64 (u.vmGas gas).1) (int64OfUInt64 (u.vmGas gas).2.1)
    (int64OfUInt64 (u.vmGas gas).2.2)
  limits : GasLims gas (u.gasBoughtFor gas) u u.vmBalance
  gv : st.globalVersion = u.gv

theorem int64OfUInt64_lt (n : Nat) : int64OfUInt64 n < 2 ^ 63 := by
  simp only [int64OfUInt64, Nat.reducePow, Int.reducePow, Int.ofNat_eq_coe]
  split <;> omega

theorem int64OfUInt64_ge (n : Nat) : -2 ^ 63 ≤ int64OfUInt64 n := by
  simp only [int64OfUInt64, Nat.reducePow, Int.reducePow, Int.ofNat_eq_coe]
  split <;> omega

theorem int64OfUInt64_of_lt {n : Nat} (h : n < 2 ^ 63) : int64OfUInt64 n = n := by
  simp only [int64OfUInt64, Nat.reducePow] at h ⊢
  rw [if_pos (by omega), Nat.mod_eq_of_lt (by omega)]
  rfl

/-- The parameter tuple of `Tx.c7` has at most 18 entries. -/
theorem Tx.c7_params_size (t : Tx) (seed : BitString) : ∃ params : Array Value,
    t.c7 seed = .tuple params ∧ params.size ≤ 18 := by
  unfold Tx.c7
  refine ⟨_, rfl, ?_⟩
  simp only [Array.size_append]
  by_cases h4 : 4 ≤ t.gv <;> by_cases h6 : 6 ≤ t.gv <;> by_cases h11 : 11 ≤ t.gv <;> simp [h4, h6, h11]

namespace VmStart.Facts

variable {gas : GasPrices} {seed : BitString} {u : Tx} {st : VmState}

/-- An ordinary transaction: the stack of the message, with the selector -1 (external) or 0. -/
theorem stack_ord (h : Facts gas seed u st) (hk : u.kind = .ord) :
    st.stack = computePhaseStack (Int.ofNat u.vmBalance) (Int.ofNat u.msgBalanceRemaining) u.inMsg u.inMsgBody
      u.inMsgExtern := by
  rw [h.stack, Tx.vmStack, hk]
  rfl

/-- Tick-tock: the balance, the address (signed), -1 for tock or 0 for tick, and -2. -/
theorem stack_tickTock (h : Facts gas seed u st) (hk : u.kind ≠ .ord) :
    st.stack = #[.int (.num (Int.ofNat u.vmBalance)), .int (.num (bitsToIntSignedTwos u.account.addr)),
      .int (.num (if u.kind == .tock then -1 else 0)), .int (.num (-2))] := by
  rw [h.stack, Tx.vmStack]
  have : (u.kind != .ord) = true := by
    revert hk
    cases u.kind <;> intro hk <;> first | rfl | exact absurd rfl hk
  rw [if_pos this]

/-- `c7` is one tuple whose first ten entries are `SmartContractInfo` (`prepare_vm_c7`,
transaction.cpp:1520-1576): the tag, 0, 0, `NOW`, the logical times of the block and of the
transaction, the random seed, the balance of the phase, the address and the configuration. -/
theorem c7_params (h : Facts gas seed u st) : ∃ rest : Array Value,
    st.regs.c7 = #[.tuple (#[.int (.num 0x076ef1ea), .int (.num 0), .int (.num 0), .int (.num (Int.ofNat u.now)),
      .int (.num (Int.ofNat u.account.blockLt)), .int (.num (Int.ofNat u.startLt)),
      .int (.num (Int.ofNat (u.randSeed seed))), balanceTuple u.vmBalance u.balanceExtra,
      .slice (Slice.ofCell u.myAddr), .cell u.cfg.root] ++ rest)] := by
  rw [h.c7]
  exact ⟨_, by simp only [Tx.c7, Array.append_assoc]; rfl⟩

/-- `NOW` (`c7[0][3]`) is the time of the transaction. -/
theorem now (h : Facts gas seed u st) : ∃ params : Array Value,
    st.regs.c7 = #[.tuple params] ∧ params[3]? = some (.int (.num (Int.ofNat u.now))) := by
  obtain ⟨rest, hr⟩ := h.c7_params
  exact ⟨_, hr, by rw [Array.getElem?_append_left (by simp)]; rfl⟩

/-- The parameter tuple `c7[0]` has at most 18 entries (`prepare_vm_c7`, transaction.cpp:1520-1576:
ten, four more from version 4, three from version 6, one from version 11): the readers of `c7[0]`,
which refuse a tuple of more than 255 entries (C++ `get_param`, tonops.cpp:121-128), take it. -/
theorem params_size (h : Facts gas seed u st) : ∃ params : Array Value,
    st.regs.c7 = #[.tuple params] ∧ params.size ≤ 18 := by
  obtain ⟨params, hp, hs⟩ := Tx.c7_params_size ({ u with balance := u.vmBalance }) seed
  exact ⟨params, by rw [h.c7, hp], hs⟩

/-- The gas limit and the credit are at most the maximum (`td::uint64`). -/
theorem vmGas_le (h : Facts gas seed u st) :
    (u.vmGas gas).1 ≤ (u.vmGas gas).2.1 ∧ (u.vmGas gas).2.2 ≤ (u.vmGas gas).2.1 := by
  obtain ⟨_, hl, hc⟩ := h.limits
  unfold Tx.vmGas
  split
  · refine ⟨?_, ?_⟩
    · rw [hl]; split
      · exact Nat.le_refl _
      · exact Nat.min_le_right _ _
    · rw [hc]; split
      · exact Nat.min_le_right _ _
      · exact Nat.zero_le _
  · dsimp only
    refine ⟨Nat.le_refl _, ?_⟩
    by_cases hc : u.computePhase.gasCredit ≠ 0 <;> simp [hc]

/-- Without an external message the VM starts without gas credit. -/
theorem gasCredit_eq_zero (h : Facts gas seed u st) (he : u.inMsgExtern = false) : st.gas.gasCredit = 0 := by
  obtain ⟨_, _, hc⟩ := h.limits
  rw [h.gasLimits]
  simp only [GasLimits.ofLimits, Tx.vmGas]
  rw [he] at hc
  split <;> simp [hc, int64OfUInt64]

/-- The VM's gas limit, maximum and credit are `long long`: below 2^63. -/
theorem gas_lt (h : Facts gas seed u st) :
    st.gas.gasLimit < 2 ^ 63 ∧ st.gas.gasMax < 2 ^ 63 ∧ st.gas.gasCredit < 2 ^ 63 := by
  rw [h.gasLimits]
  exact ⟨int64OfUInt64_lt _, int64OfUInt64_lt _, int64OfUInt64_lt _⟩

/-- With a gas maximum below 2^63 (a configuration whose gas limits are), the VM gets the limits of
the compute phase: 0 ≤ limit ≤ maximum and 0 ≤ credit ≤ maximum. -/
theorem gas_of_lt (h : Facts gas seed u st) (hm : (u.vmGas gas).2.1 < 2 ^ 63) :
    st.gas.gasLimit = (u.vmGas gas).1 ∧ st.gas.gasMax = (u.vmGas gas).2.1 ∧ st.gas.gasCredit = (u.vmGas gas).2.2 ∧
      0 ≤ st.gas.gasLimit ∧ st.gas.gasLimit ≤ st.gas.gasMax ∧ 0 ≤ st.gas.gasCredit ∧
      st.gas.gasCredit ≤ st.gas.gasMax := by
  obtain ⟨h1, h2⟩ := h.vmGas_le
  rw [h.gasLimits]
  simp only [GasLimits.ofLimits]
  rw [int64OfUInt64_of_lt (n := (u.vmGas gas).1) (by omega), int64OfUInt64_of_lt hm,
    int64OfUInt64_of_lt (n := (u.vmGas gas).2.2) (by omega)]
  omega

end VmStart.Facts

/-- The run of `Tx.runVm`: from a state of `VmStart` with the stack of `Tx.vmStack`, `c7` of `Tx.c7`,
the gas limits as `long long` and the global version of `t`. -/
theorem runVm_facts (t : Tx) (code : Cell) (gl gm gc : Nat) (seed : BitString) (sl : SizeLimits) :
    OKp (fun r : VmState × Int => ∃ st, VmStart code (t.newData.getD Cell.empty) st ∧ r.1 = vmFinal st ∧
      st.stack = t.vmStack t.balance ∧ st.regs.c7 = #[t.c7 seed] ∧
      st.gas = GasLimits.ofLimits (int64OfUInt64 gl) (int64OfUInt64 gm) (int64OfUInt64 gc) ∧
      st.globalVersion = t.gv)
      (t.runVm code gl gm gc seed sl) := by
  unfold OKp Tx.runVm
  extract_lets stack libs st0 st fuel
  refine ⟨st, ⟨t.gv, libs, stack, t.c7 seed, _, _, _, sl.maxVmDataDepth, sl.maxTransactionLibraryLoads, ?_, rfl⟩,
    ?_, rfl, rfl, rfl, rfl⟩
  · simp only [stack]
    split
    · exact Or.inr ⟨_, _, _, rfl⟩
    · exact Or.inl ⟨_, _, _, _, _, rfl⟩
  · simp only [vmFinal, fuel]
    cases VmState.run (st.gas.stepBound + 16) st <;> rfl

/-- `unpack_msg_state` keeps the balance, the time and the message's value and kind. -/
theorem unpackMsgState_keep (t : Tx) (sl : SizeLimits) (libOnly : Bool) :
    OKp (fun r : Tx × Bool => r.1.balance = t.balance ∧ r.1.now = t.now ∧
        r.1.msgBalanceRemaining = t.msgBalanceRemaining ∧ r.1.inMsgExtern = t.inMsgExtern)
      (t.unpackMsgState sl libOnly) := by
  unfold Tx.unpackMsgState
  tx_vcg
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- `check_in_msg_state_hash` keeps the balance, the time and the message's value and kind. -/
theorem checkInMsgStateHash_keep (t : Tx) :
    OKo (fun u => u.balance = t.balance ∧ u.now = t.now ∧ u.msgBalanceRemaining = t.msgBalanceRemaining ∧
        u.inMsgExtern = t.inMsgExtern) t.checkInMsgStateHash := by
  unfold Tx.checkInMsgStateHash
  tx_vcg
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- The payment for the gas takes the fees (at most the balance) off the balance and records them
(a special account's are 0); a message not accepted pays nothing and keeps its gas fees. -/
theorem payGas_pays (t : Tx) (gas : GasPrices) (cp : ComputePhase) :
    OKe (fun r : Tx × ComputePhase => ∃ fees g, fees ≤ t.balance ∧
      r = ({ t with totalFees := t.totalFees + fees, balance := t.balance - fees }, { cp with gasFees := g }) ∧
      (g = fees ∨ (g = cp.gasFees ∧ fees = 0))) (t.payGas gas cp) := by
  unfold Tx.payGas
  tx_vcg
  all_goals first
    | exact ⟨0, cp.gasFees, Nat.zero_le _, rfl, Or.inr ⟨rfl, rfl⟩⟩
    | exact ⟨0, 0, Nat.zero_le _, rfl, Or.inl rfl⟩
    | exact ⟨_, _, by omega, rfl, Or.inl rfl⟩

/-- What the VM of the compute phase reads of the transaction, but the balance: the same in `t` and
`u`. -/
@[reducible] def Tx.SameVm (t u : Tx) : Prop :=
  u.kind = t.kind ∧ u.account = t.account ∧ u.gv = t.gv ∧ u.now = t.now ∧ u.startLt = t.startLt ∧ u.cfg = t.cfg ∧
    u.balanceExtra = t.balanceExtra ∧ u.myAddr = t.myAddr ∧ u.newCode = t.newCode ∧
    u.msgBalanceRemaining = t.msgBalanceRemaining ∧ u.msgExtra = t.msgExtra ∧ u.storagePhase = t.storagePhase ∧
    u.duePayment = t.duePayment ∧ u.inMsg = t.inMsg ∧ u.inMsgInfo = t.inMsgInfo ∧ u.inMsgBody = t.inMsgBody ∧
    u.inMsgExtern = t.inMsgExtern ∧ u.inMsgState = t.inMsgState ∧
    u.computePhase.gasMax = t.computePhase.gasMax ∧ u.computePhase.gasLimit = t.computePhase.gasLimit ∧
    u.computePhase.gasCredit = t.computePhase.gasCredit ∧
    u.computePhase.precompiledGasUsage = t.computePhase.precompiledGasUsage

theorem Tx.gasBoughtFor_congr {t u : Tx} (ha : u.account = t.account) (hv : u.gv = t.gv) (hn : u.now = t.now) :
    u.gasBoughtFor = t.gasBoughtFor := by
  unfold Tx.gasBoughtFor
  rw [ha, hv, hn]

/-- The facts of a state the VM of `t` starts from, for the transaction `u` that agrees with `t` on
what the VM reads (`Tx.SameVm`) and ran with the balance of `t`, the gas limits of `t` those of
`compute_gas_limits` for the account, version and time of `t₀`. -/
theorem VmStart.Facts.intro {gas : GasPrices} {seed : BitString} (t₀ : Tx) {t u : Tx} {st : VmState}
    {gl gm gc : Nat} (hst : st.stack = t.vmStack t.balance) (hc7 : st.regs.c7 = #[t.c7 seed])
    (hgas : st.gas = GasLimits.ofLimits (int64OfUInt64 gl) (int64OfUInt64 gm) (int64OfUInt64 gc))
    (hvg : t.vmGas gas = (gl, gm, gc)) (hgv : st.globalVersion = t.gv)
    (hlim : GasLims gas (t₀.gasBoughtFor gas) t t.balance) (ha0 : t.account = t₀.account) (hv0 : t.gv = t₀.gv)
    (hn0 : t.now = t₀.now) (hbal : u.vmBalance = t.balance) (hs : t.SameVm u) : VmStart.Facts gas seed u st := by
  obtain ⟨hk, ha, hv, hn, hsl, hcf, hbe, hma, hnc, hmb, hme, hsp, hdp, him, hii, hib, hie, hims, hgm, hgl, hgc, hpg⟩ := hs
  have hb : u.gasBoughtFor = t₀.gasBoughtFor :=
    Tx.gasBoughtFor_congr (ha.trans ha0) (hv.trans hv0) (hn.trans hn0)
  obtain ⟨hl1, hl2, hl3⟩ := hlim
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hst, hbal]
    simp only [Tx.vmStack, hk, ha, hmb, him, hib, hie]
  · rw [hc7]
    simp only [Tx.c7, Tx.inMsgParams, Tx.randSeed, hk, ha, hv, hn, hsl, hcf, hbe, hma, hnc, hmb, hme, hsp, hdp, hii,
      hims, hpg, hbal]
  · have e : u.vmGas gas = t.vmGas gas := by simp only [Tx.vmGas, ha, hgm, hgl, hgc, hpg]
    rw [hgas, e, hvg]
  · refine ⟨?_, ?_, ?_⟩
    · rw [hgm, hl1, ha, hb, hbal]
    · rw [hgl, hl2, hk, ha, hv, hb, hmb, hgm]
    · rw [hgc, hl3, hie, hgm]
  · rw [hgv, hv]

/-- Invariant of the compute phase before it sets the gas limits (`computePhaseRun_facts`). -/
@[reducible] def CpInvF0 (t₀ u : Tx) : Prop :=
  u.computePhase.success = false ∧ u.account = t₀.account ∧ u.gv = t₀.gv ∧ u.now = t₀.now

theorem CpInvF0.buy {t₀ u : Tx} (h : CpInvF0 t₀ u) : u.gasBoughtFor = t₀.gasBoughtFor :=
  Tx.gasBoughtFor_congr h.2.1 h.2.2.1 h.2.2.2

/-- Invariant of the compute phase once it set the gas limits (`computePhaseRun_facts`). -/
@[reducible] def CpInvF (gas : GasPrices) (t₀ u : Tx) : Prop :=
  GasLims gas (t₀.gasBoughtFor gas) u u.balance ∧ u.computePhase.gasFees = 0 ∧ u.computePhase.success = false ∧
    u.account = t₀.account ∧ u.gv = t₀.gv ∧ u.now = t₀.now

/-- A successful compute phase (`RunFacts`) with the facts of the state it started the VM from. -/
def RunFactsF (gas : GasPrices) (seed : BitString) (u : Tx) : Prop :=
  ∃ code st, u.newCode = some code ∧ VmStart code (u.newData.getD Cell.empty) st ∧
    (vmFinal st).cstate.committed = true ∧ (vmFinal st).gas.gasCredit = 0 ∧
    u.computePhase.newData = some (vmFinal st).cstate.c4 ∧ u.computePhase.actions = some (vmFinal st).cstate.c5 ∧
    VmStart.Facts gas seed u st

theorem RunFactsF.runFacts {gas : GasPrices} {seed : BitString} {u : Tx} (h : RunFactsF gas seed u) :
    RunFacts u := by
  obtain ⟨code, st, h1, h2, h3, h4, h5, h6, _⟩ := h
  exact ⟨code, st, h1, h2, h3, h4, h5, h6⟩

set_option maxHeartbeats 4000000 in
/-- **The facts of the compute phase**: after a successful compute phase `u`, the VM ran from a state
of `VmStart` with `VmStart.Facts` (and as `RunFacts` says). -/
theorem computePhaseRun_facts (t₀ : Tx) (gas : GasPrices) (sl : SizeLimits) (seed : BitString)
    (h3 : t₀.computePhase.success = false) :
    OKe (OKo (fun u => u.computePhase.success = true → RunFactsF gas seed u)) (t₀.computePhaseRun gas sl seed) := by
  unfold Tx.computePhaseRun
  tx_vcg keep_jps
  tx_jp_spec [CpInvF0 t₀]
  all_goals tx_vcg_inv [CpInvF gas t₀]
  all_goals try trivial
  all_goals tx_specs [payGas_pays, checkInMsgStateHash_spec, checkInMsgStateHash_keep, unpackMsgState_spec,
    unpackMsgState_keep, runVm_facts, ofHalt_spec]
  all_goals try (tx_close [Tx.account, Tx.kind, Tx.gv, Tx.now, Tx.balance, Tx.msgBalanceRemaining, Tx.inMsgExtern,
    Tx.computePhase, ComputePhase.success, ComputePhase.gasMax, ComputePhase.gasLimit, ComputePhase.gasCredit,
    ComputePhase.gasFees] [CpInvF, CpInvF0, GasLims, RunFactsF])
  all_goals try (have := CpInvF0.buy ‹CpInvF0 t₀ _›
                 tx_prep [Tx.account, Tx.kind, Tx.gv, Tx.now, Tx.balance, Tx.msgBalanceRemaining, Tx.inMsgExtern,
                   Tx.computePhase, ComputePhase.success, ComputePhase.gasMax, ComputePhase.gasLimit,
                   ComputePhase.gasCredit, ComputePhase.gasFees] [CpInvF, CpInvF0, GasLims, RunFactsF]
                 (try dsimp only at *)
                 simp_all
                 done)
  all_goals
    intro hs
    tx_destruct
    all_goals
      subst_vars
      refine ⟨_, _, ?_, (by assumption), ?_, ?_, ?_, ?_, VmStart.Facts.intro t₀ (by assumption) (by assumption)
        (by assumption) (by rfl) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) ?_
        (by repeat' constructor)⟩
  all_goals try assumption
  all_goals (try simp (config := { zetaDelta := true }) only [] at *)
  all_goals try grind
  -- the balance the VM ran with: the payment took `fees` off it and recorded `fees` (or nothing)
  all_goals simp only [Tx.vmBalance] at *; omega

end TvmLean.Tx

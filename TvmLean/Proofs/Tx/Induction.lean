import TvmLean.Proofs.Tx.Effect
import TvmLean.Proofs.Tx.ReadBack

/-!
# Induction over the transactions of an account

An invariant `Inv code data` of the code and the data of an active account (`Good Inv sa`: of every
active account the shard account `sa` reads as) holds of every shard account reachable by
transactions (`Reachable`) if (`Reachable.good`)
* it holds of the start (`Good Inv sa` for `Start sa`),
* it holds of the code and data of every `StateInit` the account may be deployed with (`Init`), and
* every committed run of the compute phase preserves it (`RunPreserves`): from code `code` and data
  `data` with `Inv (some code) data`, a run that commits the data `c4` and the action list `c5`
  (`Ran`) leaves `Inv code' (some c4)` for the code `code'` the action phase installs (`NewCode`:
  `code` if `c5` has no `SETCODE`, else the code of one of its `SETCODE` actions).
The obligations about a run are facts about a committed `c4` and the action list `c5`, what a
symbolic run of the code gives; the rest (storage, credit and bounce phases, rollback, the action
phase, deployment, the account written and read back) is proved here once and for all
(`Effect`, `computeState_readBack`). `Reachable.good_split` states the obligation about a run in
two parts (no `SETCODE`: the data; a `SETCODE`: the new code with the data),
`Reachable.code_fixed` the case of code that never changes, `Reachable.spec` the case of code that
changes only to code satisfying the same specification.

A step (`Step`) is a transaction the model runs (`emulate`, `emulateTickTock`) under the
configuration `configRoot`, with any inbound message, time, logical time, random seed and
libraries; the next shard account holds the account it writes, with any hash (256 bits) and logical
time of the last transaction (`shardAccountCell`). Two conditions restrict the steps:
* the account written fits its fields (`Tx.Fits`): C++ `compute_state` fails otherwise, the model
  writes it anyway;
* the account takes its code and data from the message's `StateInit` only if `Init` holds of it
  (`DeployOK`). The model takes them only from a `StateInit` whose hash matches the address (an
  uninitialized account) or the frozen state hash; that only the contract's own `StateInit` can be
  deployed is a property of the hash, which a theorem cannot assume (hashes collide), so the
  statement leaves `Init` to the user: `Init c := Inv` of the code and data of `c` makes the
  obligation trivial.
-/

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-- `Inv` holds of the code and the data of every active account the shard account `sa` reads as
(at any address). -/
def Good (Inv : Option Cell → Option Cell → Prop) (sa : Cell) : Prop :=
  ∀ wc addr sp a, Account.unpack sa wc addr sp = some a → a.status = .active → Inv a.code a.data

/-- The account takes its code and data from the message's `StateInit` (`useMsgState`) only if `Init`
holds of its cell. -/
def DeployOK (Init : Cell → Prop) (tf : Tx) : Prop :=
  ∀ c, tf.inMsgState = some c → tf.useMsgState = true → Init c

/-- Every committed run of the compute phase preserves `Inv`: see the module docstring. -/
def RunPreserves (Inv : Option Cell → Option Cell → Prop) : Prop :=
  ∀ code data c4 c5, Inv (some code) data → Ran code data c4 c5 →
    ∀ code', NewCode c5 (some code) code' → Inv code' (some c4)

/-- One transaction of the account in the shard account `sa` under the configuration `configRoot`:
ordinary (`emulate`) or tick-tock (`emulateTickTock`), the account written fitting its fields, the
code and data taken from the message's `StateInit` only if `Init` holds of it. The next shard
account holds the account written (`acc`, the account `Tx.computeState` writes from the state `tf`
the transaction ends in) with any hash and logical time of the last transaction. -/
inductive Step (configRoot : Cell) (Init : Cell → Prop) : Cell → Cell → Prop
  | ord {sa inMsg : Cell} {now lt : Nat} {seed : BitString} {libs : Option Cell} {tx acc : Cell} {tf : Tx}
      {sl : SizeLimits} (hash : BitString) (lt' : Nat) :
      emulate configRoot sa inMsg now lt seed libs = .ok tx acc →
      EmulateFinal configRoot sa inMsg now lt seed libs tf sl → acc = (tf.computeState sl).2 →
      tf.Fits sl → DeployOK Init tf → hash.size = 256 →
      Step configRoot Init sa (shardAccountCell acc hash lt')
  | tickTock {sa : Cell} {isTock : Bool} {now lt : Nat} {seed : BitString} {libs : Option Cell} {tx acc : Cell}
      {tf : Tx} {sl : SizeLimits} (hash : BitString) (lt' : Nat) :
      emulateTickTock configRoot sa isTock now lt seed libs = .ok tx acc →
      TickTockFinal configRoot sa isTock now lt seed libs tf sl → acc = (tf.computeState sl).2 →
      tf.Fits sl → hash.size = 256 →
      Step configRoot Init sa (shardAccountCell acc hash lt')

/-- The shard accounts reachable by transactions (`Step`) from those of `Start`. -/
inductive Reachable (configRoot : Cell) (Init : Cell → Prop) (Start : Cell → Prop) : Cell → Prop
  | start {sa : Cell} : Start sa → Reachable configRoot Init Start sa
  | step {sa sa' : Cell} : Reachable configRoot Init Start sa → Step configRoot Init sa sa' →
      Reachable configRoot Init Start sa'

/-- Every ordinary transaction (`emulate`) the model returns ends in a state `tf` of `EmulateFinal`
from which it writes its account: `Step.ord` applies to it if the account fits and the deployment is
allowed. -/
theorem emulate_step (configRoot sa inMsg : Cell) (now lt : Nat) (seed : BitString) (libs : Option Cell)
    {tx acc : Cell} (h : emulate configRoot sa inMsg now lt seed libs = .ok tx acc) :
    ∃ tf sl, EmulateFinal configRoot sa inMsg now lt seed libs tf sl ∧ acc = (tf.computeState sl).2 := by
  have := emulate_final configRoot sa inMsg now lt seed libs
  unfold OKp at this
  rw [h] at this
  obtain ⟨tf, sl, hacc, hf⟩ := this
  exact ⟨tf, sl, hf, hacc⟩

/-- The same for a tick-tock transaction (`emulateTickTock`). -/
theorem emulateTickTock_step (configRoot sa : Cell) (isTock : Bool) (now lt : Nat) (seed : BitString)
    (libs : Option Cell) {tx acc : Cell} (h : emulateTickTock configRoot sa isTock now lt seed libs = .ok tx acc) :
    ∃ tf sl, TickTockFinal configRoot sa isTock now lt seed libs tf sl ∧ acc = (tf.computeState sl).2 := by
  have := emulateTickTock_final configRoot sa isTock now lt seed libs
  unfold OKp at this
  rw [h] at this
  obtain ⟨tf, sl, hacc, hf⟩ := this
  exact ⟨tf, sl, hf, hacc⟩

/-- A tick-tock transaction has no inbound message, hence no `StateInit` to deploy. -/
theorem TickTockFinal.inMsgState {configRoot sa : Cell} {isTock : Bool} {now lt : Nat} {seed : BitString}
    {libs : Option Cell} {tf : Tx} {sl : SizeLimits} (h : TickTockFinal configRoot sa isTock now lt seed libs tf sl) :
    tf.inMsgState = none := by
  obtain ⟨cfg, kind, wc, addr, addrBits, t0, pricing, gas, fwd, t2, t3, _, hnew, _, hs, hc, ha⟩ := h
  have hstart := OKe_of (newTx_spec cfg sa Cell.empty kind wc addr addrBits lt now libs) hnew
  obtain ⟨a, _, _, _, _, _, hu0, hw0, _, hs0, hi0, _, _⟩ := hstart
  have ⟨⟨_, i2, cp2, _⟩, _, _, _, u2, w2, _⟩ := OKo_of (storagePhaseRun_spec t0 pricing gas false) hs
  have ⟨_, hin3, _, _⟩ := OKo_of (OKe_of (computePhaseRun_spec t2 gas sl seed (by rw [u2, hu0])
    (by rw [w2, hw0]) (by rw [cp2, hs0])) hc) rfl
  rcases ha with ⟨_, hap⟩ | ⟨_, rfl⟩
  · have := (OKo_of (OKe_of (actionPhaseRun_spec t3 sl) hap) rfl).2.1
    rw [this, hin3, i2, hi0]
  · rw [hin3, i2, hi0]

/-- The state a transaction starts from is active only if the shard account reads as active. -/
theorem StartsFrom.good {Inv : Option Cell → Option Cell → Prop} {sa : Cell} {cfg : Config} {wc : Int}
    {addr : BitString} {kind : TxKind} {t₀ : Tx} (hs : StartsFrom sa cfg wc addr kind t₀) (hg : Good Inv sa)
    (ha : t₀.accStatus = .active) : Inv t₀.newCode t₀.newData := by
  obtain ⟨a, hu, _, hc, hd, hst, _⟩ := hs
  rw [hc, hd]
  refine hg _ _ _ a hu ?_
  rw [hst] at ha
  cases h : a.status <;> rw [h] at ha <;> first | rfl | cases ha

/-- `Inv` of the code and data a transaction leaves, from `Inv` of those it starts from. -/
theorem Effect.inv {Init : Cell → Prop} {Inv : Option Cell → Option Cell → Prop} {t₀ tf : Tx}
    (heff : Effect t₀ tf) (htf : tf.accStatus = .active)
    (h0 : t₀.accStatus = .active → Inv t₀.newCode t₀.newData) (hdep : DeployOK Init tf)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si → Inv si.code si.data)
    (hrun : RunPreserves Inv) : Inv tf.newCode tf.newData := by
  obtain ⟨code, data, hsrc, hres⟩ := heff htf
  have hcd : Inv code data := by
    rcases hsrc with ⟨ha, rfl, rfl⟩ | ⟨si, hsi, hu, rfl, rfl⟩
    · exact h0 ha
    · unfold msgStateInit? at hsi
      cases hc : tf.inMsgState with
      | none => rw [hc] at hsi; cases hsi
      | some c => rw [hc] at hsi; exact hdeploy c si (hdep c hc hu) hsi
  rcases hres with ⟨e1, e2⟩ | ⟨c, c4, c5, rfl, hran, hd, hnc⟩
  · rw [e1, e2]; exact hcd
  · rw [hd]; exact hrun c data c4 c5 hcd hran _ hnc

/-- **A step keeps the invariant.** -/
theorem Step.good {configRoot : Cell} {Init : Cell → Prop} {Inv : Option Cell → Option Cell → Prop}
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si → Inv si.code si.data)
    (hrun : RunPreserves Inv) {sa sa' : Cell} (hs : Step configRoot Init sa sa') (hg : Good Inv sa) :
    Good Inv sa' := by
  intro wc addr sp a hu ha
  cases hs with
  | ord hash lt' _ hfin hacc hfits hdep hh =>
    subst hacc
    obtain ⟨htf, hc, hd⟩ := computeState_readBack hfits hh lt' hu ha
    obtain ⟨_, _, _, t₀, hst, heff⟩ := hfin.effect
    rw [hc, hd]
    exact heff.inv htf (hst.good hg) hdep hdeploy hrun
  | tickTock hash lt' _ hfin hacc hfits hh =>
    subst hacc
    obtain ⟨htf, hc, hd⟩ := computeState_readBack hfits hh lt' hu ha
    obtain ⟨_, _, _, _, t₀, hst, heff⟩ := hfin.effect
    rw [hc, hd]
    refine heff.inv htf (hst.good hg) ?_ hdeploy hrun
    intro c h
    rw [hfin.inMsgState] at h
    cases h

/-- **Induction over the transactions of an account.** An invariant of the code and data of the
active account that holds at the start, of every `StateInit` that may be deployed, and is preserved
by every committed run of the compute phase (`RunPreserves`), holds of every reachable shard
account. -/
theorem Reachable.good {configRoot : Cell} {Init Start : Cell → Prop} {Inv : Option Cell → Option Cell → Prop}
    (hstart : ∀ sa, Start sa → Good Inv sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si → Inv si.code si.data)
    (hrun : RunPreserves Inv) {sa : Cell} (h : Reachable configRoot Init Start sa) : Good Inv sa := by
  induction h with
  | start hs => exact hstart _ hs
  | step _ hs ih => exact Step.good hdeploy hrun hs ih

/-- `Reachable.good` with the obligation about a run in two parts: a run without `SETCODE` keeps the
invariant of the code with the new data; a `SETCODE` installs code with which the new data satisfies
it. -/
theorem Reachable.good_split {configRoot : Cell} {Init Start : Cell → Prop}
    {Inv : Option Cell → Option Cell → Prop}
    (hstart : ∀ sa, Start sa → Good Inv sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si → Inv si.code si.data)
    (hkeep : ∀ code data c4 c5, Inv (some code) data → Ran code data c4 c5 →
      (∀ c, ¬ActionIn c5 (.setCode c)) → Inv (some code) (some c4))
    (hset : ∀ code data c4 c5 c, Inv (some code) data → Ran code data c4 c5 →
      ActionIn c5 (.setCode c) → Inv (some c) (some c4))
    {sa : Cell} (h : Reachable configRoot Init Start sa) : Good Inv sa := by
  refine Reachable.good hstart hdeploy ?_ h
  intro code data c4 c5 hi hr code' hn
  rcases hn with ⟨rfl, hno⟩ | ⟨c, rfl, hc⟩
  · exact hkeep code data c4 c5 hi hr hno
  · exact hset code data c4 c5 c hi hr hc

/-- **Code that never changes.** If every committed run of the code `C` from data satisfying `P`
commits data satisfying `P` and an action list without `SETCODE`, the account's code is `C` and its
data satisfies `P` in every reachable shard account. -/
theorem Reachable.code_fixed {configRoot : Cell} {Init Start : Cell → Prop} {C : Cell} {P : Option Cell → Prop}
    (hstart : ∀ sa, Start sa → Good (fun code data => code = some C ∧ P data) sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
      si.code = some C ∧ P si.data)
    (hrun : ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧ ∀ c, ¬ActionIn c5 (.setCode c))
    {sa : Cell} (h : Reachable configRoot Init Start sa) : Good (fun code data => code = some C ∧ P data) sa := by
  refine Reachable.good_split hstart hdeploy ?_ ?_ h
  · intro code data c4 c5 ⟨hc, hp⟩ hr _
    cases hc
    exact ⟨rfl, (hrun data c4 c5 hp hr).1⟩
  · intro code data c4 c5 c ⟨hc, hp⟩ hr hs
    cases hc
    exact absurd hs ((hrun data c4 c5 hp hr).2 c)

/-- **Code that changes only to code satisfying the specification.** `Spec code data`: the
specification of the code `code` with the data `data`. If every committed run of a code satisfying
it keeps it, with the same code when the action list has no `SETCODE` and with the code of each of
its `SETCODE` actions otherwise, the account's code and data satisfy it in every reachable shard
account. -/
theorem Reachable.spec {configRoot : Cell} {Init Start : Cell → Prop} {Spec : Cell → Option Cell → Prop}
    (hstart : ∀ sa, Start sa → Good (fun code data => ∃ c, code = some c ∧ Spec c data) sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
      ∃ k, si.code = some k ∧ Spec k si.data)
    (hkeep : ∀ code data c4 c5, Spec code data → Ran code data c4 c5 →
      (∀ c, ¬ActionIn c5 (.setCode c)) → Spec code (some c4))
    (hset : ∀ code data c4 c5 c, Spec code data → Ran code data c4 c5 →
      ActionIn c5 (.setCode c) → Spec c (some c4))
    {sa : Cell} (h : Reachable configRoot Init Start sa) :
    Good (fun code data => ∃ c, code = some c ∧ Spec c data) sa := by
  refine Reachable.good_split hstart hdeploy ?_ ?_ h
  · intro code data c4 c5 ⟨k, hk, hs⟩ hr hno
    cases hk
    exact ⟨code, rfl, hkeep code data c4 c5 hs hr hno⟩
  · intro code data c4 c5 c ⟨k, hk, hs⟩ hr hc
    cases hk
    exact ⟨c, rfl, hset code data c4 c5 c hs hr hc⟩

end TvmLean.Tx

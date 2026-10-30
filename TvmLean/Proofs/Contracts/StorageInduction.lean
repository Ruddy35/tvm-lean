import TvmLean.Proofs.Tx.Example
import TvmLean.Proofs.Tx.NoSetCode
import TvmLean.Proofs.Contracts.StorageRun.Internal
import TvmLean.Proofs.Contracts.StorageRun.External

/-!
# TON Storage across all transactions: the code and the fixed fields never change

From the bytecode of the storage contract of TON Storage (`TvmLean.Contracts.storageCode`,
`storage/storage-daemon/smartcont/storage-contract-code.boc`) to a theorem about every sequence of
transactions of an account (`TvmLean.Tx.Reachable`, `TvmLean/Proofs/Tx/Induction.lean`): under any
configuration, through any inbound messages (internal or external), times, logical times, random
seeds, libraries and tick-tock transactions, an account that runs the storage contract keeps its
code and the fields of its data the contract never writes but as they were
(`reachable`):

* `Stored d0 data`: the data is `Data.encode d` of fields within their widths (`Data.WF`) whose
  provider, Merkle root, file size, rate, longest span paid, client and torrent hash are those of
  `d0` (`Data.Fixed d0 d`), active if `d0` is;
* `AccountInv d0 code data`: the code is `storageCode` and `Stored d0 data`.

`reachable` is `Reachable.code_fixed` with its obligation about a committed run (`run_preserves`):
from every state of `VmStart` of `storageCode` on such data (every gas limit, global version,
inbound stack, `c7`, libraries and limits), a run that commits leaves such data and an action list
without `SETCODE`. That comes from the runs of `TvmLean/Proofs/Contracts/StorageRun/`:
* an internal message (selector 0, `Run.internal`): the outcome of the path taken (`Run.Outcome`:
  the data of `d` with some fields changed, an action list of `SENDRAWMSG` and `RAWRESERVE` actions),
  which keeps the fixed fields (`Run.Outcome.weak`), and whose actions are no `SETCODE`
  (`SafeActs.noSetCode`, TvmLean/Proofs/Tx/NoSetCode.lean);
* an external message (selector -1, `Run.external`) and tick-tock (selector -2, `Run.tickTock`): the
  contract has neither `recv_external` nor `run_ticktock`, the run raises exception 11 and never
  commits.
-/

namespace TvmLean.Contracts.Storage

open TvmLean.Tx

theorem Data.Fixed.trans {a b c : Data} (h1 : Data.Fixed a b) (h2 : Data.Fixed b c) : Data.Fixed a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7⟩

theorem Data.Fixed.refl (d : Data) : Data.Fixed d d := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The invariant -/

/-- The data of the storage contract with the fields of `d0` it never changes: `encode d` of a `d`
within its widths, with the provider, Merkle root, file size, rate, longest span paid, client and
torrent hash of `d0`, active if `d0` is. -/
def Stored (d0 : Data) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.WF ∧ Data.Fixed d0 d ∧ (d0.active = true → d.active = true)

/-- The account runs the storage contract (`storageCode`) with data `Stored d0`. -/
def AccountInv (d0 : Data) (code data : Option Cell) : Prop :=
  code = some storageCode ∧ Stored d0 data

/-- **Every committed run of the storage contract keeps the invariant** (the obligation of
`Reachable.code_fixed`): from data `Stored d0`, a run of the compute phase that commits (`Ran`:
from any state of `VmStart`) leaves data `Stored d0` and an action list without `SETCODE`. -/
theorem run_preserves (d0 : Data) (data : Option Cell) (c4 c5 : Cell) (hd : Stored d0 data)
    (hr : Ran storageCode data c4 c5) : Stored d0 (some c4) ∧ ∀ c, ¬ActionIn c5 (.setCode c) := by
  obtain ⟨d, rfl, hwf, hfx, hact⟩ := hd
  obtain ⟨st, ⟨gv, libs, stack, c7, gl, gm, gc, mdd, mll, hstack, rfl⟩, hcomm, -, rfl, rfl, -⟩ := hr
  rw [convertCodeCell_ordinary storageCode gv libs rfl] at hcomm ⊢
  have hst : ({ computePhaseInit storageCode ((some d.encode).getD Cell.empty) stack #[c7] gl gm gc gv with
      libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll } : VmState) =
      Run.start d.encode stack c7 gl gm gc gv libs mdd mll #[] := rfl
  rw [hst, vmFinal_eq] at hcomm ⊢
  rcases hstack with ⟨bal, val, msg, body, ext, rfl⟩ | ⟨bal, addr, tock, rfl⟩
  · cases ext with
    | false =>
      have ho := Run.internal d hwf msg body bal val c7 gl gm gc gv libs mdd mll #[] _ hcomm
      obtain ⟨d', h4, hwf', hfx', hact', hacts⟩ := Run.Outcome.weak hwf ho
      exact ⟨⟨d', by rw [h4], hwf', hfx.trans hfx', fun h => hact' (hact h)⟩, hacts.noSetCode⟩
    | true =>
      rw [Run.external d.encode msg body bal val c7 gl gm gc gv libs mdd mll #[] _] at hcomm
      cases hcomm
  · rw [Run.tickTock d.encode bal addr tock c7 gl gm gc gv libs mdd mll #[] _] at hcomm
    cases hcomm

/-! ## Across all transactions -/

/-- **The storage contract across all transactions.** Under any configuration, if every start
state has an active account only with the code `storageCode` and data `Stored d0`, and every
`StateInit` the account may be deployed with has that code and such data, then every shard account
reachable by transactions (any messages, times, random seeds, libraries, tick-tock) has an active
account only with the code `storageCode` and data `Stored d0`: the code never changes, nor do the
provider, the Merkle root and the size of the file, the rate, the longest span paid, the client and
the torrent hash; and once active, the contract stays active. -/
theorem reachable {configRoot : Cell} {Init Start : Cell → Prop} (d0 : Data)
    (hstart : ∀ sa, Start sa → Good (AccountInv d0) sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
      AccountInv d0 si.code si.data)
    {sa : Cell} (h : Reachable configRoot Init Start sa) : Good (AccountInv d0) sa :=
  Reachable.code_fixed (C := storageCode) (P := Stored d0) hstart hdeploy (run_preserves d0) h

/-- A `StateInit` (its cell `c`) deploys the storage contract with the fixed fields of `d0`: it
reads as the code `storageCode` and the data `encode d` of a `d` within its widths with the fixed
fields of `d0`, active if `d0` is. -/
def Deploys (d0 : Data) (c : Cell) : Prop :=
  ∀ si, Reader.runExact Account.Reader.stateInit c = some si →
    si.code = some storageCode ∧ ∃ d : Data, si.data = some d.encode ∧ d.WF ∧ Data.Fixed d0 d ∧
      (d0.active = true → d.active = true)

/-- **A storage contract deployed at an empty address.** From a shard account without an account
(`noAccount`), through any transactions that deploy only the storage contract with the fixed
fields of `d0` (`Deploys`), the account, whenever active, runs the storage contract with those
fixed fields. -/
theorem reachable_from_empty (configRoot : Cell) (d0 : Data) {hash : BitString} (hh : hash.size = 256)
    (lt : Nat) {sa : Cell} (h : Reachable configRoot (Deploys d0) (· = noAccount hash lt) sa) :
    Good (AccountInv d0) sa := by
  refine reachable d0 ?_ ?_ h
  · rintro _ rfl
    exact noAccount_good _ hh lt
  · intro c si hc hsi
    obtain ⟨hcode, d, hdata, hwf, hfx, hact⟩ := hc si hsi
    exact ⟨hcode, d, hdata, hwf, hfx, hact⟩

end TvmLean.Contracts.Storage

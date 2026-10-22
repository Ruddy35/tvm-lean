import TvmLean.Proofs.Tx.Example
import TvmLean.Proofs.Tx.NoSetCode
import TvmLean.Proofs.Contracts.Wallet3Run.External
import TvmLean.Proofs.Contracts.Wallet3Run.ExternalOld
import TvmLean.Proofs.Contracts.Wallet3Run.Other

/-!
# Wallet v3 across all transactions: the code and the key never change

From the bytecode (`TvmLean.Contracts.wallet3Code`) to a theorem about every sequence of
transactions of an account (`TvmLean.Tx.Reachable`, `TvmLean/Proofs/Tx/Induction.lean`): under any
configuration, through any inbound messages (internal or external), times, logical times, random
seeds, libraries and tick-tock transactions, an account that is wallet v3 with public key `key` and
subwallet `sub` stays wallet v3 with that key and subwallet (`reachable`):

* `Stored key sub data`: the data is `Data.encode` of fields within their widths
  (`seqno subwallet public_key`, `Wallet3Spec`) with that key and subwallet;
* `AccountInv key sub code data`: the code is `wallet3Code` and `Stored key sub data`.

`reachable` is `Reachable.code_fixed` with its obligation about a committed run (`run_preserves`):
from every state of `VmStart` of `wallet3Code` on such data (every gas limit, global version,
inbound stack, `c7`, libraries and limits), a run that commits leaves such data and an action list
without `SETCODE`. That comes from the runs of `TvmLean/Proofs/Contracts/Wallet3Run/`:
* an external message (selector -1, `Run.external_le`, `Run.external_lt` for global versions from 4
  and below 4): the committed data is the stored data with the seqno increased by one (as 32 bits),
  the action list is made of `SENDRAWMSG` actions (`SendList`), none of which reads as `SETCODE`
  (`SendList.noSetCode`, TvmLean/Proofs/Tx/NoSetCode.lean);
* an internal message (selector 0, `Run.internal`): the data and the empty action list;
* tick-tock (selector -2, `Run.tickTock`): no commit.

`reachable_from_empty`: the same from an address without an account (`noAccount`), when the account
may be deployed only with a `StateInit` of wallet v3 with the key and subwallet (`Deploys`).
-/

namespace TvmLean.Contracts.Wallet3

open TvmLean.Tx

/-! ## The invariant -/

/-- The data of wallet v3 with public key `key` and subwallet `sub`: `encode` of fields within their
widths (`Data.WF`) with that key and subwallet (any seqno). -/
def Stored (key sub : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.WF ∧ d.publicKey = key ∧ d.subwallet = sub

/-- The account is wallet v3 (`wallet3Code`) with public key `key` and subwallet `sub`. -/
def AccountInv (key sub : Nat) (code data : Option Cell) : Prop :=
  code = some wallet3Code ∧ Stored key sub data

/-- `Data.encode` keeps the seqno on its 32 bits only. -/
theorem encode_seqno_mod (d : Data) (s : Nat) :
    Data.encode { d with seqno := s } = Data.encode { d with seqno := s % 2 ^ 32 } := by
  simp only [Data.encode, natToBits_mod]

/-- **Every committed run of wallet v3 keeps the invariant** (the obligation of
`Reachable.code_fixed`): from data `Stored key sub`, a run of the compute phase that commits
(`Ran`: from any state of `VmStart`) leaves data `Stored key sub` and an action list without
`SETCODE`. -/
theorem run_preserves (key sub : Nat) (data : Option Cell) (c4 c5 : Cell) (hd : Stored key sub data)
    (hr : Ran wallet3Code data c4 c5) : Stored key sub (some c4) ∧ ∀ c, ¬ActionIn c5 (.setCode c) := by
  obtain ⟨d, rfl, hwf, hk, hs⟩ := hd
  obtain ⟨st, ⟨gv, libs, stack, c7, gl, gm, gc, mdd, mll, hstack, rfl⟩, hcomm, -, rfl, rfl⟩ := hr
  rw [convertCodeCell_ordinary wallet3Code gv libs rfl] at hcomm ⊢
  have hst : ({ computePhaseInit wallet3Code ((some d.encode).getD Cell.empty) stack #[c7] gl gm gc gv with
      libraries := libs, maxDataDepth := mdd, maxLibraryLoads := mll } : VmState) =
      Run.start d.encode stack c7 gl gm gc gv libs mdd mll #[] := rfl
  rw [hst, vmFinal_eq] at hcomm ⊢
  have hdd : Run.dataOf d.encode = d := Run.dataOf_of_decode (Data.decode_encode d hwf)
  rcases hstack with ⟨bal, val, msg, body, ext, rfl⟩ | ⟨bal, addr, tock, rfl⟩
  · cases ext with
    | false =>
      obtain ⟨h4, h5⟩ := Run.internal d.encode msg body bal val c7 gl gm gc gv libs mdd mll #[] _ hcomm
      rw [h4, h5]
      exact ⟨⟨d, rfl, hwf, hk, hs⟩, noSetCode_empty⟩
    | true =>
      have hspec : ∀ fuel, Run.ExtSpec d.encode (VmState.runWith execInstr fuel
          (Run.start d.encode (computePhaseStack bal val msg body true) c7 gl gm gc gv libs mdd mll #[])) := by
        intro fuel
        by_cases hgv : 4 ≤ gv
        · exact Run.external_le d.encode msg body bal val c7 rfl gl gm gc gv hgv libs mdd mll #[] fuel
        · exact Run.external_lt d.encode msg body bal val c7 rfl gl gm gc gv hgv libs mdd mll #[] fuel
      obtain ⟨h4, h5⟩ := hspec _ hcomm
      rw [h4, hdd, encode_seqno_mod]
      exact ⟨⟨_, rfl, ⟨Nat.mod_lt _ (by decide), hwf.2.1, hwf.2.2⟩, hk, hs⟩, h5.noSetCode⟩
  · rw [Run.tickTock d.encode bal addr tock c7 gl gm gc gv libs mdd mll #[] _] at hcomm
    cases hcomm

/-! ## Across all transactions -/

/-- **Wallet v3 across all transactions.** Under any configuration, if every start state has an
active account only with the code `wallet3Code` and data `Stored key sub`, and every `StateInit` the
account may be deployed with has that code and such data, then every shard account reachable by
transactions (any messages, times, random seeds, libraries, tick-tock) has an active account only
with the code `wallet3Code` and data `Stored key sub`: the code, the public key and the subwallet
never change. -/
theorem reachable {configRoot : Cell} {Init Start : Cell → Prop} (key sub : Nat)
    (hstart : ∀ sa, Start sa → Good (AccountInv key sub) sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
      AccountInv key sub si.code si.data)
    {sa : Cell} (h : Reachable configRoot Init Start sa) : Good (AccountInv key sub) sa :=
  Reachable.code_fixed (C := wallet3Code) (P := Stored key sub) hstart hdeploy (run_preserves key sub) h

/-- A `StateInit` (its cell `c`) deploys wallet v3 with public key `key` and subwallet `sub`: it
reads as the code `wallet3Code` and the data `encode` of some seqno (of 32 bits) with that
subwallet and key. -/
def Deploys (key sub : Nat) (c : Cell) : Prop :=
  ∀ si, Reader.runExact Account.Reader.stateInit c = some si →
    si.code = some wallet3Code ∧ ∃ seqno, seqno < 2 ^ 32 ∧ si.data = some (Data.encode ⟨seqno, sub, key⟩)

/-- **A wallet deployed at an empty address.** From a shard account without an account
(`noAccount`), through any transactions that deploy only wallet v3 with public key `key` and
subwallet `sub` (`Deploys`; any seqno), the account, whenever active, is wallet v3 with that key and
subwallet. -/
theorem reachable_from_empty (configRoot : Cell) (key sub : Nat) (hk : key < 2 ^ 256) (hs : sub < 2 ^ 32)
    {hash : BitString} (hh : hash.size = 256) (lt : Nat) {sa : Cell}
    (h : Reachable configRoot (Deploys key sub) (· = noAccount hash lt) sa) : Good (AccountInv key sub) sa := by
  refine reachable key sub ?_ ?_ h
  · rintro _ rfl
    exact noAccount_good _ hh lt
  · intro c si hc hsi
    obtain ⟨hcode, seqno, hsq, hdata⟩ := hc si hsi
    exact ⟨hcode, ⟨seqno, sub, key⟩, hdata, ⟨hsq, hs, hk⟩, rfl, rfl⟩

end TvmLean.Contracts.Wallet3

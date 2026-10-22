import TvmLean.Proofs.Tx.Induction

/-!
# An example of the induction over transactions

`codeData_persist`: under any configuration, from an empty shard account (`noAccount`:
`account_none`), through any transactions the model runs (`Reachable`: any inbound messages,
times, logical times, random seeds, libraries, tick-tock transactions) that deploy only a
`StateInit` with code and data (`HasCodeData`), every active account has code and data. The
obligations of `Reachable.good` are trivial here: the start has no active account
(`noAccount_good`), a deployed `StateInit` has code and data by `HasCodeData`, and a committed run
leaves data (`some c4`) and code (the old code or that of a `SETCODE`, `NewCode`), whatever the
code does. `codeData_step`: the same for one transaction the model returns (`emulate ... = .ok`),
with nothing else to check about it than what it deploys.
-/

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-- The shard account of `account_none` (no account at the address). -/
def noAccount (hash : BitString) (lt : Nat) : Cell := shardAccountCell (W.bool {} false).cell hash lt

/-- No account is active in `noAccount`: any invariant holds of it. -/
theorem noAccount_good (Inv : Option Cell → Option Cell → Prop) {hash : BitString} (hh : hash.size = 256)
    (lt : Nat) : Good Inv (noAccount hash lt) := by
  intro wc addr sp a hu ha
  obtain ⟨acc, x, _, _, _, _, hsa, hbit, _⟩ := OKo_of (unpack_active _ wc addr sp) hu ha
  have := shardAccount_read hh hsa
  subst this
  have hr := Rem.ofCell (W.bool {} false).cell
  rw [show (W.bool {} false).cell.bits.toList = [false] from rfl] at hr
  rw [Rem.readBit0 hr] at hbit
  cases hbit

/-- The cell of a `StateInit` with code and data. -/
def HasCodeData (c : Cell) : Prop :=
  ∀ si, Reader.runExact Account.Reader.stateInit c = some si → si.code.isSome ∧ si.data.isSome

/-- **Example.** Every active account reachable from an empty shard account by transactions that
deploy only a `StateInit` with code and data has code and data. -/
theorem codeData_persist (configRoot : Cell) {hash : BitString} (hh : hash.size = 256) (lt : Nat) {sa : Cell}
    (h : Reachable configRoot HasCodeData (· = noAccount hash lt) sa) :
    Good (fun code data => code.isSome ∧ data.isSome) sa := by
  refine Reachable.good ?_ ?_ ?_ h
  · rintro _ rfl
    exact noAccount_good _ hh lt
  · intro c si hc hsi
    exact hc si hsi
  · intro code data c4 c5 _ _ code' hn
    refine ⟨?_, rfl⟩
    rcases hn with ⟨rfl, _⟩ | ⟨c, rfl, _⟩ <;> rfl

/-- A committed run leaves code and data (the obligation of `codeData_persist`). -/
theorem codeData_run : RunPreserves (fun code data => code.isSome ∧ data.isSome) := by
  intro code data c4 c5 _ _ code' hn
  refine ⟨?_, rfl⟩
  rcases hn with ⟨rfl, _⟩ | ⟨c, rfl, _⟩ <;> rfl

/-- **Example, one transaction.** If every active account of the shard account `sa` has code and
data, so has every active account of the shard account of the account an ordinary transaction the
model returns writes, if it deploys only a `StateInit` with code and data. -/
theorem codeData_step {configRoot sa inMsg : Cell} {now lt : Nat} {seed : BitString} {libs : Option Cell}
    {tx acc : Cell} (h : emulate configRoot sa inMsg now lt seed libs = .ok tx acc)
    (hdep : ∀ tf sl, EmulateFinal configRoot sa inMsg now lt seed libs tf sl → DeployOK HasCodeData tf)
    (hg : Good (fun code data => code.isSome ∧ data.isSome) sa)
    {hash : BitString} (hh : hash.size = 256) (lt' : Nat) :
    Good (fun code data => code.isSome ∧ data.isSome) (shardAccountCell acc hash lt') :=
  Step.good (fun _ si hc hsi => hc si hsi) codeData_run (Step.of_emulate h hdep hash hh lt') hg

end TvmLean.Tx

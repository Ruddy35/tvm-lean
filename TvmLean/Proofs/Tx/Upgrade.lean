import TvmLean.Proofs.Tx.Induction

/-!
# Induction over the transactions of a contract whose code may change

`Reachable.code_fixed` (TvmLean/Proofs/Tx/Induction.lean) carries an invariant `P` of the data of a
contract whose code `C` never changes: every committed run of `C` keeps `P` and installs no code.
A contract that may run `SETCODE` needs another form, since a run of `C` may install code that is
not `C`, and nothing is known of what that code does (it may even install `C` again, with any data):

* `Reachable.code_self`: the code changes only to `C` itself (every `SETCODE` of a committed run of
  `C` installs `C`): the code is `C` and the data satisfies `P` in every reachable shard account, as
  for `Reachable.code_fixed` (`Reachable.spec` with the specification "the code is `C` and the data
  satisfies `P`").
* `ReachableWhile.good_codes`: any code may be installed. The shard accounts reachable by
  transactions run while the code is `C` (`ReachableWhile`: a step is followed only from a shard
  account whose active accounts have the code `C`, so the account's history up to its first change
  of code) have data satisfying `P` while their code is `C`, and every code they have is `C` or one
  that a run of `C` may install (`K`: in `tools/contract-check`, the condition of `Acts K`,
  TvmLean/Proofs/Tx/Acts.lean, e.g. "carried by a message signed by the owner"); `ReachableWhile.good`
  without `K`. The steps: `Effect.invTo` and `Step.goodTo`, `Effect.inv` and `Step.good` with one
  invariant before the transaction and another after it.
-/

namespace TvmLean.Tx

/-- **Code that changes only to itself.** If every committed run of the code `C` from data
satisfying `P` commits data satisfying `P` and an action list whose `SETCODE` actions install `C`,
the account's code is `C` and its data satisfies `P` in every reachable shard account. -/
theorem Reachable.code_self {configRoot : Cell} {Init Start : Cell → Prop} {C : Cell} {P : Option Cell → Prop}
    (hstart : ∀ sa, Start sa → Good (fun code data => code = some C ∧ P data) sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
      si.code = some C ∧ P si.data)
    (hrun : ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧ ∀ c, ActionIn c5 (.setCode c) → c = C)
    {sa : Cell} (h : Reachable configRoot Init Start sa) : Good (fun code data => code = some C ∧ P data) sa := by
  have hg := Reachable.spec (Spec := fun c data => c = C ∧ P data)
    (fun sa hs wc addr sp a hu ha => ⟨C, (hstart sa hs wc addr sp a hu ha).1, rfl,
      (hstart sa hs wc addr sp a hu ha).2⟩)
    (fun c si hi hr => ⟨C, (hdeploy c si hi hr).1, rfl, (hdeploy c si hi hr).2⟩)
    (by
      rintro code data c4 c5 ⟨rfl, hp⟩ hr _
      exact ⟨rfl, (hrun data c4 c5 hp hr).1⟩)
    (by
      rintro code data c4 c5 c ⟨rfl, hp⟩ hr hs
      exact ⟨(hrun data c4 c5 hp hr).2 c hs, (hrun data c4 c5 hp hr).1⟩) h
  intro wc addr sp a hu ha
  obtain ⟨c, hc, rfl, hp⟩ := hg wc addr sp a hu ha
  exact ⟨hc, hp⟩

/-- The shard accounts reachable by transactions (`Step`) from those of `Start` while the account's
code is `C`: a step is followed only from a shard account whose active accounts have the code `C`. -/
inductive ReachableWhile (configRoot : Cell) (Init : Cell → Prop) (Start : Cell → Prop) (C : Cell) :
    Cell → Prop
  | start {sa : Cell} : Start sa → ReachableWhile configRoot Init Start C sa
  | step {sa sa' : Cell} : ReachableWhile configRoot Init Start C sa →
      Good (fun code _ => code = some C) sa → Step configRoot Init sa sa' →
      ReachableWhile configRoot Init Start C sa'

/-- `Effect.inv` with an invariant `I` of the account before the transaction and `J` after it:
the account it starts from, if active, and a deployment satisfy `I`; code and data that the
transaction keeps satisfy `J` when they satisfy `I`; every committed run from code and data
satisfying `I` leaves the new code (`NewCode`) and data satisfying `J`. -/
theorem Effect.invTo {Init : Cell → Prop} {I J : Option Cell → Option Cell → Prop} {t₀ tf : Tx}
    (heff : Effect t₀ tf) (htf : tf.accStatus = .active)
    (h0 : t₀.accStatus = .active → I t₀.newCode t₀.newData) (hdep : DeployOK Init tf)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si → I si.code si.data)
    (hIJ : ∀ code data, I code data → J code data)
    (hrun : ∀ code data c4 c5, I (some code) data → Ran code data c4 c5 →
      ∀ code', NewCode c5 (some code) code' → J code' (some c4)) :
    J tf.newCode tf.newData := by
  obtain ⟨code, data, hsrc, hres⟩ := heff htf
  have hcd : I code data := by
    rcases hsrc with ⟨ha, rfl, rfl⟩ | ⟨si, hsi, hu, rfl, rfl⟩
    · exact h0 ha
    · unfold msgStateInit? at hsi
      cases hc : tf.inMsgState with
      | none => rw [hc] at hsi; cases hsi
      | some c => rw [hc] at hsi; exact hdeploy c si (hdep c hc hu) hsi
  rcases hres with ⟨e1, e2⟩ | ⟨c, c4, c5, rfl, hran, hd, hnc⟩
  · rw [e1, e2]; exact hIJ _ _ hcd
  · rw [hd]; exact hrun c data c4 c5 hcd hran _ hnc

/-- `Step.good` with an invariant `I` before the step and `J` after it (`Effect.invTo`). -/
theorem Step.goodTo {configRoot : Cell} {Init : Cell → Prop} {I J : Option Cell → Option Cell → Prop}
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si → I si.code si.data)
    (hIJ : ∀ code data, I code data → J code data)
    (hrun : ∀ code data c4 c5, I (some code) data → Ran code data c4 c5 →
      ∀ code', NewCode c5 (some code) code' → J code' (some c4))
    {sa sa' : Cell} (hs : Step configRoot Init sa sa') (hg : Good I sa) : Good J sa' := by
  intro wc addr sp a hu ha
  cases hs with
  | ord hash lt' _ hfin hacc hdep hh =>
    obtain ⟨htf, hc, hd⟩ := computeState_readBack hacc hfin.fits hh lt' hu ha
    obtain ⟨_, _, _, t₀, hst, heff⟩ := hfin.effect
    rw [hc, hd]
    exact heff.invTo htf (hst.good hg) hdep hdeploy hIJ hrun
  | tickTock hash lt' _ hfin hacc hh =>
    obtain ⟨htf, hc, hd⟩ := computeState_readBack hacc hfin.fits hh lt' hu ha
    obtain ⟨_, _, _, _, t₀, hst, heff⟩ := hfin.effect
    rw [hc, hd]
    refine heff.invTo htf (hst.good hg) ?_ hdeploy hIJ hrun
    intro c h
    rw [hfin.inMsgState] at h
    cases h

/-- **Induction while the code is `C`, with the codes it installs.** If the start states satisfy
the statement below, the deployments install `C` with data satisfying `P`, and every committed run
of `C` from data satisfying `P` commits data satisfying `P` and an action list whose `SETCODE`
actions install codes satisfying `K`, then in every shard account reachable by transactions while
the code is `C` (`ReachableWhile`) an active account with the code `C` has data satisfying `P`,
and an active account has the code `C` or a code satisfying `K`. -/
theorem ReachableWhile.good_codes {configRoot : Cell} {Init Start : Cell → Prop} {C : Cell}
    {P : Option Cell → Prop} {K : Cell → Prop}
    (hstart : ∀ sa, Start sa →
      Good (fun code data => (code = some C → P data) ∧ ∀ c, code = some c → c = C ∨ K c) sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
      si.code = some C ∧ P si.data)
    (hrun : ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4) ∧ ∀ c, ActionIn c5 (.setCode c) → K c)
    {sa : Cell} (h : ReachableWhile configRoot Init Start C sa) :
    Good (fun code data => (code = some C → P data) ∧ ∀ c, code = some c → c = C ∨ K c) sa := by
  induction h with
  | start hs => exact hstart _ hs
  | step _ hkeep hs ih =>
    refine Step.goodTo (I := fun code data => code = some C ∧ P data) hdeploy ?_ ?_ hs ?_
    · rintro code data ⟨rfl, hp⟩
      exact ⟨fun _ => hp, fun c hc => Or.inl (Option.some.inj hc).symm⟩
    · rintro code data c4 c5 ⟨hc, hp⟩ hr code' hn
      cases hc
      have hk := hrun data c4 c5 hp hr
      refine ⟨fun _ => hk.1, fun c hc => ?_⟩
      rcases hn with ⟨rfl, _⟩ | ⟨c', rfl, hin⟩
      · exact Or.inl (Option.some.inj hc).symm
      · obtain rfl := Option.some.inj hc
        exact Or.inr (hk.2 _ hin)
    · intro wc addr sp a hu ha
      have hC := hkeep wc addr sp a hu ha
      exact ⟨hC, (ih wc addr sp a hu ha).1 hC⟩

/-- **Induction while the code is `C`.** If the start states and the deployments satisfy `P` when
their code is `C` (a deployment installs `C`), and every committed run of `C` from data satisfying
`P` commits data satisfying `P`, then in every shard account reachable by transactions while the
code is `C` (`ReachableWhile`), an active account with the code `C` has data satisfying `P`, whatever
code the runs of `C` install (`ReachableWhile.good_codes` with any code). -/
theorem ReachableWhile.good {configRoot : Cell} {Init Start : Cell → Prop} {C : Cell} {P : Option Cell → Prop}
    (hstart : ∀ sa, Start sa → Good (fun code data => code = some C → P data) sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
      si.code = some C ∧ P si.data)
    (hrun : ∀ data c4 c5, P data → Ran C data c4 c5 → P (some c4))
    {sa : Cell} (h : ReachableWhile configRoot Init Start C sa) :
    Good (fun code data => code = some C → P data) sa := by
  have hg := ReachableWhile.good_codes (K := fun _ => True)
    (fun sa hs wc addr sp a hu ha => ⟨hstart sa hs wc addr sp a hu ha, fun _ _ => Or.inr trivial⟩)
    hdeploy (fun data c4 c5 hp hr => ⟨hrun data c4 c5 hp hr, fun _ _ => trivial⟩) h
  exact fun wc addr sp a hu ha => (hg wc addr sp a hu ha).1

end TvmLean.Tx

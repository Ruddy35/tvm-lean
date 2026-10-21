import TvmLean.Proofs.WF.Library
import Std.Tactic.Do

/-!
# The VM monad keeps states well-formed

Specifications, as `Std.Do` triples, of the VM monad operations the instructions are made of: each
keeps `VmState.WF` (also when it throws) given well-formed arguments, and says what it returns. They
are registered with `@[spec]`, so that `mvcgen` uses them when it unfolds an instruction.

`VM.Keeps m Q` is the shape of a whole instruction: from a well-formed state, `m` ends in a
well-formed state, normally or by an exception, and its result satisfies `Q`. `VM.Keeps.run` reads
it back as a statement about `m.run`.

* The stack: `push` (of a well-formed value), `pop`, `fetch`, `swap`, `popInt`, `popCont`,
  `popBool`, `pushIntQuiet`, `pushSmallInt`, `popIntFinite`, `popNatUpTo` (its bound),
  `popCell`, `popSlice`, `popBuilder`, `popMaybeCell` (well-formed results), `checkUnderflow`,
  `popStackCount`.
* Gas and loads: the state functions that only change gas and counters keep the invariant
  (`VmState.consumeGas_WF`, ...; an `iff`); `VM.consumeGas`, `chargeCellCreates`,
  `registerCellLoad(Special)`, `checkNewCellDepth`, `chargeDictSetCreates`; `cellResolver` (a
  resolver keeping cells well-formed), `loadCellSlice` (a well-formed slice, `Library.lean`),
  `loadLibrary`.
* Registers and exceptions: `VmState.getCtr` (a well-formed value), `setCtr` (of a well-formed
  value), `throwException(Arg)`, `tryCommit`, `ret`, `retAlt`, `jumpTo`, `callTo(WithFrame)`;
  `VM.throwToHandler`, `unimplementedInstr`, `getUnpackedConfigTuple`, `getMsgPrices`,
  `getGasPrices`, `execNullSwapIf`; continuations' `forceCdata`, `defineCtr`
  (`OrdCregs.defineFromValue`).
* `throw` needs nothing: `mvcgen` knows it, and the invariant asks the same of an exception.

`wf_vc` closes the verification conditions `mvcgen` leaves (see its docstring).
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

/-- From a well-formed state, `m` ends in a well-formed state, normally or by an exception, and its
result satisfies `Q`. -/
abbrev VM.Keeps {α : Type} (m : VM α) (Q : α → Prop) : Prop :=
  ⦃fun st => ⌜st.WF⌝⦄ m ⦃post⟨fun a st => ⌜st.WF ∧ Q a⌝, fun _ st => ⌜st.WF⌝⟩⦄

/-- `VM.Keeps` with no claim on the result. -/
abbrev VM.KeepsWF (m : VM Unit) : Prop := VM.Keeps m fun _ => True

/-- A triple of the VM monad as a statement about `run`. -/
theorem VM.triple_run {α : Type} {m : VM α} {P : VmState → Prop} {Q : α → VmState → Prop}
    {E : Excno → VmState → Prop}
    (h : ⦃fun st => ⌜P st⌝⦄ m ⦃post⟨fun a st => ⌜Q a st⌝, fun e st => ⌜E e st⌝⟩⦄) (st : VmState)
    (hs : P st) :
    match m.run st with
    | (.ok a, st') => Q a st'
    | (.error e, st') => E e st' := by
  have := h st hs
  simp only [wp, PredTrans.pushExcept_apply, PredTrans.pushArg_apply] at this
  revert this
  simp only [ExceptT.run]
  rcases m st with ⟨r, st'⟩
  cases r <;> simp_all [Id.run, SPred.down_pure]

/-- A statement about `run` as a triple of the VM monad. -/
theorem VM.triple_of_run {α : Type} {m : VM α} {P : VmState → Prop} {Q : α → VmState → Prop}
    {E : Excno → VmState → Prop}
    (h : ∀ st, P st → match m.run st with
      | (.ok a, st') => Q a st'
      | (.error e, st') => E e st') :
    ⦃fun st => ⌜P st⌝⦄ m ⦃post⟨fun a st => ⌜Q a st⌝, fun e st => ⌜E e st⌝⟩⦄ := by
  intro st hs
  have := h st hs
  simp only [wp, PredTrans.pushExcept_apply, PredTrans.pushArg_apply]
  revert this
  simp only [ExceptT.run]
  rcases m st with ⟨r, st'⟩
  cases r <;> simp_all [Id.run, SPred.down_pure]

/-- `VM.Keeps` read on `run`: the state after `m` is well-formed, and so is a result. -/
theorem VM.Keeps.run {α : Type} {m : VM α} {Q : α → Prop} (h : m.Keeps Q) {st : VmState}
    (hs : st.WF) : (m.run st).2.WF ∧ ∀ a, (m.run st).1 = .ok a → Q a := by
  have := VM.triple_run h st hs
  revert this
  rcases m.run st with ⟨r, st'⟩
  cases r <;> simp_all

theorem VM.Keeps.of_run {α : Type} {m : VM α} {Q : α → Prop}
    (h : ∀ st, st.WF → (m.run st).2.WF ∧ ∀ a, (m.run st).1 = .ok a → Q a) : m.Keeps Q := by
  apply VM.triple_of_run
  intro st hs
  have := h st hs
  revert this
  rcases m.run st with ⟨r, st'⟩
  cases r <;> simp_all

/-- A weaker claim on the result. -/
theorem VM.Keeps.mono {α : Type} {m : VM α} {Q Q' : α → Prop} (h : m.Keeps Q)
    (hq : ∀ a, Q a → Q' a) : m.Keeps Q' := by
  apply VM.Keeps.of_run
  intro st hs
  obtain ⟨h1, h2⟩ := h.run hs
  exact ⟨h1, fun a ha => hq a (h2 a ha)⟩

/-! ## State changes that keep the invariant -/

/-- Two states agree on everything the invariant reads. -/
theorem VmState.wf_congr {st st' : VmState} (hs : st'.stack = st.stack) (hr : st'.regs = st.regs)
    (hc : st'.cc = st.cc) (hk : st'.cstate = st.cstate) (hl : st'.libraries = st.libraries) :
    st'.WF ↔ st.WF :=
  ⟨fun h => h.of_eq hs.symm hr.symm hc.symm hk.symm hl.symm, fun h => h.of_eq hs hr hc hk hl⟩

@[simp] theorem VmState.consumeGas_WF (st : VmState) (n : Int) : (st.consumeGas n).WF ↔ st.WF :=
  VmState.wf_congr rfl rfl rfl rfl rfl

@[simp] theorem VmState.consumeTupleGas_WF (st : VmState) (n : Nat) :
    (st.consumeTupleGas n).WF ↔ st.WF := by
  simp [VmState.consumeTupleGas]

@[simp] theorem VmState.consumeStackGas_WF (st : VmState) (n : Nat) :
    (st.consumeStackGas n).WF ↔ st.WF := by
  simp [VmState.consumeStackGas]

@[simp] theorem VmState.registerChkSgnCall_WF (st : VmState) : st.registerChkSgnCall.WF ↔ st.WF := by
  unfold VmState.registerChkSgnCall
  split
  · rfl
  · dsimp only
    split
    · simp only [VmState.consumeGas_WF]; exact VmState.wf_congr rfl rfl rfl rfl rfl
    · exact VmState.wf_congr rfl rfl rfl rfl rfl

@[simp] theorem VmState.registerCellLoad_WF (st : VmState) (c : Cell) :
    (st.registerCellLoad c).WF ↔ st.WF := by
  unfold VmState.registerCellLoad
  simp only [VmState.consumeGas_WF]
  split
  · rfl
  · exact VmState.wf_congr rfl rfl rfl rfl rfl

@[simp] theorem VmState.admitLibrary_WF (st : VmState) (hash : BitString) :
    (st.admitLibrary hash).1.WF ↔ st.WF := by
  unfold VmState.admitLibrary
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · exact VmState.wf_congr rfl rfl rfl rfl rfl

@[simp] theorem VmState.registerLibraryLoad_WF (st : VmState) (hash : BitString) :
    (st.registerLibraryLoad hash).WF ↔ st.WF := by
  unfold VmState.registerLibraryLoad
  split
  · rename_i st' refused h
    have : st' = (st.admitLibrary hash).1 := by rw [h]
    split
    · rw [← VmState.admitLibrary_WF st hash, ← this]
      exact VmState.wf_congr rfl rfl rfl rfl rfl
    · rw [← VmState.admitLibrary_WF st hash, ← this]

@[simp] theorem VmState.registerCellLoads_WF (st : VmState) (l : List LibraryLoadStep) :
    (st.registerCellLoads l).1.WF ↔ st.WF := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih =>
    cases x with
    | cell c =>
      simp only [VmState.registerCellLoads]
      split
      · simp
      · rw [ih]; simp
    | library hash =>
      simp only [VmState.registerCellLoads]
      rw [ih]; simp

/-! ## Closing verification conditions -/

theorem Value.getElem!_WF {a : Array Value} (h : ∀ v ∈ a, v.WF) (i : Nat) : (a[i]!).WF :=
  WF.getElem!_of_forall h Value.default_WF i

/-- Closes a verification condition `mvcgen` leaves about well-formed states: removes the state
changes that keep the invariant (gas, counters), splits `VmState.WF` and `Regs.WF` into their
fields and closes the goal from the hypotheses with `grind`, which knows the membership lemmas of
arrays and the inversions of `Value.WF`; `wf_vc [h₁, h₂]` gives it more lemmas. -/
syntax "wf_vc" (" [" Lean.Parser.Tactic.grindParam,* "]")? : tactic

macro_rules
  | `(tactic| wf_vc) => `(tactic| wf_vc [])
  | `(tactic| wf_vc [$ts,*]) => `(tactic|
    ((try simp (config := { zetaDelta := true }) only [VmState.consumeGas_WF,
        VmState.consumeTupleGas_WF, VmState.consumeStackGas_WF, VmState.registerChkSgnCall_WF,
        VmState.registerCellLoad_WF, VmState.registerLibraryLoad_WF, VmState.registerCellLoads_WF,
        VmState.admitLibrary_WF] at *)
     (try simp only [VmState.wf_iff, Regs.wf_iff] at *)
     grind [→ WF.mem_of_mem_pop, → WF.mem_of_mem_extract, → WF.mem_of_mem_take,
       → WF.mem_or_eq_of_mem_set!, → Array.mem_of_getElem?, WF.getElem!_mem_or_default,
       Array.back_mem, Value.default_WF,
       Cell.default_WF, Value.wf_int, Value.wf_cell, Value.wf_slice, Value.wf_builder, Value.wf_tuple,
       Value.wf_cont, Value.wf_null, Value.wf_nullCell, $ts,*]))

/-! ## The stack -/

@[spec] theorem VM.push_spec (v : Value) :
    ⦃fun st => ⌜st.WF ∧ v.WF⌝⦄ VM.push v ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.push]
  all_goals wf_vc

@[spec] theorem VM.pop_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.pop ⦃post⟨fun v st => ⌜st.WF ∧ v.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.pop]
  all_goals wf_vc

@[spec] theorem VM.fetch_spec (i : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.fetch i ⦃post⟨fun v st => ⌜st.WF ∧ v.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.fetch]
  all_goals wf_vc

@[spec] theorem VM.swap_spec (i j : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.swap i j ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.swap]
  all_goals wf_vc

@[spec] theorem VM.popInt_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popInt ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popInt]
  all_goals wf_vc

@[spec] theorem VM.popCont_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popCont ⦃post⟨fun k st => ⌜st.WF ∧ k.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popCont]
  all_goals wf_vc

@[spec] theorem VM.popBool_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popBool ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popBool]
  all_goals wf_vc

@[spec] theorem VM.pushIntQuiet_spec (i : IntVal) (quiet : Bool) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.pushIntQuiet i quiet ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.pushIntQuiet]
  all_goals wf_vc

@[spec] theorem VM.pushSmallInt_spec (n : Int) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.pushSmallInt n ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.pushSmallInt]
  all_goals wf_vc

@[spec] theorem VM.popIntFinite_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popIntFinite ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popIntFinite]
  all_goals wf_vc

@[spec] theorem VM.popNatUpTo_spec (max : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popNatUpTo max
      ⦃post⟨fun n st => ⌜st.WF ∧ n ≤ max⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popNatUpTo]
  all_goals wf_vc

@[spec] theorem VM.popCell_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popCell ⦃post⟨fun c st => ⌜st.WF ∧ c.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popCell]
  all_goals wf_vc

@[spec] theorem VM.popSlice_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popSlice ⦃post⟨fun s st => ⌜st.WF ∧ s.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popSlice]
  all_goals wf_vc

@[spec] theorem VM.popBuilder_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popBuilder ⦃post⟨fun b st => ⌜st.WF ∧ b.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popBuilder]
  all_goals wf_vc

@[spec] theorem VM.popMaybeCell_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popMaybeCell
      ⦃post⟨fun c st => ⌜st.WF ∧ ∀ c', c = some c' → c'.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popMaybeCell]
  all_goals wf_vc

@[spec] theorem VM.checkUnderflow_spec (n : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.checkUnderflow n ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.checkUnderflow]
  all_goals wf_vc

@[spec] theorem VM.popStackCount_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.popStackCount ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.popStackCount]
  all_goals wf_vc

/-! ## Gas and cell loads -/

@[spec] theorem VM.consumeGas_spec (n : Int) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.consumeGas n ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.consumeGas]
  all_goals wf_vc

@[spec] theorem VM.chargeCellCreates_spec (n : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.chargeCellCreates n ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.chargeCellCreates] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

@[spec] theorem VM.registerCellLoad_spec (c : Cell) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.registerCellLoad c ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.registerCellLoad]
  all_goals wf_vc

@[spec] theorem VM.registerCellLoadSpecial_spec (c : Cell) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.registerCellLoadSpecial c
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.registerCellLoadSpecial]
  all_goals wf_vc

@[spec] theorem VM.checkNewCellDepth_spec (refs : Array Cell) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.checkNewCellDepth refs ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.checkNewCellDepth]
  all_goals wf_vc

@[spec] theorem VM.chargeDictSetCreates_spec (newRoot? : Option Cell) (created : Nat)
    (path : Cell → Array Cell) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.chargeDictSetCreates newRoot? created path
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.chargeDictSetCreates]
  all_goals wf_vc

/-- The cell loader of the VM keeps cells well-formed: library roots come from well-formed
collections. -/
@[spec] theorem VM.cellResolver_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.cellResolver
      ⦃post⟨fun r st => ⌜st.WF ∧ ResolverWF r⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.cellResolver]
  rename_i st hst
  exact ⟨hst, libraryResolver_WF hst.libraries _ _⟩

/-- C++ `load_cell_slice`: a well-formed cell loads as a well-formed slice. -/
@[spec] theorem VM.loadCellSlice_spec (c : Cell) :
    ⦃fun st => ⌜st.WF ∧ c.WF⌝⦄ VM.loadCellSlice c
      ⦃post⟨fun s st => ⌜st.WF ∧ s.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.loadCellSlice]
  all_goals try wf_vc
  rename_i st h1 _ st' h2 r hr
  exact ⟨h2, Slice.ofCell_WF (libraryResolveLoads_WF h2.libraries h1.2 hr)⟩

@[spec] theorem VM.loadLibrary_spec (hash : BitString) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.loadLibrary hash
      ⦃post⟨fun r st => ⌜st.WF ∧ ∀ c, r = some c → c.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.loadLibrary]
  all_goals try wf_vc
  rename_i st hst _ _
  refine ⟨(VmState.admitLibrary_WF st hash).mpr hst, fun c hc => ?_⟩
  obtain ⟨lib, hlib, hl⟩ := Array.exists_of_findSome?_eq_some hc
  have hlibs : ∀ c ∈ (st.admitLibrary hash).1.libraries, c.WF :=
    ((VmState.admitLibrary_WF st hash).mpr hst).libraries
  exact lookupLibraryIn?_WF (hlibs lib hlib) hl

/-! ## Registers, exceptions and jumps (state functions) -/

theorem VmState.WF.getCtr {st : VmState} (h : st.WF) {idx : Nat} {v : Value}
    (hv : st.getCtr idx = .ok v) : v.WF := by
  have hr := h.regs
  unfold VmState.getCtr at hv
  split at hv <;> (try cases hv) <;> simp only [Value.wf_cont, Value.wf_cell, Value.wf_tuple] <;>
    (first | exact hr.c0 | exact hr.c1 | exact hr.c2 | exact hr.c3 | exact hr.c4 | exact hr.c5 |
      exact hr.c7)

theorem VmState.WF.setCtr {st : VmState} (h : st.WF) {idx : Nat} {v : Value} {st' : VmState}
    (hv : v.WF) (hs : st.setCtr idx v = .ok st') : st'.WF := by
  have hr := h.regs
  unfold VmState.setCtr at hs
  split at hs <;> (try split at hs) <;> (try cases hs) <;>
    (try simp only [Value.wf_cont, Value.wf_cell, Value.wf_tuple] at hv) <;>
    exact h.withRegs (by simp only [Regs.wf_iff] at hr ⊢; grind)

theorem VmState.WF.throwException {st : VmState} (h : st.WF) (exc : Int) :
    (st.throwException exc).WF := by
  refine ⟨?_, h.regs, h.regs.c2, h.committedC4, h.committedC5, h.libraries⟩
  unfold VmState.throwException; simp

theorem VmState.WF.throwExceptionArg {st : VmState} (h : st.WF) (exc : Int) {arg : Value}
    (ha : arg.WF) : (st.throwExceptionArg exc arg).WF := by
  refine ⟨?_, h.regs, h.regs.c2, h.committedC4, h.committedC5, h.libraries⟩
  unfold VmState.throwExceptionArg; simp [ha]

theorem VmState.WF.tryCommit {st : VmState} (h : st.WF) : st.tryCommit.2.WF := by
  unfold VmState.tryCommit
  split
  · exact ⟨h.stack, h.regs, h.cc, h.regs.c4, h.regs.c5, h.libraries⟩
  · exact h

theorem VmState.WF.ret {st : VmState} (h : st.WF) : st.ret.WF := by
  have hr := h.regs
  refine ⟨h.stack, ?_, hr.c0, h.committedC4, h.committedC5, h.libraries⟩
  exact ⟨.quit 0, hr.c1, hr.c2, hr.c3, hr.c4, hr.c5, hr.c7⟩

theorem VmState.WF.retAlt {st : VmState} (h : st.WF) : st.retAlt.WF := by
  have hr := h.regs
  refine ⟨h.stack, ?_, hr.c1, h.committedC4, h.committedC5, h.libraries⟩
  exact ⟨hr.c0, .quit 1, hr.c2, hr.c3, hr.c4, hr.c5, hr.c7⟩

theorem VmState.WF.jumpTo {st : VmState} (h : st.WF) {k : Continuation} (hk : k.WF) :
    (st.jumpTo k).WF :=
  h.withCc hk

theorem VmState.WF.callToWithFrame {st : VmState} (h : st.WF) {frame : CallFrame}
    (hf : ∀ v ∈ frame.savedStack, v.WF) {k : Continuation} (hk : k.WF) :
    (st.callToWithFrame frame k).WF := by
  have hr := h.regs
  refine ⟨h.stack, ⟨?_, hr.c1, hr.c2, hr.c3, hr.c4, hr.c5, hr.c7⟩, hk, h.committedC4, h.committedC5,
    h.libraries⟩
  have hcc := h.cc
  simp only [VmState.callToWithFrame]
  split
  · rename_i code _ _ _ heq
    rw [heq] at hcc
    simp only [Continuation.wf_ordinary] at hcc ⊢
    refine ⟨hcc.1, by simp, ?_, by simpa using hf⟩
    rw [OrdCregs.wf_iff]
    simp [OrdCregs.empty, hr.c0]
  · simp

theorem VmState.WF.callTo {st : VmState} (h : st.WF) {k : Continuation} (hk : k.WF) :
    (st.callTo k).WF :=
  h.callToWithFrame (by simp [CallFrame.identity]) hk

theorem tupleExtendSetIndex_WF {t : Array Value} (ht : ∀ v ∈ t, v.WF) {idx : Nat} {v : Value}
    (hv : v.WF) : ∀ x ∈ (tupleExtendSetIndex t idx v).1, x.WF := by
  unfold tupleExtendSetIndex
  split
  · exact WF.forall_mem_set! ht hv _
  · split
    · exact ht
    · refine WF.forall_mem_set! ?_ hv _
      simp only [Array.forall_mem_append, Array.forall_mem_replicate]
      exact ⟨ht, .inr Value.WF.null⟩

/-! ## Continuations (data) -/

theorem Continuation.WF.forceCdata {k : Continuation} (h : k.WF) : k.forceCdata.WF := by
  unfold Continuation.forceCdata
  split <;> simp_all [OrdCdata.empty]

theorem OrdCregs.WF.defineFromValue {cr cr' : OrdCregs} (h : cr.WF) {idx : Nat} {v : Value}
    (hv : v.WF) {silent : Bool} (hd : cr.defineFromValue idx v silent = .ok cr') : cr'.WF := by
  rw [OrdCregs.wf_iff] at h ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h7⟩ := h
  unfold OrdCregs.defineFromValue at hd
  split at hd <;> (try simp only [Value.wf_cont, Value.wf_cell, Value.wf_tuple] at hv) <;>
    (repeat' split at hd) <;> (try cases hd) <;> simp_all

theorem Continuation.WF.defineCtr {k k' : Continuation} (h : k.WF) {idx : Nat} {v : Value}
    (hv : v.WF) {silent : Bool} (hd : k.defineCtr idx v silent = .ok k') : k'.WF := by
  have hf := h.forceCdata
  unfold Continuation.defineCtr at hd
  simp only [bind, Except.bind, pure, Except.pure] at hd
  split at hd
  · rename_i heq
    rw [heq] at hf
    simp only [Continuation.wf_ordinary] at hf
    split at hd
    · cases hd
    · rename_i cr hcr
      cases hd
      exact (Continuation.wf_ordinary _ _ _ _).mpr
        ⟨hf.1, hf.2.1, hf.2.2.1.defineFromValue hv hcr, hf.2.2.2⟩
  · rename_i heq
    rw [heq] at hf
    simp only [Continuation.wf_envelope] at hf
    split at hd
    · cases hd
    · rename_i cr hcr
      cases hd
      exact (Continuation.wf_envelope _ _ _).mpr ⟨hf.1, hf.2.1.defineFromValue hv hcr, hf.2.2⟩
  · cases hd; exact hf

/-! ## Registers, exceptions and jumps (VM monad) -/

@[spec] theorem VM.throwToHandler_spec (raise : VmState → VmState)
    (hr : ∀ st, st.WF → (raise st).WF) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.throwToHandler raise ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.throwToHandler]
  all_goals wf_vc

@[spec] theorem VM.unimplementedInstr_spec {α : Type} (id : InstrId) (msg : String) :
    ⦃fun st => ⌜st.WF⌝⦄ (VM.unimplementedInstr id msg : VM α)
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.unimplementedInstr]

@[spec] theorem VM.getUnpackedConfigTuple_spec :
    ⦃fun st => ⌜st.WF⌝⦄ VM.getUnpackedConfigTuple
      ⦃post⟨fun t st => ⌜st.WF ∧ ∀ v ∈ t, v.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.getUnpackedConfigTuple]
  all_goals wf_vc

@[spec] theorem VM.getMsgPrices_spec (mc : Bool) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.getMsgPrices mc ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.getMsgPrices]
  all_goals wf_vc

@[spec] theorem VM.getGasPrices_spec (mc : Bool) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.getGasPrices mc ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.getGasPrices]
  all_goals wf_vc

@[spec] theorem VM.execNullSwapIf_spec (cond : Bool) (depth count : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.execNullSwapIf cond depth count
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.execNullSwapIf] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

end TvmLean

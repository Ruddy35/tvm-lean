import TvmLean.Proofs.WF.Monad
import TvmLean.Proofs.WF.Decode

/-!
# A step keeps the VM state well-formed

`VmState.WF.stepWith`: one step of the VM (`VmState.stepWith exec`) keeps `VmState.WF`, provided
`exec` keeps it for every well-formed instruction (`ExecWF exec`); `VmState.WF.runWith`: so does a
run, its commit of c4 and c5 included. Everything that is not an instruction is proved here: the
jump into a continuation that is not ordinary (`quit`, `excQuit`, the loop continuations,
`pushInt`, `envelope`), entering an ordinary continuation (its saved registers and closure stack,
`VmState.WF.applyCregsCdata`), the implicit `RET` and `JMPREF` (with the library the reference may
load), the decoding of the next instruction (`decodeCp0WithBits_WF`: the instruction and the rest of
the code are well-formed), exceptions (`VmState.WF.raiseException`: the jump to `c2`), running out
of gas, and the reruns of a step that refuses libraries (`max_library_loads`).

`execInstr_WF`: `execInstr` keeps states well-formed if each of its 14 family handlers does
(`FamilyWF`: the handler keeps them when its fallback `next` does); `VmState.WF.step` and
`VmState.WF.run` then hold for the VM itself. The families proved are in `TvmLean/Proofs/WF/Exec/`.

## How to discharge a family

A family `execInstrX` (`TvmLean/Semantics/Exec/X.lean`) chains handlers `execInstrXY i next`, one
per file under `Exec/X/`, each `match i with | <its instructions> => <its code> | _ => next`.

1. In a new module `TvmLean/Proofs/WF/Exec/X.lean` (importing this one; a root of `TvmLeanProofs`
   in `lakefile.lean`; with `set_option mvcgen.warning false`), prove for every handler
   ```
   theorem execInstrXY_WF : FamilyWF execInstrXY := by
     intro i next hi hnext
     mvcgen [execInstrXY, hnext]
     all_goals wf_vc
   ```
   `mvcgen` unfolds the handler, splits its `match`es and `if`s, and replaces the VM operations by
   their specifications (`@[spec]`, `Monad.lean`), `next` by `hnext`; `wf_vc` closes the conditions
   left (each a state or value that must be well-formed, from hypotheses that others are).
2. When something is left:
   * a `for` loop in the VM monad: `mvcgen [...] invariants` followed by one bullet
     `· post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩` per invariant goal (the error message of
     `mvcgen` says how many);
   * a value computed by a loop in `Id.run` (an array of values, ...): `WF.id_forIn_range` with
     the invariant `fun a => ∀ v ∈ a, v.WF`, after `extract_lets` names it;
   * a cell, slice or builder the handler builds: the lemmas of `Defs.lean` (`Cell.mkOrdinary_WF`,
     `Slice.advanceBits_WF'`, `Slice.toCellRemaining_WF`, `Builder.append_WF`,
     `Builder.storeBits_WF'`, `Builder.pushRef_WF'`, `Builder.finalize_WF`, ...) passed to
     `wf_vc [...]` or applied by hand; the checks the handler makes (`canExtendBy`, `haveBits`) are
     hypotheses of the condition (`Builder.canExtendBy_iff`, `Slice.haveBits_iff`);
   * a cell or slice the instruction carries: `hi : i.WF`; `simp only [Instr.WF] at hi` once
     `mvcgen` has substituted `i`;
   * an operation several handlers share (a helper of the family): prove its `@[spec]` triple
     first, as in `Monad.lean`, and `mvcgen` uses it; a `private def` helper cannot be named from
     another module: `unfold_private M f` unfolds it in the goal, `private% M f` names it in the
     statement of its specification (`M` the module, `f` the full name);
   * a helper that computes on long bit strings (`intToBitsTwos n 257`, ...): `mvcgen` may evaluate
     it; raise `maxRecDepth`, or `generalize` it in a hand-made specification;
   * a hash (`Cell.hashBytes`, `CellLevelInfo.getHash`), or an integer computed from one that
     `VM.pushIntQuiet` range-checks: `mvcgen`, and then the kernel, would compute it; bind the steps
     by hand (`Triple.bind`, `VM.spec_mono` of `Cells.lean`), `generalize` the hash or the integer,
     and close with the specifications (`execCellOpChashI_WF`, `HASHBU` in `execInstrCellExt_WF`);
   * a join point taking a pair or an `Except` and matching on it (the code after a `match` that
     binds several values): `mvcgen` leaves `wp⟦jp ...⟧`; name it with `extract_lets`, prove
     `∀ p, ⦃...⦄ jp p ⦃...⦄` by `cases p`, `simp only [jp]` and `mvcgen`, `clear_value` it, and
     close what `mvcgen` leaves with `refine hjp _ _ ?_` (`execInstrCellStIntVar_WF`, `XLOAD`);
   * a loop whose body has a `try ... catch` and a `break` (the body ends in a match on
     `DoResultSBC`): `mvcgen` leaves that match and may build a term the kernel rejects
     (`(kernel) application type mismatch`); bind the steps by hand, take the loop with
     `VM.forIn_range_WF` and the result of the body apart with `rcases` before `mvcgen`
     (`VM.execSdataSize_spec`, `Exec/Misc.lean`);
   * a long handler: `set_option maxHeartbeats 4000000` for the file (not `in`: the equations of
     the handler `mvcgen` unfolds are built with the options of the file); compile a family file
     single-threaded under a memory cap (`ulimit -v 10000000`; the resident memory stays under 3 GB
     but Lean reserves much more address space).
3. Chain the handlers as the family does:
   ```
   theorem execInstrX_WF : FamilyWF execInstrX := by
     intro i next hi hnext
     unfold execInstrX
     exact execInstrXA_WF i _ hi <| execInstrXB_WF i _ hi <| ... <| hnext
   ```
   and pass it to `execInstr_WF`.

Done: Stack, Arith, Cell, CellOp (`wf_cells` of `Cells.lean`: `wf_vc` with the lemmas on the
cells, slices and builders instructions build), Exception (`Continuation.WF.defineC0`,
`Continuation.WF.defineC2`), Debug, Tuple, Misc (`VM.forIn_range_WF`: a loop in the VM monad
whose body `mvcgen` cannot take). Left: Cont, Flow (with `RUNVM`, which runs a child VM with
`execInstr`: `VmState.WF.runWith` applies), TonEnv, Crypto, Msg, Dict. The VM operations of those families without a specification yet: `VM.call`,
`VM.callComputeStacks`, `VM.extractCc` (mvcgen unfolds them; their conditions need the
continuation lemmas of `Monad.lean`), the dictionary functions (`Library.lean` has the lookup; the
setters build cells), the cell serialization of messages and actions.
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

/-! ## Private helpers of the instruction files -/

open Lean Elab Tactic Meta in
/-- `unfold_private M f` unfolds in the goal the private definition `f` of the module `M` (a helper
of an instruction file, `private def`, which cannot be named from another module), so that `mvcgen`
sees its code. -/
elab "unfold_private " m:ident n:ident : tactic => do
  let full := Name.mkNum (`_private ++ m.getId) 0 ++ n.getId
  unless (← getEnv).contains full do
    throwError "unfold_private: no private definition {n.getId} in {m.getId}"
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let t' ← deltaExpand t (· == full)
    replaceMainGoal [← g.replaceTargetDefEq t'.headBeta]

open Lean Elab Term in
/-- `private% M f`: the private definition `f` of the module `M`, as a term (to state its
specification). -/
elab "private% " m:ident n:ident : term => do
  let full := Name.mkNum (`_private ++ m.getId) 0 ++ n.getId
  let some ci := (← getEnv).find? full
    | throwError "private%: no private definition {n.getId} in {m.getId}"
  return mkConst full (ci.levelParams.map fun _ => levelZero)

/-! ## Loops computing values -/

/-- A loop over a range in `Id` keeps an invariant every step keeps (for the values instructions
compute with `Id.run do ... for ...`). -/
theorem WF.id_forIn_range {β : Type} (P : β → Prop) {r : Std.Range} {init : β}
    {f : Nat → β → Id (ForInStep β)} (h0 : P init)
    (hf : ∀ i b, P b → P (f i b).run.value) : P (Id.run (forIn r init f)) := by
  rw [Std.Range.forIn_eq_forIn_range']
  generalize List.range' r.start r.size r.step = l
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih =>
    simp only [List.forIn_cons]
    have := hf a init h0
    cases hfa : f a init with
    | done b => rw [hfa] at this; exact this
    | yield b => rw [hfa] at this; exact ih this

/-! ## The obligations -/

/-- What an instruction semantics owes: every well-formed instruction keeps the state
well-formed (`VM.KeepsWF`: also when it throws). -/
def ExecWF (exec : Instr → VM Unit) : Prop :=
  ∀ i, i.WF → (exec i).KeepsWF

/-- What a family handler (`execInstrStack`, `execInstrCell`, ...: an instruction and the handler
of the instructions it does not take) owes: it keeps the state well-formed when its fallback does. -/
def FamilyWF (h : Instr → VM Unit → VM Unit) : Prop :=
  ∀ i next, i.WF → next.KeepsWF → (h i next).KeepsWF

/-! ## State functions of the step -/

theorem VmState.WF.outOfGasHalt {st : VmState} (h : st.WF) : st.outOfGasHalt.state.WF := by
  unfold VmState.outOfGasHalt StepResult.state
  exact ⟨by simp, h.regs, h.cc, h.committedC4, h.committedC5, h.libraries⟩

@[simp] theorem VmState.countJump_WF (st : VmState) : st.countJump.WF ↔ st.WF := by
  unfold VmState.countJump
  dsimp only
  split
  · rw [VmState.consumeGas_WF]; exact VmState.wf_congr rfl rfl rfl rfl rfl
  · exact VmState.wf_congr rfl rfl rfl rfl rfl

theorem VmState.WF.jumped {st : VmState} (h : st.WF) : (VmState.jumped st).state.WF := by
  unfold VmState.jumped
  dsimp only
  split
  · exact ((VmState.countJump_WF st).mpr h).outOfGasHalt
  · exact (VmState.countJump_WF st).mpr h

theorem VmState.WF.withSteps {st : VmState} (h : st.WF) (n : Nat) :
    ({ st with steps := n } : VmState).WF :=
  h.of_eq rfl rfl rfl rfl rfl

theorem VmState.WF.withChainJumps {st : VmState} (h : st.WF) (n : Nat) :
    ({ st with chainJumps := n } : VmState).WF :=
  h.of_eq rfl rfl rfl rfl rfl

theorem OrdCdata.WF.entered {cdata : OrdCdata} (h : cdata.WF) (st : VmState) :
    (st.enteredCdata cdata).WF := by
  unfold VmState.enteredCdata
  split
  · exact h
  · exact OrdCdata.empty_WF

/-- The saved control registers of a continuation and its closure stack, applied to a
well-formed state. -/
theorem VmState.WF.applyCregsCdata {st : VmState} (h : st.WF) {cregs : OrdCregs} {cdata : OrdCdata}
    (hc : cregs.WF) (hd : cdata.WF) : (st.applyCregsCdata cregs cdata).WF := by
  rw [OrdCregs.wf_iff] at hc
  obtain ⟨h0, h1, h2, h3, h4, h5, h7⟩ := hc
  have hr := h.regs
  rw [Regs.wf_iff] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r7⟩ := hr
  rw [OrdCdata.wf_iff] at hd
  unfold VmState.applyCregsCdata
  extract_lets regs0 regs1 regs2 regs3 regs4 regs5 regs6 regs7 st1 stack0
  have k0 : regs0.WF := (Regs.wf_iff _).mpr ⟨r0, r1, r2, r3, r4, r5, r7⟩
  have k1 : regs1.WF := by
    simp only [regs1]; split <;> simp only [Regs.wf_iff] at * <;> simp_all
  have k2 : regs2.WF := by
    simp only [regs2]; split <;> simp only [Regs.wf_iff] at * <;> simp_all
  have k3 : regs3.WF := by
    simp only [regs3]; split <;> simp only [Regs.wf_iff] at * <;> simp_all
  have k4 : regs4.WF := by
    simp only [regs4]; split <;> simp only [Regs.wf_iff] at * <;> simp_all
  have k5 : regs5.WF := by
    simp only [regs5]; split <;> simp only [Regs.wf_iff] at * <;> simp_all
  have k6 : regs6.WF := by
    simp only [regs6]; split <;> simp only [Regs.wf_iff] at * <;> simp_all
  have k7 : regs7.WF := by
    simp only [regs7]; split <;> simp only [Regs.wf_iff] at * <;> simp_all
  have hs1 : st1.WF := h.withRegs k7
  have hst : ∀ v ∈ stack0, v.WF := hs1.stack
  clear_value regs0 regs1 regs2 regs3 regs4 regs5 regs6 regs7
  generalize hp : (if decide (0 ≤ cdata.nargs) = true then _ else _) = p
  obtain ⟨stack1, truncated⟩ := p
  have hs1' : ∀ v ∈ stack1, v.WF := by
    split at hp
    · split at hp <;> cases hp
      · exact WF.forall_mem_extract hst _ _
      · exact hst
    · cases hp; exact hst
  dsimp only
  have hst1' : ({ st1 with stack := stack1 } : VmState).WF := hs1.withStack hs1'
  split
  · split
    · exact (VmState.consumeStackGas_WF _ _).mpr hst1'
    · exact hst1'
  · rw [VmState.consumeStackGas_WF]
    exact hs1.withStack (by simp only [Array.forall_mem_append]; exact ⟨hd, hs1'⟩)

end TvmLean

namespace TvmLean

theorem VmState.WF.excHandlerJump {st : VmState} (h : st.WF) :
    (match st.cc with
      | .ordinary code saved cregs cdata =>
          { st.applyCregsCdata OrdCregs.empty cdata with cc := .ordinary code saved cregs OrdCdata.empty }
      | .envelope ext cregs cdata =>
          { st.applyCregsCdata OrdCregs.empty cdata with cc := .envelope ext cregs OrdCdata.empty }
      | _ => st).WF := by
  have hcc := h.cc
  split
  · rename_i code saved cregs cdata heq
    rw [heq] at hcc
    simp only [Continuation.wf_ordinary] at hcc
    exact (h.applyCregsCdata OrdCregs.empty_WF hcc.2.2.2).withCc
      ((Continuation.wf_ordinary _ _ _ _).mpr ⟨hcc.1, hcc.2.1, hcc.2.2.1, OrdCdata.empty_WF⟩)
  · rename_i ext cregs cdata heq
    rw [heq] at hcc
    simp only [Continuation.wf_envelope] at hcc
    exact (h.applyCregsCdata OrdCregs.empty_WF hcc.2.2).withCc
      ((Continuation.wf_envelope _ _ _).mpr ⟨hcc.1, hcc.2.1, OrdCdata.empty_WF⟩)
  · exact h

/-- C++ `run_inner` handling an exception: the jump to the handler `c2` keeps the state
well-formed. -/
theorem VmState.WF.raiseException {st : VmState} (h : st.WF) (e : Int) :
    (st.raiseException e).state.WF := by
  unfold VmState.raiseException
  extract_lets st' stExc stJ
  have h' : st'.WF := h.withSteps _
  have hExc : stExc.WF := (VmState.consumeGas_WF _ _).mpr (h'.throwException e)
  have hJ : stJ.WF := hExc.excHandlerJump
  split
  · exact hExc.outOfGasHalt
  · split
    · exact hExc
    · split
      · exact hJ.outOfGasHalt
      · exact hJ.withChainJumps 0

theorem VmState.WF.withC0Cc {st : VmState} (h : st.WF) {k c : Continuation} (hk : k.WF) (hc : c.WF) :
    ({ st with regs := { st.regs with c0 := k }, cc := c } : VmState).WF := by
  have hr := h.regs
  exact ⟨h.stack, ⟨hk, hr.c1, hr.c2, hr.c3, hr.c4, hr.c5, hr.c7⟩, hc, h.committedC4, h.committedC5,
    h.libraries⟩

/-- The run of a VM action that keeps states well-formed ends in a well-formed state. -/
theorem VM.Keeps.run_state {α : Type} {m : VM α} {Q : α → Prop} (h : m.Keeps Q) {st : VmState}
    (hs : st.WF) {r : Except Excno α} {st' : VmState} (hr : m.run st = (r, st')) : st'.WF := by
  have := (h.run hs).1
  rw [hr] at this
  exact this

/-- The state after a VM action whose specification keeps states well-formed. -/
theorem VM.run_state_of_spec {α : Type} {m : VM α} {Q : α → VmState → Prop}
    (h : ⦃fun st => ⌜st.WF⌝⦄ m ⦃post⟨fun a st => ⌜Q a st⌝, fun _ st => ⌜st.WF⌝⟩⦄)
    (hQ : ∀ a st, Q a st → st.WF) {st : VmState} (hs : st.WF) {r : Except Excno α} {st' : VmState}
    (hr : m.run st = (r, st')) : st'.WF := by
  have := VM.triple_run h st hs
  rw [hr] at this
  cases r with
  | ok a => exact hQ a st' this
  | error e => exact this

@[simp] theorem StepResult.state_continue (st : VmState) : (StepResult.continue st).state = st := rfl
@[simp] theorem StepResult.state_halt (n : Int) (st : VmState) : (StepResult.halt n st).state = st := rfl

set_option maxHeartbeats 1000000 in
/-- One step keeps the state well-formed, if every well-formed instruction does (`ExecWF`): the
jumps into continuations, the loop continuations, the implicit `RET` and `JMPREF`, the decoding of
the next instruction, the exceptions and running out of gas. -/
theorem VmState.WF.stepOnceWith {exec : Instr → VM Unit} (hexec : ExecWF exec) {st : VmState}
    (h : st.WF) : (st.stepOnceWith exec).state.WF := by
  have hcc := h.cc
  unfold VmState.stepOnceWith
  split
  · -- quit
    dsimp only
    split
    · exact ((VmState.countJump_WF st).mpr h).outOfGasHalt
    · exact (VmState.countJump_WF st).mpr h
  · -- excQuit
    extract_lets action
    have ha : ⦃fun st => ⌜st.WF⌝⦄ action ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
      simp only [action]
      mvcgen
      all_goals wf_vc
    rcases hr : action.run st with ⟨res, st'⟩
    have h' : st'.WF := VM.run_state_of_spec ha (fun _ _ h => h) h hr
    dsimp only
    split
    · exact ((VmState.countJump_WF _).mpr h').outOfGasHalt
    · exact (VmState.countJump_WF _).mpr h'
  · -- whileCond
    rename_i cond body after heq
    rw [heq] at hcc
    simp only [Continuation.wf_whileCond] at hcc
    obtain ⟨hc, hb, ha⟩ := hcc
    split
    · next e st' hm =>
      exact (VM.run_state_of_spec VM.popBool_spec (fun _ _ h => h) h hm).raiseException _
    · next st' hm =>
      have h' := VM.run_state_of_spec VM.popBool_spec (fun _ _ h => h) h hm
      split
      · exact (h'.withCc hb).jumped
      · exact (h'.withC0Cc ((Continuation.wf_whileBody _ _ _).mpr ⟨hc, hb, ha⟩) hb).jumped
    · next st' hm =>
      exact ((VM.run_state_of_spec VM.popBool_spec (fun _ _ h => h) h hm).withCc ha).jumped
  · -- whileBody
    rename_i cond body after heq
    rw [heq] at hcc
    simp only [Continuation.wf_whileBody] at hcc
    obtain ⟨hc, hb, ha⟩ := hcc
    split
    · exact (h.withCc hc).jumped
    · exact (h.withC0Cc ((Continuation.wf_whileCond _ _ _).mpr ⟨hc, hb, ha⟩) hc).jumped
  · -- untilBody
    rename_i body after heq
    rw [heq] at hcc
    simp only [Continuation.wf_untilBody] at hcc
    obtain ⟨hb, ha⟩ := hcc
    split
    · next e st' hm =>
      exact (VM.run_state_of_spec VM.popBool_spec (fun _ _ h => h) h hm).raiseException _
    · next st' hm =>
      exact ((VM.run_state_of_spec VM.popBool_spec (fun _ _ h => h) h hm).withCc ha).jumped
    · next st' hm =>
      have h' := VM.run_state_of_spec VM.popBool_spec (fun _ _ h => h) h hm
      split
      · exact (h'.withCc hb).jumped
      · exact (h'.withC0Cc ((Continuation.wf_untilBody _ _).mpr ⟨hb, ha⟩) hb).jumped
  · -- repeatBody
    rename_i body after count heq
    rw [heq] at hcc
    simp only [Continuation.wf_repeatBody] at hcc
    obtain ⟨hb, ha⟩ := hcc
    split
    · exact (h.withCc ha).jumped
    · split
      · exact (h.withCc hb).jumped
      · exact (h.withC0Cc ((Continuation.wf_repeatBody _ _ _).mpr ⟨hb, ha⟩) hb).jumped
  · -- againBody
    rename_i body heq
    rw [heq] at hcc
    simp only [Continuation.wf_againBody] at hcc
    split
    · exact (h.withCc hcc).jumped
    · exact (h.withC0Cc ((Continuation.wf_againBody _).mpr hcc) hcc).jumped
  · -- pushInt
    rename_i n next heq
    rw [heq] at hcc
    simp only [Continuation.wf_pushInt] at hcc
    refine VmState.WF.jumped ⟨?_, h.regs, hcc, h.committedC4, h.committedC5, h.libraries⟩
    simp only [Array.forall_mem_push]
    exact ⟨Value.WF.int _, h.stack⟩
  · -- envelope
    rename_i ext cregs cdata heq
    rw [heq] at hcc
    simp only [Continuation.wf_envelope] at hcc
    obtain ⟨he, hcr, hcd⟩ := hcc
    extract_lets cdata' st'
    have hcd' : cdata'.WF := hcd.entered st
    have h' : st'.WF := h.applyCregsCdata hcr hcd'
    split
    · exact h.raiseException _
    · split
      · exact h'.outOfGasHalt
      · exact (h'.withCc he).jumped
  · -- ordinary
    rename_i code saved cregs cdata heq
    rw [heq] at hcc
    simp only [Continuation.wf_ordinary] at hcc
    obtain ⟨hcode, hsaved, hcr, hcd⟩ := hcc
    extract_lets cdata1 st2 st3 cdata2 st4 st0ret st0ref refCell head opcode24 st0inv decoded
      invalBits
    have hcd1 : cdata1.WF := hcd.entered st
    have h2 : st2.WF := h.applyCregsCdata hcr hcd1
    have h3 : st3.WF := (VmState.countJump_WF _).mpr h2
    have hcd2 : cdata2.WF := by simp [cdata2]
    have h4 : st4.WF :=
      ⟨h3.stack, h3.regs, (Continuation.wf_ordinary _ _ _ _).mpr ⟨hcode, hsaved, OrdCregs.empty_WF, hcd2⟩,
        h3.committedC4, h3.committedC5, h3.libraries⟩
    have hret : st0ret.WF := (VmState.consumeGas_WF _ _).mpr h4
    have href : st0ref.WF := (VmState.consumeGas_WF _ _).mpr h4
    have hrefCell : refCell.WF := hcode.ref! _
    have hinv : st0inv.WF := (VmState.consumeGas_WF _ _).mpr h4
    have hdec : ∀ i n r, decoded = .ok (i, n, r) → i.WF ∧ r.WF := by
      intro i n r hd
      simp only [decoded] at hd
      split at hd
      · exact decodeCp0WithBits_WF hcode hd
      · cases hd
    clear_value decoded
    split
    · exact h.raiseException _
    · split
      · exact h2.outOfGasHalt
      · split
        · exact h3.outOfGasHalt
        · split
          · split
            · -- implicit RET
              split
              · exact hret.outOfGasHalt
              · split
                next res st1 hm =>
                have h1 : st1.WF := VM.run_state_of_spec (VM.ret_spec _) (fun _ _ h => h) hret hm
                split
                · split
                  · exact h1.outOfGasHalt
                  · exact h1
                · exact h1.raiseException _
            · -- implicit JMPREF
              split
              · exact href.outOfGasHalt
              · split
                · split
                  next st1 exhausted hm =>
                  have h1 : st1.WF := by
                    have := (VmState.registerCellLoads_WF st0ref
                      (.cell refCell :: (st0ref.libraryLoads refCell).toList)).mpr href
                    rw [hm] at this
                    exact this
                  split
                  · exact h1.outOfGasHalt
                  · split
                    · next root hroot =>
                      have hr : root.WF := libraryResolveLoads_WF h1.libraries hrefCell hroot
                      split
                      · exact h1.outOfGasHalt
                      · exact h1.withCc ((Continuation.wf_ordinary _ _ _ _).mpr
                          ⟨Slice.ofCell_WF hr, by simp, OrdCregs.empty_WF, OrdCdata.empty_WF⟩)
                    · exact h1.raiseException _
                · exact href.raiseException _
          · split
            · split
              · exact hinv.outOfGasHalt
              · exact hinv.raiseException _
            · split
              · -- an invalid opcode
                extract_lets st0
                have h0 : st0.WF := by
                  simp only [st0]
                  split
                  · exact (VmState.consumeGas_WF _ _).mpr h4
                  · exact h4
                split
                · exact h0.outOfGasHalt
                · exact h0.raiseException _
              · -- an instruction
                next _ instr totBits rest =>
                obtain ⟨hi, hrest⟩ := hdec instr totBits rest rfl
                extract_lets st0 stGas
                have h0 : st0.WF := h4.withCc ((Continuation.wf_ordinary _ _ _ _).mpr
                  ⟨hrest, by simp, OrdCregs.empty_WF, OrdCdata.empty_WF⟩)
                have hg : stGas.WF := (VmState.consumeGas_WF _ _).mpr h0
                split
                · exact hg.outOfGasHalt
                · split
                  next res st1 hm =>
                  have h1 : st1.WF := (hexec instr hi).run_state hg hm
                  split
                  · split
                    · exact h1.outOfGasHalt
                    · exact h1
                  · split
                    · exact h1.outOfGasHalt
                    · exact h1.raiseException _

theorem StepResult.mapState_state (f : VmState → VmState) (r : StepResult) :
    (r.mapState f).state = f r.state := by
  cases r <;> rfl

theorem VmState.WF.withLibrarySets {st : VmState} (h : st.WF) (a b : Array BitString) :
    ({ st with librariesRefused := a, librariesMissed := b } : VmState).WF :=
  h.of_eq rfl rfl rfl rfl rfl

/-- The runs of a step refusing libraries (`max_library_loads`) keep the state well-formed. -/
theorem VmState.WF.stepRefusingWith {exec : Instr → VM Unit} (hexec : ExecWF exec) {st : VmState}
    (h : st.WF) : ∀ (refused : Array BitString) (n : Nat),
      (st.stepRefusingWith exec refused n).state.WF
  | refused, 0 => by
    rw [VmState.stepRefusingWith, StepResult.mapState_state]
    exact ((h.withLibrarySets _ _).stepOnceWith hexec).withLibrarySets _ _
  | refused, n + 1 => by
    rw [VmState.stepRefusingWith]
    split
    · rw [StepResult.mapState_state]
      exact ((h.withLibrarySets _ _).stepOnceWith hexec).withLibrarySets _ _
    · exact VmState.WF.stepRefusingWith hexec h _ n

/-- One step of the VM keeps the state well-formed, if every well-formed instruction does. -/
theorem VmState.WF.stepWith {exec : Instr → VM Unit} (hexec : ExecWF exec) {st : VmState}
    (h : st.WF) : (st.stepWith exec).state.WF := by
  unfold VmState.stepWith
  split
  · exact h.stepOnceWith hexec
  · exact h.stepRefusingWith hexec _ _

/-- A run of the VM, its commit of c4 and c5 included, keeps the state well-formed. -/
theorem VmState.WF.runWith {exec : Instr → VM Unit} (hexec : ExecWF exec) :
    ∀ (fuel : Nat) {st : VmState}, st.WF → (st.runWith exec fuel).state.WF
  | 0, st, h => by rw [VmState.runWith]; exact h
  | fuel + 1, st, h => by
    rw [VmState.runWith]
    have hs := h.stepWith hexec
    split
    · rename_i st' heq
      rw [heq] at hs
      exact VmState.WF.runWith hexec fuel hs
    · rename_i n st' heq
      rw [heq] at hs
      dsimp only
      split
      · have hc := hs.tryCommit
        split
        · exact hc
        · exact hc.withStack (by simp)
      · exact hs

/-! ## The instruction dispatcher -/

theorem VM.unimplementedInstr_keeps (id : InstrId) (msg : String) :
    (VM.unimplementedInstr id msg : VM Unit).KeepsWF := by
  mvcgen [VM.unimplementedInstr]
  all_goals exact fun h => h

/-- `execInstr` keeps states well-formed if each family handler does. -/
theorem execInstr_WF (hStack : FamilyWF execInstrStack) (hCont : FamilyWF execInstrCont)
    (hCell : FamilyWF execInstrCell) (hFlow : FamilyWF execInstrFlow)
    (hArith : FamilyWF execInstrArith) (hTuple : FamilyWF execInstrTuple)
    (hCellOp : FamilyWF execInstrCellOp) (hTonEnv : FamilyWF execInstrTonEnv)
    (hCrypto : FamilyWF execInstrCrypto) (hMsg : FamilyWF execInstrMsg)
    (hMisc : FamilyWF execInstrMisc) (hDebug : FamilyWF execInstrDebug)
    (hException : FamilyWF execInstrException) (hDict : FamilyWF execInstrDict) :
    ExecWF execInstr := by
  intro i hi
  unfold execInstr
  exact hStack i _ hi <| hCont i _ hi <| hCell i _ hi <| hFlow i _ hi <| hArith i _ hi <|
    hTuple i _ hi <| hCellOp i _ hi <| hTonEnv i _ hi <| hCrypto i _ hi <| hMsg i _ hi <|
    hMisc i _ hi <| hDebug i _ hi <| hException i _ hi <| hDict i _ hi <|
    VM.unimplementedInstr_keeps _ _

/-- A step of the VM keeps the state well-formed, given the obligations of the families. -/
theorem VmState.WF.step (hexec : ExecWF execInstr) {st : VmState} (h : st.WF) :
    st.step.state.WF :=
  h.stepWith hexec

/-- A run of the VM keeps the state well-formed, given the obligations of the families. -/
theorem VmState.WF.run (hexec : ExecWF execInstr) (fuel : Nat) {st : VmState} (h : st.WF) :
    (st.run fuel).state.WF :=
  VmState.WF.runWith hexec fuel h

end TvmLean

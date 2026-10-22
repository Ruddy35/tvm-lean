import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Contracts.Wallet3Run.Tactic

/-!
# Instructions on unknown cells: the step of a framed instruction

Some instructions load a cell the run knows nothing about: `CTOS` of the inbound message
(`in_msg_full` is any cell of the stack the compute phase starts with: an ordinary cell, a library
cell whose library is loaded, refused or missing, another exotic cell), a dictionary lookup in a
dictionary of unknown cells (`TvmLean/Proofs/Exec/FramedDict.lean`). What the instruction does
depends on the cell's kind and on the library collections; a run cannot compute it. What it may
change is known: the stack, the gas, the cells and libraries loaded, and the libraries C++ refuses
(`librariesMissed`, after which `VmState.stepWith` runs the step again with them refused, C++
`load_library` with `max_library_loads`, vm.cpp:644-656).

* `Dead r`: a step result after which no run commits (`dead_halt`: a halt that is not a normal
  exit; `dead_excQuit`: the exception handler `excQuit` about to end the run with an exception of
  code at least 2; `raise_dead`: an exception raised with `c2 = excQuit`).
* `ExecFramed i Ok st`: the run of `i` from `st` changes nothing else (`Frame`), leaves a stack
  satisfying `Ok` when it succeeds, raises an exception of code 2 or more when it fails, and notes
  no refused library without `max_library_loads`.
* `runWith_framed`: a run from a state about to run such an instruction (an ordinary continuation
  without saved registers or closure data, `c2` the handler `excQuit`, nothing committed) commits
  nothing, or goes on from the state after the instruction (`after`) with any stack satisfying
  `Ok`, any gas, any loaded cells and libraries, whatever the runs of the step again for refused
  libraries did (`stepRefusing_good`).
* `ctos_framed`, `runWith_ctos` and the tactic `vm_ctos_any`: `CTOS` of any cell (`VM.loadCellSlice`
  changes only what a load changes, `loadCellSlice_frame`, and fails only with out of gas or
  cell_und, `libraryResolveLoadsAux_error`).
* `VmState.raiseDead`, `VmState.instrEnd_error_dead`, `dead_stepFinish_raiseDead`: an exception of an
  instruction kept under a name `vm_run` does not unfold, for runs whose exceptions all end the run
  (`c2 = excQuit`): its expansion (the handler's state and gas checks, the step of `excQuit`) is
  not computed, and the path is closed at once.
* `vm_clear_unused`: the context of a run after a framed instruction, cleared of the hypotheses
  about the state before it.
-/

namespace TvmLean.Framed

/-- A step result after which no run commits, whatever its fuel (`VmState.runCont`). -/
def Dead (r : StepResult) : Prop := ∀ fuel, (VmState.runCont execInstr fuel r).state.cstate.committed = false

/-- A halt that is not a normal exit (-1, -2) commits nothing (nothing was committed before). -/
theorem dead_halt {ec : Int} {st : VmState} (h1 : ec ≠ -1) (h2 : ec ≠ -2) (hc : st.cstate.committed = false) :
    Dead (.halt ec st) := by
  intro fuel
  simp only [VmState.runCont_halt, VmState.haltResult, h1, h2, or_self, if_false, StepResult.state_halt, hc]

/-- The step of the exception handler `excQuit` with an exception of code at least 2 on the stack:
a halt that is not a normal exit, the committed state and the libraries noted kept. -/
theorem excQuit_step (st : VmState) (e : Int) (hcc : st.cc = .excQuit)
    (hs : st.stack = #[.int (.num 0), .int (.num e)]) (he : 2 ≤ e) :
    ∃ ec st', st.stepOnceWith execInstr = .halt ec st' ∧ ec ≠ -1 ∧ ec ≠ -2 ∧ st'.cstate = st.cstate ∧
      st'.librariesMissed = st.librariesMissed := by
  have hpop : ExceptT.run VM.popInt st = (.ok (.num e), { st with stack := #[.int (.num 0)] }) := by
    rw [VM.run_popInt, hs]; rfl
  unfold VmState.stepOnceWith
  rw [hcc]
  simp only [VM.run_bind, hpop, VM.bindRes_ok]
  have hcj : ∀ s : VmState, s.countJump.cstate = s.cstate ∧ s.countJump.librariesMissed = s.librariesMissed := by
    intro s; simp only [VmState.countJump]; split <;> exact ⟨rfl, rfl⟩
  have key : ∀ (n : Int) (s : VmState), n ≠ 0 → n ≠ 1 → s.cstate = st.cstate → s.librariesMissed = st.librariesMissed →
      ∃ ec st', (if s.countJump.gasExhaustedNow = true then s.countJump.outOfGasHalt else StepResult.halt (~~~n) s.countJump)
        = StepResult.halt ec st' ∧ ec ≠ -1 ∧ ec ≠ -2 ∧ st'.cstate = st.cstate ∧ st'.librariesMissed = st.librariesMissed := by
    intro n s h0 h1 hc hm
    obtain ⟨c1, c2⟩ := hcj s
    split
    · exact ⟨_, _, rfl, by decide, by decide, by rw [← hc, ← c1], by rw [← hm, ← c2]⟩
    · refine ⟨_, _, rfl, ?_, ?_, by rw [← hc, ← c1], by rw [← hm, ← c2]⟩
      · rw [VM.int_complement]; omega
      · rw [VM.int_complement]; omega
  by_cases hr : e < 0 ∨ e > 65535
  · rw [if_pos hr]
    refine key _ _ ?_ ?_ rfl rfl <;> decide
  · rw [if_neg hr]
    refine key e _ ?_ ?_ rfl rfl <;> omega

/-- **The exception handler `excQuit` ends the run without committing** an exception of code at
least 2 (between steps: no library refused or noted). -/
theorem dead_excQuit {st : VmState} {e : Int} (hcc : st.cc = .excQuit)
    (hs : st.stack = #[.int (.num 0), .int (.num e)]) (he : 2 ≤ e) (hc : st.cstate.committed = false)
    (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[]) : Dead (.continue st) := by
  intro fuel
  rw [VmState.runCont_continue]
  cases fuel with
  | zero => exact hc
  | succ n =>
    obtain ⟨ec, st', h1, h2, h3, h4, h5⟩ := excQuit_step st e hcc hs he
    rw [VmState.runWith_succ', VmState.stepWith_unfold _ _ hr hm, h1]
    have hh : ∀ st'' : VmState, st''.cstate = st.cstate →
        (VmState.runCont execInstr n (.halt ec st'')).state.cstate.committed = false :=
      fun st'' hst => dead_halt h2 h3 (by rw [hst]; exact hc) n
    split
    · exact hh st' h4
    · simp only [StepResult.state_halt, h5, hm, Array.isEmpty_empty, if_true, StepResult.mapState_halt]
      exact hh _ h4

/-- `st'` is `st` but for the stack, the gas, the loaded cells, the loaded libraries and the
libraries noted refused in the step (`librariesMissed`). -/
def Frame (st st' : VmState) : Prop :=
  st' = { st with stack := st'.stack, gas := st'.gas, loadedCells := st'.loadedCells,
                  loadedLibraries := st'.loadedLibraries, librariesMissed := st'.librariesMissed }

/-- The run of the instruction `i` from `st` changes only what `Frame` allows, leaves a stack
satisfying `Ok` when it succeeds, raises an exception of code at least 2 when it fails, and notes
no refused library without `max_library_loads`. -/
structure ExecFramed (i : Instr) (Ok : Stack → Prop) (st : VmState) : Prop where
  frame : Frame st (ExceptT.run (execInstr i) st).2
  ok : (ExceptT.run (execInstr i) st).1 = .ok () → Ok (ExceptT.run (execInstr i) st).2.stack
  err : ∀ e, (ExceptT.run (execInstr i) st).1 = .error e → 2 ≤ e.toInt
  none : st.maxLibraryLoads = none → (ExceptT.run (execInstr i) st).2.librariesMissed = st.librariesMissed

/-- The state after a framed instruction run from `st` (the code after it `rest`): `st` with the
stack `s'`, the gas `g`, the loaded cells and libraries `lc ll`, the step counted. -/
def after (st : VmState) (rest : Slice) (s' : Stack) (g : GasLimits) (lc : Array (Array UInt8))
    (ll : Array BitString) : VmState :=
  { st with stack := s', cc := .plain rest, gas := g, loadedCells := lc, loadedLibraries := ll,
            chainJumps := 0, steps := st.steps + 1 }

/-- The libraries of a step cleared (`VmState.stepRefusingWith`, `VmState.stepWith`). -/
abbrev clearLibs (st : VmState) : VmState := { st with librariesRefused := #[], librariesMissed := #[] }

/-- The hypotheses on the state about to run the framed instruction `i` (decoded from `code`, with
`n` bits, the code after it `rest`): an ordinary continuation without saved registers or closure
data, codepage 0, `c2` the handler `excQuit`, nothing committed, and `ExecFramed` from every state
with its stack and registers. -/
structure At (i : Instr) (Ok : Stack → Prop) (st : VmState) (code rest : Slice) : Prop where
  cc : st.cc = .plain code
  cp : st.cp = 0
  bits : code.bitsRemaining ≠ 0
  ver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion
  dec : ∃ n, decodeCp0WithBits code = .ok (i, n, rest)
  chain : st.chainJumps < freeNestedContJump
  c2 : st.regs.c2 = .excQuit
  com : st.cstate.committed = false
  exec : ∀ st0 : VmState, st0.stack = st.stack → st0.regs = st.regs → ExecFramed i Ok st0

theorem outOfGasHalt_dead {st : VmState} (h : st.cstate.committed = false) :
    Dead (st.outOfGasHalt.mapState clearLibs) :=
  dead_halt (by decide) (by decide) h

/-- What one run of the step of a framed instruction gives, the libraries `R` refused. -/
def Good1 (st : VmState) (rest : Slice) (Ok : Stack → Prop) (R : Array BitString) (r : StepResult) : Prop :=
  (∃ s' g lc ll lm, Ok s' ∧
      r = .continue { after st rest s' g lc ll with librariesRefused := R, librariesMissed := lm } ∧
      (st.maxLibraryLoads = none → lm = #[])) ∨
  (Dead (r.mapState clearLibs) ∧ r.state.librariesRefused = R ∧
    (st.maxLibraryLoads = none → r.state.librariesMissed = #[]))


/-- An exception of code at least 2 raised with `c2` the handler `excQuit`, nothing committed:
dead, the libraries of the step kept. -/
theorem raise_dead {st : VmState} {x : Int} (hc2 : st.regs.c2 = .excQuit) (hcom : st.cstate.committed = false)
    (hx : 2 ≤ x) :
    Dead ((st.raiseException x).mapState clearLibs) ∧ (st.raiseException x).state.librariesRefused = st.librariesRefused ∧
      (st.raiseException x).state.librariesMissed = st.librariesMissed := by
  unfold VmState.raiseException
  simp only [VmState.throwException, VmState.consumeGas, VmState.excHandlerNeedsMoreArgs, hc2]
  split
  · exact ⟨outOfGasHalt_dead hcom, rfl, rfl⟩
  · simp only [Bool.false_eq_true, if_false]
    split
    · exact ⟨outOfGasHalt_dead hcom, rfl, rfl⟩
    · exact ⟨dead_excQuit (e := x) rfl rfl hx hcom rfl rfl, rfl, rfl⟩

/-- An exception raised by an instruction (`VmState.raiseException`), under a name `vm_run` does
not unfold: when the handler is `excQuit` the run ends there without committing
(`dead_stepFinish_raiseDead`), and the exception's expansion (the handler's state, its gas checks,
the step of `excQuit`) is not computed. -/
def _root_.TvmLean.VmState.raiseDead (st : VmState) (x : Int) : StepResult := st.raiseException x

/-- `VmState.instrEnd` of an exception, the exception kept as `VmState.raiseDead` (a pre-rewrite,
`↓`, for `vm_run`). -/
theorem _root_.TvmLean.VmState.instrEnd_error_dead (e : Excno) (st : VmState) :
    VmState.instrEnd (.error e, st) = if e = .outOfGas then st.outOfGasHalt else st.raiseDead e.toInt := rfl

/-- **An exception the handler `excQuit` ends** after a step between steps (`VmState.stepFinish`,
the step whatever `max_library_loads` is) commits nothing. -/
theorem dead_stepFinish_raiseDead (S st : VmState) (x : Int) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hx : 2 ≤ x) (hr : st.librariesRefused = #[])
    (hm : st.librariesMissed = #[]) : Dead (VmState.stepFinish execInstr S (st.raiseDead x)) := by
  obtain ⟨hd, h1, h2⟩ := raise_dead (x := x) hc2 hcom hx
  unfold VmState.stepFinish VmState.raiseDead
  split
  · have e : (st.raiseException x).mapState clearLibs = st.raiseException x := by
      apply StepResult.mapState_self
      generalize hS : (st.raiseException x).state = S at h1 h2
      obtain ⟨⟩ := S
      simp only at h1 h2
      rw [h1, h2, hr, hm]
    rw [← e]; exact hd
  · rw [if_pos (by rw [h2, hm]; rfl)]
    exact hd

/-- How the step of a framed instruction ends once it ran (`VmState.instrEnd`). -/
theorem instrEnd_good {i : Instr} {Ok : Stack → Prop} {st : VmState} {rest : Slice} {R : Array BitString}
    (hc2 : st.regs.c2 = .excQuit) (hcom : st.cstate.committed = false) (st1 : VmState)
    (hF : ExecFramed i Ok st1)
    (h1 : st1 = { after st rest st.stack st1.gas st.loadedCells st.loadedLibraries with
                  librariesRefused := R, librariesMissed := #[] }) :
    Good1 st rest Ok R (VmState.instrEnd (ExceptT.run (execInstr i) st1)) := by
  obtain ⟨hfr, hok, herr, hnone⟩ := hF
  generalize hX : ExceptT.run (execInstr i) st1 = X at hfr hok herr hnone
  obtain ⟨res, st2⟩ := X
  simp only at hfr hok herr hnone
  have e2 : st2 = { after st rest st2.stack st2.gas st2.loadedCells st2.loadedLibraries with
      librariesRefused := R, librariesMissed := st2.librariesMissed } := by
    conv => lhs; rw [hfr]
    rw [h1]
    rfl
  have hc2' : st2.regs.c2 = .excQuit := by rw [e2]; exact hc2
  have hcom' : st2.cstate.committed = false := by rw [e2]; exact hcom
  have hR : st2.librariesRefused = R := by rw [e2]
  have hml : st.maxLibraryLoads = none → st2.librariesMissed = #[] := by
    intro hn
    have := hnone (by rw [h1]; exact hn)
    rw [this, h1]
  cases res with
  | ok u =>
    simp only [VmState.instrEnd]
    split
    · exact Or.inr ⟨outOfGasHalt_dead hcom', hR, hml⟩
    · exact Or.inl ⟨st2.stack, st2.gas, st2.loadedCells, st2.loadedLibraries, st2.librariesMissed, hok rfl,
        by rw [← e2], hml⟩
  | error e =>
    have he := herr e rfl
    simp only [VmState.instrEnd]
    split
    · exact Or.inr ⟨outOfGasHalt_dead hcom', hR, hml⟩
    · obtain ⟨d, h2, h3⟩ := raise_dead (x := e.toInt) hc2' hcom' he
      exact Or.inr ⟨d, by rw [h2, hR], fun hn => by rw [h3, hml hn]⟩

end TvmLean.Framed

namespace TvmLean.Framed

/-- One run of the step of a framed instruction, the libraries `R` refused. -/
theorem stepOnce_good {i : Instr} {Ok : Stack → Prop} {st : VmState} {code rest : Slice}
    (h : At i Ok st code rest) (R : Array BitString) :
    Good1 st rest Ok R (VmState.stepOnceWith execInstr { st with librariesRefused := R, librariesMissed := #[] }) := by
  obtain ⟨hcc, hcp, hbits, hver, ⟨n, hdec⟩, hchain, hc2, hcom, hexec⟩ := h
  rw [VmState.stepOnceWith_instr' execInstr { st with librariesRefused := R, librariesMissed := #[] } code rest (.quit 0) OrdCregs.empty i n _ _ hcc hcp rfl hbits rfl
    hver hdec]
  rw [VmState.applyCregsCdata_empty,
    VmState.countJump_of_lt { st with librariesRefused := R, librariesMissed := #[] } hchain,
    VmState.enter_empty { st with librariesRefused := R, librariesMissed := #[] } _ hchain, VmState.instrStep_eq]
  split
  · exact Or.inr ⟨outOfGasHalt_dead hcom, rfl, fun _ => rfl⟩
  · split
    · exact Or.inr ⟨outOfGasHalt_dead hcom, rfl, fun _ => rfl⟩
    · exact instrEnd_good hc2 hcom _ (hexec _ rfl rfl) rfl

/-- The state after a framed instruction with the step's libraries cleared is `after` (the state
before had none). -/
theorem after_clear {st : VmState} (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (rest : Slice) (s' : Stack) (g : GasLimits) (lc : Array (Array UInt8)) (ll : Array BitString)
    (R lm : Array BitString) :
    clearLibs { after st rest s' g lc ll with librariesRefused := R, librariesMissed := lm } =
      after st rest s' g lc ll := by
  obtain ⟨⟩ := st
  simp only at hr hm
  subst hr hm
  rfl

/-- What the step of a framed instruction gives: the state after it, or a dead result. -/
def Good (st : VmState) (rest : Slice) (Ok : Stack → Prop) (r : StepResult) : Prop :=
  (∃ s' g lc ll, Ok s' ∧ r = .continue (after st rest s' g lc ll)) ∨ Dead r

/-- A run of the step with the libraries cleared after it gives `Good`. -/
theorem good_of_good1 {Ok : Stack → Prop} {st : VmState} {rest : Slice}
    (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    {R : Array BitString} {r : StepResult} (h1 : Good1 st rest Ok R r) : Good st rest Ok (r.mapState clearLibs) := by
  rcases h1 with ⟨s', g, lc, ll, lm, hok, rfl, -⟩ | ⟨hd, -, -⟩
  · exact Or.inl ⟨s', g, lc, ll, hok, by rw [StepResult.mapState_continue, after_clear hr hm]⟩
  · exact Or.inr hd

/-- The runs of the step again for refused libraries (`VmState.stepRefusingWith`). -/
theorem stepRefusing_good {i : Instr} {Ok : Stack → Prop} {st : VmState} {code rest : Slice}
    (h : At i Ok st code rest) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[]) :
    ∀ (k : Nat) (R : Array BitString), Good st rest Ok (st.stepRefusingWith execInstr R k) := by
  intro k
  induction k with
  | zero => intro R; exact good_of_good1 hr hm (stepOnce_good h R)
  | succ k ih =>
    intro R
    unfold VmState.stepRefusingWith
    simp only
    split
    · exact good_of_good1 hr hm (stepOnce_good h R)
    · exact ih _

/-- **The step of a framed instruction** (`VmState.stepWith`, whatever `max_library_loads` is). -/
theorem stepWith_good {i : Instr} {Ok : Stack → Prop} {st : VmState} {code rest : Slice}
    (h : At i Ok st code rest) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[]) :
    Good st rest Ok (st.stepWith execInstr) := by
  unfold VmState.stepWith
  split
  · rename_i hn
    have hn' : st.maxLibraryLoads = none := by simpa using hn
    have e : st = { st with librariesRefused := #[], librariesMissed := #[] } := by
      obtain ⟨⟩ := st; simp only at hr hm; subst hr hm; rfl
    have h1 := stepOnce_good h #[]
    rw [← e] at h1
    rcases h1 with ⟨s', g, lc, ll, lm, hok, he, hlm⟩ | ⟨hd, hR, hM⟩
    · refine Or.inl ⟨s', g, lc, ll, hok, ?_⟩
      rw [he, hlm hn', ← after_clear hr hm rest s' g lc ll #[] #[]]
    · refine Or.inr ?_
      have : (st.stepOnceWith execInstr).mapState clearLibs = st.stepOnceWith execInstr := by
        apply StepResult.mapState_self
        generalize hS : (st.stepOnceWith execInstr).state = S at hR hM
        obtain ⟨⟩ := S
        simp only at hR hM
        rw [hR, hM hn']
      rwa [this] at hd
  · exact stepRefusing_good h hr hm _ _

/-- **A run from a state about to run a framed instruction**: if `P` holds of every result that
commits nothing and of every run from the state after the instruction (any stack satisfying `Ok`,
gas, loaded cells and libraries), it holds of the run. -/
theorem runWith_framed {i : Instr} {Ok : Stack → Prop} {st : VmState} {code rest : Slice}
    (h : At i Ok st code rest) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r)
    (hok : ∀ s' g lc ll fuel, Ok s' → P (VmState.runWith execInstr fuel (after st rest s' g lc ll)))
    (fuel : Nat) : P (VmState.runWith execInstr fuel st) := by
  cases fuel with
  | zero => exact hP _ h.com
  | succ n =>
    rw [VmState.runWith_succ']
    rcases stepWith_good h hr hm with ⟨s', g, lc, ll, hs, he⟩ | hd
    · rw [he, VmState.runCont_continue]
      exact hok s' g lc ll n hs
    · exact hP _ (hd n)

end TvmLean.Framed

namespace TvmLean.Framed

/-! ## Loading a cell -/

/-- `st'` is `st` but for the gas, the loaded cells and libraries and the libraries noted. -/
def LoadFrame (st st' : VmState) : Prop :=
  st' = { st with gas := st'.gas, loadedCells := st'.loadedCells, loadedLibraries := st'.loadedLibraries,
                  librariesMissed := st'.librariesMissed }

theorem LoadFrame.refl (st : VmState) : LoadFrame st st := rfl

theorem LoadFrame.trans {a b c : VmState} (h1 : LoadFrame a b) (h2 : LoadFrame b c) : LoadFrame a c := by
  unfold LoadFrame at *
  conv => lhs; rw [h2, h1]

theorem LoadFrame.stack {st st' : VmState} (h : LoadFrame st st') : st'.stack = st.stack := by
  rw [h]

theorem LoadFrame.maxLibraryLoads {st st' : VmState} (h : LoadFrame st st') :
    st'.maxLibraryLoads = st.maxLibraryLoads := by
  rw [h]

theorem LoadFrame.librariesRefused {st st' : VmState} (h : LoadFrame st st') :
    st'.librariesRefused = st.librariesRefused := by
  rw [h]

theorem LoadFrame.registerCellLoad (st : VmState) (c : Cell) : LoadFrame st (st.registerCellLoad c) := by
  rw [VmState.registerCellLoad_eq]
  rfl

theorem LoadFrame.admitLibrary (st : VmState) (h : BitString) : LoadFrame st (st.admitLibrary h).1 := by
  unfold VmState.admitLibrary
  repeat' (first | rfl | split)

theorem LoadFrame.registerLibraryLoad (st : VmState) (h : BitString) :
    LoadFrame st (st.registerLibraryLoad h) := by
  have h1 := LoadFrame.admitLibrary st h
  unfold VmState.registerLibraryLoad
  generalize st.admitLibrary h = A at h1
  obtain ⟨st', b⟩ := A
  simp only at h1 ⊢
  split
  · exact h1.trans rfl
  · exact h1

/-- Without `max_library_loads` no library is noted refused. -/
theorem registerLibraryLoad_none (st : VmState) (h : BitString) (hn : st.maxLibraryLoads = none) :
    (st.registerLibraryLoad h).librariesMissed = st.librariesMissed := by
  unfold VmState.registerLibraryLoad VmState.admitLibrary
  rw [hn]
  rfl

theorem LoadFrame.registerCellLoads (st : VmState) (l : List LibraryLoadStep) :
    LoadFrame st (st.registerCellLoads l).1 ∧
      (st.maxLibraryLoads = none → (st.registerCellLoads l).1.librariesMissed = st.librariesMissed) := by
  induction l generalizing st with
  | nil => exact ⟨LoadFrame.refl _, fun _ => rfl⟩
  | cons x l ih =>
    cases x with
    | cell c =>
      simp only [VmState.registerCellLoads]
      have h1 := LoadFrame.registerCellLoad st c
      split
      · exact ⟨h1, fun _ => by rw [VmState.registerCellLoad_eq]⟩
      · obtain ⟨h2, h3⟩ := ih (st.registerCellLoad c)
        refine ⟨h1.trans h2, fun hn => ?_⟩
        rw [h3 (by rw [h1.maxLibraryLoads]; exact hn), VmState.registerCellLoad_eq]
    | library h =>
      simp only [VmState.registerCellLoads]
      have h1 := LoadFrame.registerLibraryLoad st h
      obtain ⟨h2, h3⟩ := ih (st.registerLibraryLoad h)
      refine ⟨h1.trans h2, fun hn => ?_⟩
      rw [h3 (by rw [h1.maxLibraryLoads]; exact hn), registerLibraryLoad_none st h hn]

/-- Following a library cell fails only with cell_und. -/
theorem libraryResolveLoadsAux_error (libs : Array Cell) (gv : Nat) (refused : Array BitString) :
    ∀ (fuel : Nat) (c : Cell) (loads : Array LibraryLoadStep) (e : Excno),
      (libraryResolveLoadsAux libs gv refused fuel c loads).2 = .error e → e = .cellUnd := by
  intro fuel
  induction fuel with
  | zero => intro c loads e h; simp only [libraryResolveLoadsAux, Except.error.injEq] at h; exact h.symm
  | succ f ih =>
    intro c loads e h
    simp only [libraryResolveLoadsAux] at h
    repeat' (first
      | (simp only [Except.error.injEq] at h; exact h.symm)
      | (cases h; done)
      | exact ih _ _ e h
      | (unfold Cell.rejectSpecial at h)
      | split at h)

/-- **`VM.loadCellSlice`** (the load of `CTOS`, a library cell followed) changes only what a load
changes (`LoadFrame`), fails only with out of gas or cell_und, and notes no refused library without
`max_library_loads`. -/
theorem loadCellSlice_frame (c : Cell) (st : VmState) :
    LoadFrame st (ExceptT.run (VM.loadCellSlice c) st).2 ∧
      (∀ e, (ExceptT.run (VM.loadCellSlice c) st).1 = .error e → 2 ≤ e.toInt) ∧
      (st.maxLibraryLoads = none → (ExceptT.run (VM.loadCellSlice c) st).2.librariesMissed = st.librariesMissed) := by
  obtain ⟨hF, hN⟩ := LoadFrame.registerCellLoads st (.cell c :: (st.libraryLoads c).toList)
  simp only [VM.loadCellSlice, VM.registerCellLoad, VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_set]
  generalize st.registerCellLoads (.cell c :: (st.libraryLoads c).toList) = R at hF hN ⊢
  obtain ⟨st', ex⟩ := R
  simp only at hF hN ⊢
  cases ex with
  | true =>
    simp only [if_true, VM.run_throw, VM.bindRes_error]
    exact ⟨hF, (fun e h => by cases h; decide), hN⟩
  | false =>
    simp only [Bool.false_eq_true, if_false, VM.run_pure, VM.bindRes_ok, VM.run_bind, VM.run_get]
    split
    · exact ⟨hF, (fun e h => by cases h), hN⟩
    · rename_i e' he
      refine ⟨hF, fun e h => ?_, hN⟩
      simp only [VM.run_throw, Except.error.injEq] at h
      subst h
      rw [libraryResolveLoadsAux_error _ _ _ _ _ _ _ he]
      decide

/-! ## `CTOS` of any cell -/

/-- `CTOS` of the cell `c` on top of the stack `s`: the load (`VM.loadCellSlice`, a library cell
followed), then its slice pushed. -/
theorem run_ctos (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) :
    ExceptT.run (execInstr .ctos) st =
      VM.bindRes (ExceptT.run (VM.loadCellSlice c) { st with stack := s }) (fun sl => VM.push (.slice sl)) := by
  simp only [Exec.reduceExecInstrRun]
  simp only [VM.run_bind, VM.run_popCell, hs, Array.size_push, Nat.zero_lt_succ, dif_pos,
    VM.back_push, Array.pop_push, VM.bindRes_ok]

/-- **`CTOS` of any cell is framed**: a slice pushed, or an exception of code 2 or more. -/
theorem ctos_framed (st : VmState) (s : Stack) (c : Cell) (hs : st.stack = s.push (.cell c)) :
    ExecFramed .ctos (fun s' => ∃ sl, s' = s.push (.slice sl)) st := by
  obtain ⟨hF, hE, hN⟩ := loadCellSlice_frame c { st with stack := s }
  have hr := run_ctos st s c hs
  generalize ExceptT.run (VM.loadCellSlice c) { st with stack := s } = R at hF hE hN hr
  obtain ⟨r, st'⟩ := R
  simp only at hF hE hN
  cases r with
  | ok sl =>
    simp only [VM.bindRes_ok, VM.run_push] at hr
    refine ⟨?_, fun _ => ?_, fun e h => ?_, fun hn => ?_⟩
    · rw [hr, hF]; rfl
    · rw [hr]; exact ⟨sl, by rw [hF.stack]⟩
    · rw [hr] at h; cases h
    · rw [hr]; exact hN hn
  | error e =>
    simp only [VM.bindRes_error] at hr
    refine ⟨?_, fun h => ?_, fun e2 h => ?_, fun hn => ?_⟩
    · rw [hr, hF]; rfl
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h; exact hE e rfl
    · rw [hr]; exact hN hn

end TvmLean.Framed

namespace TvmLean.Framed

theorem ne_zero_of_eq_ne {a b : Nat} (h : a = b) (hb : b ≠ 0) : a ≠ 0 := h ▸ hb
theorem le_of_eq_le {a b c : Nat} (h : a = b) (hb : b ≤ c) : a ≤ c := h ▸ hb

/-- **A run from `CTOS` of any cell.** `st` is about to run `CTOS` (decoded from `code`, the code
after it `rest`) on the cell `c` on top of the stack: if `P` holds of every result that commits
nothing and of every run from the state after it with any slice `sl` pushed, any gas, loaded cells
and libraries (`after`), it holds of the run. -/
theorem runWith_ctos {st : VmState} {code rest : Slice} {s : Stack} {c : Cell}
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ n, decodeCp0WithBits code = .ok (.ctos, n, rest)) (hchain : st.chainJumps < freeNestedContJump)
    (hc2 : st.regs.c2 = .excQuit) (hcom : st.cstate.committed = false)
    (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[]) (hs : st.stack = s.push (.cell c))
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r)
    (hok : ∀ (sl : Slice) g lc ll fuel, P (VmState.runWith execInstr fuel (after st rest (s.push (.slice sl)) g lc ll)))
    (fuel : Nat) : P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := fun s' => ∃ sl, s' = s.push (.slice sl))
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom, fun st0 h1 _ => ctos_framed st0 s c (h1.trans hs)⟩ hr hm P hP
    (fun s' g lc ll fuel ⟨sl, h⟩ => h ▸ hok sl g lc ll fuel) fuel

end TvmLean.Framed

namespace TvmLean.Exec

open Lean Meta Elab Tactic

/-- `f` applied to `k` new goals for its next hypotheses, then to `last`: the proof and the new
goals. -/
def applyRest (f : Expr) (k : Nat) (last : Array Expr) : MetaM (Expr × Array MVarId) := do
  let mut e := f
  let mut goals := #[]
  for _ in [0:k] do
    let .forallE _ d _ _ ← whnf (← inferType e) | throwError "applyRest: not a function"
    let m ← mkFreshExprSyntheticOpaqueMVar d
    goals := goals.push m.mvarId!
    e := mkApp e m
  return (mkAppN e last, goals)

/-- The facts of the code at the current continuation of `S` (an ordinary continuation on a closed
code slice): the code, the decoded instruction, the code after it, and the proofs of the
hypotheses `bits`, `ver` (for the global version of `S`), `dec` of a framed run lemma. -/
def framedFacts (S : Expr) : MetaM (Expr × Expr × Expr × Expr × Expr × Expr) := do
  let cc ← whnfCore (← whnfR (← mkAppM ``VmState.cc #[S]))
  unless cc.isAppOfArity ``Continuation.ordinary 4 do throwError "framed: not an ordinary continuation"
  let code := cc.getArg! 0
  unless isClosed code do throwError "framed: the code is not closed"
  let some (cellE, _, _) ← sliceParts? code | throwError "framed: the code is not a slice"
  let sv ← evalSlice code
  let (decE, some (iE, nE, restE)) ← decodeExprs cellE sv | throwError "framed: no instruction"
  let hdec ← kernelEq (← mkAppM ``decodeCp0WithBits #[code]) decE
  let tyN := mkConst ``Nat
  let hdecEx ← mkAppOptM ``Exists.intro #[tyN,
    some (← withLocalDeclD `n tyN fun n => do
      mkLambdaFVars #[n] (← mkEq (← mkAppM ``decodeCp0WithBits #[code])
        (← mkAppOptM ``Except.ok #[mkConst ``Excno, none,
          ← mkAppM ``Prod.mk #[iE, ← mkAppM ``Prod.mk #[n, restE]]]))),
    nE, hdec]
  let b := sv.bitsRemaining
  let hbits ← kernelEq (← mkAppM ``Slice.bitsRemaining #[code]) (mkNatLit b)
  let hb ← decideProof (← mkAppM ``Ne #[mkNatLit b, mkNatLit 0])
  let hbitsNe ← mkAppM ``Framed.ne_zero_of_eq_ne #[hbits, hb]
  let k := cp0RequiredVersion sv.opcode24
  let hver ← kernelEq (← mkAppM ``cp0RequiredVersion #[← mkAppM ``Slice.opcode24 #[code]]) (mkNatLit k)
  let gvE ← mkAppM ``VmState.globalVersion #[S]
  let hk ← if k = 0 then mkAppM ``Nat.zero_le #[gvE] else
    decideProof (← mkAppM ``LE.le #[mkNatLit k, ← whnfCore (← whnfR gvE)])
  let hverLe ← mkAppM ``Framed.le_of_eq_le #[hver, hk]
  return (code, iE, restE, hbitsNe, hverLe, hdecEx)

end TvmLean.Exec

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_ctos_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S` written out) is
about to run `CTOS` on a cell it does not know: by `Framed.runWith_ctos`, two goals: `P` of a result
that commits nothing (`∀ r, r.state.cstate.committed = false → P r`), and `P` of the run from the
state after `CTOS` with any slice, gas, loaded cells and libraries
(`∀ sl g lc ll fuel, P (VmState.runWith execInstr fuel (Framed.after S rest (s.push (.slice sl)) g lc ll))`). -/
elab "vm_ctos_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_ctos_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  unless (← whnfR iE).isConstOf ``Instr.ctos do throwError "vm_ctos_any: the instruction is {iE}, not CTOS"
  let stk ← whnfR (← mkAppM ``VmState.stack #[S])
  unless stk.isAppOfArity ``Array.push 3 do throwError "vm_ctos_any: the stack is not written out"
  let top ← whnfR (stk.getArg! 2)
  unless top.isAppOfArity ``Value.cell 1 do throwError "vm_ctos_any: no cell on top of the stack"
  let motive ← withLocalDeclD `r (mkConst ``StepResult) fun rv => do
    mkLambdaFVars #[rv] ((← kabstract t r).instantiate1 rv)
  let refl (e : Expr) : MetaM Expr := mkEqRefl e
  let hcc ← refl (← mkAppM ``VmState.cc #[S])
  let hcp ← refl (← mkAppM ``VmState.cp #[S])
  let hchain ← Exec.decideProof (← mkAppM ``LT.lt #[← whnfCore (← whnfR (← mkAppM ``VmState.chainJumps #[S])),
    mkConst ``freeNestedContJump])
  let hc2 ← refl (← mkAppM ``Regs.c2 #[← mkAppM ``VmState.regs #[S]])
  let hcom ← refl (← mkAppM ``CommittedState.committed #[← mkAppM ``VmState.cstate #[S]])
  let hr ← refl (← mkAppM ``VmState.librariesRefused #[S])
  let hm ← refl (← mkAppM ``VmState.librariesMissed #[S])
  let hs ← refl (← mkAppM ``VmState.stack #[S])
  let f ← mkAppOptM ``Framed.runWith_ctos #[S, none, none, stk.getArg! 1, top.getArg! 0, hcc, hcp, hbitsNe, hverLe,
    hdecEx, hchain, hc2, hcom, hr, hm, hs, motive]
  let (pf, goals) ← Exec.applyRest f 2 #[fuel]
  unless ← isDefEq (← inferType pf) t do throwError "vm_ctos_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_clear_unused`: clears the hypotheses (propositions) that mention a variable the goal does not
(after a framed instruction, the conditions on the gas and loaded cells before it), then the
variables nothing mentions; keeps the context of a run small for `omega`. -/
elab "vm_clear_unused" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let used := (collectFVars {} t).fvarSet
  let mut toClear : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let fvs := (collectFVars {} ty).fvarIds
    if fvs.any (fun v => !used.contains v) then toClear := toClear.push d.fvarId
  let g ← g.tryClearMany toClear
  -- then the variables nothing mentions
  let g ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let mut used := (collectFVars {} t).fvarSet
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      used := (collectFVars {} (← instantiateMVars d.type)).fvarSet.foldl (·.insert ·) used
    let mut unused : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if ← isProp (← instantiateMVars d.type) then continue
      unless used.contains d.fvarId do unused := unused.push d.fvarId
    g.tryClearMany unused
  replaceMainGoal [g]

end TvmLean

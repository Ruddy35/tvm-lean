import TvmLean.Proofs.Exec.Load

/-!
# Loads of cells as their outcomes

The loads of an instruction are cases `vm_run` can follow when it knows the cells (the cells of
the code, an ordinary cell written out: `VM.run_registerCellLoad_ordinary`, the closed forms of
`Proofs/Exec/Dict/Gas.lean`). The cells a dictionary of a message visits are not known: they may be
exotic (a library cell loads its library, `VmState.libraryLoads`, and with `max_library_loads` set
the step may note libraries it refuses, `VmState.registerLibraryLoad`), and how many there are is
the result of a walk of an unknown tree. What is known of such loads (`Havoc.loads_cases`): they
end normally or out of gas, and change only the gas, the loaded cells, the loaded libraries and the
libraries noted missed; without `max_library_loads` not the last two (`VmState.LoadsOnly`). Of
loads of ordinary cells (`Havoc.loadsOrd_cases`): they end normally or out of gas, and change only
the gas and the loaded cells.

Followed load by load, the loads of known cells leave in the state their gas as a term that grows
with each load (`cellLoadGas (cellsLoadedAfter … c) c'`), and a check of each of them; a run that
needs only their outcomes takes them whole instead.

`Havoc.loads cells st` names the run of the loads of `cells` from `st` (`VM.registerCellLoadList`,
`Havoc.loads_eq`); a symbolic run (`TvmLean/Proofs/Check/Unknown.lean`, `check_havoc`) replaces it
by the result `Havoc.loads_cases` or `Havoc.loadsOrd_cases` gives, with its unknown parts as new
variables.
-/

namespace TvmLean

/-- `st'` with the fields a load changes (the gas, the loaded cells, the loaded libraries, the
libraries noted missed) taken from `st`. -/
def VmState.withLoadsOf (st' st : VmState) : VmState :=
  { st' with gas := st.gas, loadedCells := st.loadedCells, loadedLibraries := st.loadedLibraries,
             librariesMissed := st.librariesMissed }

theorem VmState.withLoadsOf_withLoadsOf (c b a : VmState) :
    (c.withLoadsOf b).withLoadsOf a = c.withLoadsOf a := rfl

/-- `st'` is `st` but for the gas, the loaded cells, the loaded libraries and the libraries noted
missed, what loading cells changes; without `max_library_loads` the libraries are those of `st`. -/
def VmState.LoadsOnly (st st' : VmState) : Prop :=
  st'.withLoadsOf st = st ∧
    (st.maxLibraryLoads = none →
      st'.loadedLibraries = st.loadedLibraries ∧ st'.librariesMissed = st.librariesMissed)

namespace VmState.LoadsOnly

theorem refl (st : VmState) : st.LoadsOnly st := ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem maxLibraryLoads {st st' : VmState} (h : st.LoadsOnly st') :
    st'.maxLibraryLoads = st.maxLibraryLoads := by
  have := congrArg VmState.maxLibraryLoads h.1
  exact this

theorem trans {a b c : VmState} (h1 : a.LoadsOnly b) (h2 : b.LoadsOnly c) : a.LoadsOnly c := by
  refine ⟨?_, fun ha => ?_⟩
  · rw [← VmState.withLoadsOf_withLoadsOf c b a, h2.1, h1.1]
  · have hb : b.maxLibraryLoads = none := by rw [h1.maxLibraryLoads]; exact ha
    obtain ⟨l1, m1⟩ := h1.2 ha
    obtain ⟨l2, m2⟩ := h2.2 hb
    exact ⟨l2.trans l1, m2.trans m1⟩

/-- The state of a frame, written as `st` with the fields a load changes. -/
theorem eq {st st' : VmState} (h : st.LoadsOnly st') : st' = st.withLoadsOf st' := by
  calc st' = (st'.withLoadsOf st).withLoadsOf st' := rfl
    _ = st.withLoadsOf st' := by rw [h.1]

end VmState.LoadsOnly

/-- A load of one cell (`VmState.registerCellLoad`: the gas, the loaded cells). -/
theorem VmState.LoadsOnly.registerCellLoad (st : VmState) (c : Cell) : st.LoadsOnly (st.registerCellLoad c) := by
  refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩
  all_goals
    unfold VmState.registerCellLoad VmState.consumeGas
    dsimp only
    split <;> rfl

/-- C++ `load_library`'s admission (`VmState.admitLibrary`): only the loaded libraries change, and
nothing, with nothing refused, without `max_library_loads`. -/
theorem VmState.admitLibrary_frame (st : VmState) (h : BitString) :
    (st.admitLibrary h).1.withLoadsOf st = st ∧
      (st.maxLibraryLoads = none → (st.admitLibrary h).1 = st ∧ (st.admitLibrary h).2 = false) := by
  unfold VmState.admitLibrary
  split
  · exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  · rename_i m hm
    refine ⟨?_, fun hn => by rw [hm] at hn; cases hn⟩
    split
    · rfl
    · split <;> rfl

/-- The call of `load_library` a load makes (`VmState.registerLibraryLoad`: the loaded libraries,
the libraries noted missed; neither without `max_library_loads`). -/
theorem VmState.LoadsOnly.registerLibraryLoad (st : VmState) (h : BitString) :
    st.LoadsOnly (st.registerLibraryLoad h) := by
  have ha := VmState.admitLibrary_frame st h
  unfold VmState.registerLibraryLoad
  generalize st.admitLibrary h = p at ha
  obtain ⟨st1, refused⟩ := p
  dsimp only at ha ⊢
  refine ⟨?_, fun hn => ?_⟩
  · split
    · exact ha.1
    · exact ha.1
  · obtain ⟨rfl, rfl⟩ := ha.2 hn
    simp

/-- The loads and library calls of a load (`VmState.registerCellLoads`). -/
theorem VmState.LoadsOnly.registerCellLoads :
    ∀ (steps : List LibraryLoadStep) (st : VmState), st.LoadsOnly (st.registerCellLoads steps).1
  | [], st => VmState.LoadsOnly.refl st
  | .cell c :: rest, st => by
    simp only [VmState.registerCellLoads]
    split
    · exact VmState.LoadsOnly.registerCellLoad st c
    · exact (VmState.LoadsOnly.registerCellLoad st c).trans (registerCellLoads rest _)
  | .library h :: rest, st => by
    simp only [VmState.registerCellLoads]
    exact (VmState.LoadsOnly.registerLibraryLoad st h).trans (registerCellLoads rest _)

/-- The load of any cell (`VM.registerCellLoad`): normally or out of gas, in a frame. -/
theorem VM.registerCellLoad_frame (c : Cell) (st : VmState) :
    ∃ r st', ExceptT.run (VM.registerCellLoad c) st = (r, st') ∧ st.LoadsOnly st' ∧
      (r = .ok () ∨ r = .error .outOfGas) := by
  have hf := VmState.LoadsOnly.registerCellLoads (.cell c :: (st.libraryLoads c).toList) st
  generalize hx : st.registerCellLoads (.cell c :: (st.libraryLoads c).toList) = p at hf
  obtain ⟨st', ex⟩ := p
  refine ⟨if ex then .error .outOfGas else .ok (), st', ?_, hf, ?_⟩
  · simp only [VM.registerCellLoad, VM.run_bind, VM.run_get, VM.bindRes_ok, hx]
    cases ex <;> rfl
  · cases ex <;> simp

/-- The loads of any cells in order (`VM.registerCellLoadList`): normally or out of gas, in a
frame. -/
theorem VM.registerCellLoadList_frame :
    ∀ (cells : List Cell) (st : VmState), ∃ r st', ExceptT.run (VM.registerCellLoadList cells) st = (r, st') ∧
      st.LoadsOnly st' ∧ (r = .ok () ∨ r = .error .outOfGas)
  | [], st => ⟨_, _, rfl, VmState.LoadsOnly.refl st, Or.inl rfl⟩
  | c :: cs, st => by
    rw [VM.run_registerCellLoadList_cons]
    obtain ⟨r, st1, h1, f1, hr⟩ := VM.registerCellLoad_frame c st
    rw [h1]
    rcases hr with rfl | rfl
    · rw [VM.bindRes_ok]
      obtain ⟨r2, st2, h2, f2, hr2⟩ := registerCellLoadList_frame cs st1
      exact ⟨r2, st2, h2, f1.trans f2, hr2⟩
    · exact ⟨_, _, VM.bindRes_error _ _ _, f1, Or.inr rfl⟩

namespace Havoc

/-- The run of the loads of `cells` from `st` (`VM.registerCellLoadList`), named so that a symbolic
run leaves it for `loads_cases`. -/
@[irreducible] def loads (cells : List Cell) (st : VmState) : Except Excno Unit × VmState :=
  ExceptT.run (VM.registerCellLoadList cells) st

theorem loads_eq (cells : List Cell) (st : VmState) :
    ExceptT.run (VM.registerCellLoadList cells) st = loads cells st := by
  unfold loads; rfl

/-- The load of one cell is the loads of the list of it. -/
theorem load_eq (c : Cell) (st : VmState) : ExceptT.run (VM.registerCellLoad c) st = loads [c] st := by
  rw [← loads_eq, VM.run_registerCellLoadList_cons]
  obtain ⟨r, st', h, -, hr⟩ := VM.registerCellLoad_frame c st
  rw [h]
  rcases hr with rfl | rfl <;> rfl

/-- The loads of `cells` as an action of the VM (`VM.registerCellLoadList`), named so that a
symbolic run does not unfold the loads of a cell inside a larger action (a `do` block) before it
splits it: its run is `loads` (`run_loadsM`). -/
@[irreducible] def loadsM (cells : List Cell) : VM Unit := VM.registerCellLoadList cells

theorem loadsM_eq (cells : List Cell) : VM.registerCellLoadList cells = loadsM cells := by
  unfold loadsM; rfl

theorem run_loadsM (cells : List Cell) (st : VmState) :
    ExceptT.run (loadsM cells) st = loads cells st := by
  unfold loadsM loads; rfl

/-- The load of one cell is the action of the loads of the list of it. -/
theorem loadM_eq (c : Cell) : VM.registerCellLoad c = loadsM [c] := by
  rw [← loadsM_eq]
  funext st
  have h := load_eq c st
  rw [← loads_eq] at h
  exact h

/-- **What is known of loads of unknown cells**: they end normally or out of gas, in the state
`st` with new gas, loaded cells, loaded libraries and libraries noted missed; without
`max_library_loads`, the libraries of `st`. -/
theorem loads_cases (cells : List Cell) (st : VmState) :
    ∃ (r : Except Excno Unit) (g : GasLimits) (lc : Array (Array UInt8)) (ll lm : Array BitString),
      loads cells st = (r, { st with gas := g, loadedCells := lc, loadedLibraries := ll,
                                     librariesMissed := lm }) ∧
      (r = .ok () ∨ r = .error .outOfGas) ∧
      (st.maxLibraryLoads = none → ll = st.loadedLibraries ∧ lm = st.librariesMissed) := by
  obtain ⟨r, st', h, f, hr⟩ := VM.registerCellLoadList_frame cells st
  refine ⟨r, st'.gas, st'.loadedCells, st'.loadedLibraries, st'.librariesMissed, ?_, hr, f.2⟩
  rw [← loads_eq, h]
  exact congrArg (Prod.mk r) f.eq

/-- **What is known of loads of ordinary cells** (the cells of the code, say): they end normally or
out of gas, in the state `st` with new gas and loaded cells; no library is loaded
(`VM.run_registerCellLoad_ordinary`). -/
theorem loadsOrd_cases (cells : List Cell) (hc : cells.all (fun c => !c.special) = true) (st : VmState) :
    ∃ (r : Except Excno Unit) (g : GasLimits) (lc : Array (Array UInt8)),
      loads cells st = (r, { st with gas := g, loadedCells := lc }) ∧
      (r = .ok () ∨ r = .error .outOfGas) := by
  induction cells generalizing st with
  | nil => exact ⟨.ok (), st.gas, st.loadedCells, by rw [← loads_eq]; rfl, Or.inl rfl⟩
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hc
    have h1 : c.special = false := by simpa using hc.1
    rw [← loads_eq, VM.run_registerCellLoadList_cons, VM.run_registerCellLoad_ordinary c st h1]
    by_cases h : (st.registerCellLoad c).gasExhaustedNow = true
    · rw [if_pos h, VM.bindRes_error]
      refine ⟨_, (st.registerCellLoad c).gas, (st.registerCellLoad c).loadedCells, ?_, Or.inr rfl⟩
      rw [VmState.registerCellLoad_eq]
    · rw [if_neg h, VM.bindRes_ok, loads_eq]
      obtain ⟨r, g, lc, he, hr⟩ := ih hc.2 (st.registerCellLoad c)
      refine ⟨r, g, lc, ?_, hr⟩
      rw [he, VmState.registerCellLoad_eq]

/-- The loads and library calls of a load from `st` (`VmState.registerCellLoads`), named so that a
symbolic run leaves it for `cellLoads_cases`. -/
@[irreducible] def cellLoads (st : VmState) (steps : List LibraryLoadStep) : VmState × Bool :=
  st.registerCellLoads steps

theorem cellLoads_eq (st : VmState) (steps : List LibraryLoadStep) :
    st.registerCellLoads steps = cellLoads st steps := by
  unfold cellLoads; rfl

/-- **What is known of the loads and library calls of a load of an unknown cell**: the state `st`
with new gas, loaded cells, loaded libraries and libraries noted missed (without
`max_library_loads`, the libraries of `st`), and whether gas ran out. -/
theorem cellLoads_cases (st : VmState) (steps : List LibraryLoadStep) :
    ∃ (g : GasLimits) (lc : Array (Array UInt8)) (ll lm : Array BitString) (b : Bool),
      cellLoads st steps = ({ st with gas := g, loadedCells := lc, loadedLibraries := ll,
                                      librariesMissed := lm }, b) ∧
      (st.maxLibraryLoads = none → ll = st.loadedLibraries ∧ lm = st.librariesMissed) := by
  have f := VmState.LoadsOnly.registerCellLoads steps st
  refine ⟨(st.registerCellLoads steps).1.gas, (st.registerCellLoads steps).1.loadedCells,
    (st.registerCellLoads steps).1.loadedLibraries, (st.registerCellLoads steps).1.librariesMissed,
    (st.registerCellLoads steps).2, ?_, f.2⟩
  rw [← cellLoads_eq]
  exact Prod.ext f.eq rfl

end Havoc

end TvmLean

import TvmLean.Proofs.Exec.Eval

/-!
# Cell loads without hashes

Every load of a cell charges gas by whether the cell was loaded before (C++
`VmState::register_cell_load`: 100 for a first load, 25 for a reload), which the model decides by
comparing representation hashes (`VmState.registerCellLoad`). A hash of a cell built from symbolic
data cannot be computed, and the hash of a concrete cell of the code is costly to compute in the
kernel (`Proofs/Contracts/Wallet3Kernel.lean`). The lemmas here state a load without computing a
hash: its gas is a symbolic cost `cellLoadGas loaded c` between 25 and 100
(`cellLoadGas_bounds`), the set of loaded cells after it `cellsLoadedAfter loaded c`; both stay
terms. Only a load into an empty set is decided (`cellLoadGas_empty`: a first load).

* `VmState.registerCellLoad_eq`: the load as these two terms (tagged `vm_run`).
* `VM.run_registerCellLoad_ordinary`: the load of an ordinary cell by an instruction
  (`VM.registerCellLoad`, C++ `load_cell_slice`): no library is followed, out of gas at once.
* `VM.registerCellLoadList`: the loads of a list of cells in order (the nodes a dictionary lookup
  visits), `VM.forIn_registerCellLoad` the `for` loop of the model as it.

The dictionary lookups of the model take the resolver of the VM (`VM.cellResolver`: a library cell
loads as the root of its library); a lookup that succeeds with the default resolver
(`Cell.rejectSpecial`, every exotic cell refused) visited only ordinary cells, so it gives the same
result with any resolver that loads an ordinary cell as itself
(`dictLookupWithCells_of_rejectSpecial`). A lookup in a concrete dictionary is then a closed fact,
decided by the kernel.
-/

namespace TvmLean

/-! ## The gas of a load -/

/-- Whether `c` was loaded before, as the hashes of the loaded cells `loaded` record (C++
`loaded_cells.insert(cell->get_hash())` failing). -/
@[irreducible] def cellSeen (loaded : Array (Array UInt8)) (c : Cell) : Bool :=
  loaded.any (fun x => x == Cell.hashBytes c)

/-- The gas of loading `c` after the cells `loaded` (C++ `register_cell_load`): 25 for a reload,
100 for a first load. Symbolic execution keeps it as a term (`cellLoadGas_bounds`); it is
irreducible, so that no unification evaluates the hashes it compares. -/
@[irreducible] def cellLoadGas (loaded : Array (Array UInt8)) (c : Cell) : Int :=
  if cellSeen loaded c then cellReloadGasPrice else cellLoadGasPrice

/-- The hashes of the loaded cells after loading `c`. -/
@[irreducible] def cellsLoadedAfter (loaded : Array (Array UInt8)) (c : Cell) : Array (Array UInt8) :=
  if cellSeen loaded c then loaded else loaded.push (Cell.hashBytes c)

/-- **A load, without its hash.** `VmState.registerCellLoad` charges `cellLoadGas` and records
the cell (`cellsLoadedAfter`). -/
@[vm_run] theorem VmState.registerCellLoad_eq (st : VmState) (c : Cell) :
    st.registerCellLoad c =
      { st with loadedCells := cellsLoadedAfter st.loadedCells c,
                gas := st.gas.consume (cellLoadGas st.loadedCells c) } := by
  unfold VmState.registerCellLoad cellsLoadedAfter cellLoadGas cellSeen
  by_cases h : (st.loadedCells.any fun x => x == c.hashBytes) = true <;> simp [h, VmState.consumeGas]

/-- The gas of a load is between that of a reload and that of a first load. -/
theorem cellLoadGas_bounds (loaded : Array (Array UInt8)) (c : Cell) :
    25 ≤ cellLoadGas loaded c ∧ cellLoadGas loaded c ≤ 100 := by
  unfold cellLoadGas; split <;> simp [cellReloadGasPrice, cellLoadGasPrice]

/-- Nothing loaded yet: a first load. -/
@[vm_run] theorem cellLoadGas_empty (c : Cell) : cellLoadGas #[] c = 100 := by
  unfold cellLoadGas cellSeen; rfl

@[vm_run] theorem cellsLoadedAfter_empty (c : Cell) : cellsLoadedAfter #[] c = #[Cell.hashBytes c] := by
  unfold cellsLoadedAfter cellSeen; rfl

/-! ## Loads by instructions -/

/-- `VM.registerCellLoad` of an ordinary cell (C++ `load_cell_slice` → `register_cell_load`):
the load is charged, out of gas at once (from version 4) if the gas runs out. -/
@[vm_run] theorem VM.run_registerCellLoad_ordinary (c : Cell) (st : VmState) (hc : c.special = false) :
    ExceptT.run (VM.registerCellLoad c) st =
      if (st.registerCellLoad c).gasExhaustedNow then (.error .outOfGas, st.registerCellLoad c)
      else (.ok (), st.registerCellLoad c) := by
  have hl : st.libraryLoads c = #[] := by simp [VmState.libraryLoads, hc]
  simp only [VM.registerCellLoad, VM.run_bind, VM.run_get, VM.bindRes_ok, hl, Array.toList_empty]
  simp only [VmState.registerCellLoads]
  by_cases h : (st.registerCellLoad c).gasExhaustedNow = true
  · simp only [h, if_true]; rfl
  · simp only [h, Bool.false_eq_true, if_false]; rfl

/-- The loads of `cells` in order, each by `VM.registerCellLoad` (the nodes a dictionary lookup
visits). -/
def VM.registerCellLoadList : List Cell → VM Unit
  | [] => pure ()
  | c :: cs => do VM.registerCellLoad c; VM.registerCellLoadList cs

@[vm_run] theorem VM.run_registerCellLoadList_nil (st : VmState) :
    ExceptT.run (VM.registerCellLoadList []) st = (.ok (), st) := rfl

@[vm_run] theorem VM.run_registerCellLoadList_cons (c : Cell) (cs : List Cell) (st : VmState) :
    ExceptT.run (VM.registerCellLoadList (c :: cs)) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoad c) st) (fun _ => VM.registerCellLoadList cs) := by
  simp only [VM.registerCellLoadList, VM.run_bind]

/-- The `for` loop of the model over the cells a lookup visited is `VM.registerCellLoadList`. -/
theorem VM.forIn_registerCellLoad (cells : Array Cell) :
    (forIn cells PUnit.unit fun c _ => do VM.registerCellLoad c; pure (ForInStep.yield PUnit.unit) : VM PUnit) =
      (do VM.registerCellLoadList cells.toList; pure PUnit.unit) := by
  rw [← Array.forIn_toList]
  generalize cells.toList = l
  induction l with
  | nil => simp only [List.forIn_nil, VM.registerCellLoadList, pure_bind]
  | cons c cs ih =>
    simp only [List.forIn_cons, VM.registerCellLoadList, bind_assoc, pure_bind, ih]

/-! ## Dictionary lookups with any resolver -/

/-- The label of a node depends on the resolver only through the node itself. -/
theorem parseDictLabel_resolve (cell : Cell) (maxLen : Nat) (r r' : Cell → Except Excno Cell)
    (h : r cell = r' cell) : parseDictLabel cell maxLen r = parseDictLabel cell maxLen r' := by
  simp only [parseDictLabel, h]

/-- A resolver that loads an ordinary cell as itself (the resolver of the VM,
`VM.cellResolver`, and the default `Cell.rejectSpecial`). -/
def ResolvesOrdinary (r : Cell → Except Excno Cell) : Prop := ∀ c, c.special = false → r c = .ok c

theorem resolvesOrdinary_rejectSpecial : ResolvesOrdinary Cell.rejectSpecial := by
  intro c hc; simp [Cell.rejectSpecial, hc]

/-- The resolver of the VM loads an ordinary cell as itself. -/
theorem resolvesOrdinary_library (libs : Array Cell) (gv : Nat) (refused : Array BitString) :
    ResolvesOrdinary (fun c => (libraryResolveLoads libs gv c refused).2) := by
  intro c hc
  simp [libraryResolveLoads, libraryChainBound, libraryResolveLoadsAux, hc]

/-- A node the default resolver accepts is ordinary, and any resolver of `ResolvesOrdinary` loads
it as itself. -/
theorem parseDictLabel_of_rejectSpecial (cell : Cell) (maxLen : Nat) (r : Cell → Except Excno Cell)
    (hr : ResolvesOrdinary r) (lbl : DictLabel)
    (h : parseDictLabel cell maxLen Cell.rejectSpecial = .ok lbl) :
    parseDictLabel cell maxLen r = .ok lbl := by
  cases hs : cell.special
  · rw [parseDictLabel_resolve cell maxLen r Cell.rejectSpecial (by rw [hr cell hs, resolvesOrdinary_rejectSpecial cell hs])]
    exact h
  · simp [parseDictLabel, Cell.rejectSpecial, hs] at h
    cases h

/-- One step of the lookup: if the step with the default resolver and the recursion `rec'`
succeeds, the step with a resolver of `ResolvesOrdinary` and a recursion `rec` that succeeds
wherever `rec'` does gives the same result. -/
theorem dictLookupWithCellsStep_of_rejectSpecial (key : BitString) (pos : Nat)
    (rec rec' : Cell → (p : Nat) → pos < p → p ≤ key.size → Nat → Except Excno (Option Slice × Array Cell))
    (hrec : ∀ c p h1 h2 rm x, rec' c p h1 h2 rm = .ok x → rec c p h1 h2 rm = .ok x)
    (cell : Cell) (remaining : Nat) (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r)
    (x : Option Slice × Array Cell)
    (h : dictLookupWithCellsStep key pos rec' cell remaining Cell.rejectSpecial = .ok x) :
    dictLookupWithCellsStep key pos rec cell remaining r = .ok x := by
  unfold dictLookupWithCellsStep at h ⊢
  cases hp : parseDictLabel cell remaining Cell.rejectSpecial with
  | error e => rw [hp] at h; cases h
  | ok lbl =>
    rw [parseDictLabel_of_rejectSpecial cell remaining r hr lbl hp]
    rw [hp] at h
    simp only [bind, Except.bind] at h ⊢
    cases hv : dictValidateNodeExt lbl remaining with
    | error e => rw [hv] at h; cases h
    | ok rem0 =>
      rw [hv] at h
      simp only [pure, Except.pure] at h ⊢
      revert h
      split
      · exact id
      · split
        · exact id
        · split
          · exact id
          · split
            · intro h; cases h
            · rename_i y hy
              intro h
              rw [hrec _ _ _ _ _ _ hy]
              exact h

/-- **The lookup with any resolver.** A lookup that succeeds with the default resolver gives the
same result with any resolver that loads ordinary cells as themselves. -/
theorem dictLookupAuxWithCellsF_of_rejectSpecial (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r) :
    ∀ (f : Nat) (cell : Cell) (key : BitString) (pos remaining : Nat) (x : Option Slice × Array Cell),
      dictLookupAuxWithCellsF Cell.rejectSpecial f cell key pos remaining = .ok x →
        dictLookupAuxWithCellsF r f cell key pos remaining = .ok x := by
  intro f
  induction f with
  | zero => intro cell key pos remaining x h; exact h
  | succ f ih =>
    intro cell key pos remaining x h
    simp only [dictLookupAuxWithCellsF] at h ⊢
    exact dictLookupWithCellsStep_of_rejectSpecial key pos _ _
      (fun c p _ _ rm y hy => ih c key p rm y hy) cell remaining r hr x h

theorem dictLookupWithCells_of_rejectSpecial (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r)
    (root : Option Cell) (key : BitString) (x : Option Slice × Array Cell)
    (h : dictLookupWithCells root key = .ok x) : dictLookupWithCells root key r = .ok x := by
  cases root with
  | none => exact h
  | some cell =>
    simp only [dictLookupWithCells, dictLookupAuxWithCells] at h ⊢
    exact dictLookupAuxWithCellsF_of_rejectSpecial r hr _ _ _ _ _ _ h

/-- The lookup of `key` in the dictionary `root` as the instructions `DICT*GET*` make it (with the
default resolver: a concrete dictionary is decided by the kernel): the value found, and the cells
loaded after the root (C++ `Dictionary::lookup` loads the nodes on the key's path; the model
charges the root first, then the visited cells but the root). -/
def dictLookupLoads (root : Cell) (key : BitString) : Except Excno (Option Slice × List Cell) :=
  match dictLookupWithCells (some root) key with
  | .ok (r, cells) => .ok (r, (cells.filter (fun c => c != root)).toList)
  | .error e => .error e

end TvmLean

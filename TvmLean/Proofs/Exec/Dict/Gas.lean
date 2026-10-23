import TvmLean.Proofs.Exec.Dict.Map

/-!
# Loads and creations of cells in closed form

A dictionary update on a symbolic dictionary loads the nodes on the key's path and creates the
nodes it rebuilds: a list of cells and a number of creations that are terms, not literals. The
model charges them one at a time (`VM.registerCellLoadList`, `VM.chargeCellCreates`), each charge
out of gas at once from version 4 (`VmState.gasExhaustedNow`). A list of charges runs out of gas iff
one of them does, at the first one that does; the last one alone does not tell, as the gas left is a
C++ `long long` that wraps around (`GasLimits.remaining`):

* `VM.loadOrd cells` (the loads of ordinary cells, `VM.run_registerCellLoadList_ord`): out of gas
  at the first load that exhausts it (`VmState.loadsUntilOut`), or the state after all the loads
  (`VmState.loadsAfter`: the loaded cells `cellsLoadedAfterList`, the gas `cellLoadGasList`, terms
  of the cells);
* `VM.run_chargeCellCreates`: `n` creations, out of gas at the first one that exhausts it
  (`VmState.createsUntilOut`), or the gas of all of them.

The states are written as the state with its gas and loaded cells changed (`VmState.loadsAfter_eq`,
`VmState.loadsUntilOut_eq`, `VmState.createsUntilOut_eq`), so that `vm_run` keeps stepping.
-/

namespace TvmLean

/-- The state after loading `cells` in order. -/
def VmState.loadsAfter (st : VmState) : List Cell → VmState
  | [] => st
  | c :: cs => (st.registerCellLoad c).loadsAfter cs

/-- The state at the first load of `cells` that exhausts the gas (after all of them if none does). -/
def VmState.loadsUntilOut (st : VmState) : List Cell → VmState
  | [] => st
  | c :: cs => if (st.registerCellLoad c).gasExhaustedNow then st.registerCellLoad c
    else (st.registerCellLoad c).loadsUntilOut cs

/-- The loads of the ordinary cells `cells`, in order (`VM.registerCellLoadList` of ordinary cells,
`VM.run_registerCellLoadList_ord`). -/
def VM.loadOrd (cells : List Cell) : VM Unit := ExceptT.mk fun st =>
  if (!cells.isEmpty && (st.loadsUntilOut cells).gasExhaustedNow) = true then
    (.error .outOfGas, st.loadsUntilOut cells)
  else (.ok (), st.loadsAfter cells)

@[vm_run] theorem VM.run_loadOrd (cells : List Cell) (st : VmState) :
    ExceptT.run (VM.loadOrd cells) st =
      if (!cells.isEmpty && (st.loadsUntilOut cells).gasExhaustedNow) = true then
        (.error .outOfGas, st.loadsUntilOut cells)
      else (.ok (), st.loadsAfter cells) := rfl

attribute [vm_run] List.isEmpty_cons List.isEmpty_nil

theorem VmState.registerCellLoad_gv (st : VmState) (c : Cell) :
    (st.registerCellLoad c).globalVersion = st.globalVersion := by
  rw [VmState.registerCellLoad_eq]

theorem VmState.registerCellLoad_gasRemaining (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasRemaining ≤ st.gas.gasRemaining := by
  rw [VmState.registerCellLoad_eq]
  have := cellLoadGas_bounds st.loadedCells c
  simp only [GasLimits.consume]
  omega

/-- **The loads of a list of ordinary cells**, in closed form. -/
theorem VM.run_registerCellLoadList_ord (cells : List Cell) (h : ∀ c ∈ cells, c.special = false) (st : VmState) :
    ExceptT.run (VM.registerCellLoadList cells) st = ExceptT.run (VM.loadOrd cells) st := by
  induction cells generalizing st with
  | nil => rfl
  | cons c cs ih =>
    rw [VM.run_registerCellLoadList_cons, VM.run_registerCellLoad_ordinary c st (h c (by simp)), VM.run_loadOrd]
    simp only [VmState.loadsAfter, VmState.loadsUntilOut, List.isEmpty_cons, Bool.not_false, Bool.true_and]
    by_cases hx : (st.registerCellLoad c).gasExhaustedNow = true
    · simp only [hx, if_true]; rfl
    · rw [if_neg hx, if_neg hx, VM.bindRes_ok, ih (fun x hx' => h x (List.mem_cons_of_mem _ hx')), VM.run_loadOrd]
      cases cs with
      | nil => simp [VmState.loadsAfter, VmState.loadsUntilOut, hx]
      | cons d ds => simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and]

/-! ## The states, written out -/

/-- The gas of loading `cells` in order, and the hashes of the loaded cells after, from the
loaded cells `loaded`. -/
def loadsFold (loaded : Array (Array UInt8)) (cells : List Cell) : Int × Array (Array UInt8) :=
  cells.foldl (fun acc c => (acc.1 + cellLoadGas acc.2 c, cellsLoadedAfter acc.2 c)) (0, loaded)

theorem loadsFold_nil (loaded : Array (Array UInt8)) : loadsFold loaded [] = (0, loaded) := rfl

theorem loadsFold_cons (loaded : Array (Array UInt8)) (c : Cell) (cs : List Cell) :
    loadsFold loaded (c :: cs) =
      (cellLoadGas loaded c + (loadsFold (cellsLoadedAfter loaded c) cs).1,
        (loadsFold (cellsLoadedAfter loaded c) cs).2) := by
  unfold loadsFold
  simp only [List.foldl_cons, Int.zero_add]
  generalize cellLoadGas loaded c = g
  generalize cellsLoadedAfter loaded c = l
  suffices ∀ (g g' : Int) (l : Array (Array UInt8)),
      (cs.foldl (fun acc c => (acc.1 + cellLoadGas acc.2 c, cellsLoadedAfter acc.2 c)) (g + g', l)) =
        (g + (cs.foldl (fun acc c => (acc.1 + cellLoadGas acc.2 c, cellsLoadedAfter acc.2 c)) (g', l)).1,
          (cs.foldl (fun acc c => (acc.1 + cellLoadGas acc.2 c, cellsLoadedAfter acc.2 c)) (g', l)).2) by
    simpa using this g 0 l
  induction cs with
  | nil => intro g g' l; rfl
  | cons d ds ih =>
    intro g g' l
    simp only [List.foldl_cons]
    rw [Int.add_assoc, ih]

/-- The gas of loading `cells` in order after the cells whose hashes are `loaded` (25 or 100
each, `cellLoadGas`): a term. -/
@[irreducible] def cellLoadGasList (loaded : Array (Array UInt8)) (cells : List Cell) : Int :=
  (loadsFold loaded cells).1

/-- The hashes of the loaded cells after loading `cells` in order. -/
@[irreducible] def cellsLoadedAfterList (loaded : Array (Array UInt8)) (cells : List Cell) :
    Array (Array UInt8) := (loadsFold loaded cells).2

theorem cellLoadGasList_nil (loaded : Array (Array UInt8)) : cellLoadGasList loaded [] = 0 := by
  unfold cellLoadGasList; rfl

theorem cellLoadGasList_cons (loaded : Array (Array UInt8)) (c : Cell) (cs : List Cell) :
    cellLoadGasList loaded (c :: cs) = cellLoadGas loaded c + cellLoadGasList (cellsLoadedAfter loaded c) cs := by
  unfold cellLoadGasList; rw [loadsFold_cons]

theorem cellsLoadedAfterList_nil (loaded : Array (Array UInt8)) : cellsLoadedAfterList loaded [] = loaded := by
  unfold cellsLoadedAfterList; rfl

theorem cellsLoadedAfterList_cons (loaded : Array (Array UInt8)) (c : Cell) (cs : List Cell) :
    cellsLoadedAfterList loaded (c :: cs) = cellsLoadedAfterList (cellsLoadedAfter loaded c) cs := by
  unfold cellsLoadedAfterList; rw [loadsFold_cons]

theorem GasLimits.consume_consume (g : GasLimits) (a b : Int) : (g.consume a).consume b = g.consume (a + b) := by
  simp only [GasLimits.consume, Int.sub_sub]

theorem GasLimits.consume_zero (g : GasLimits) : g.consume 0 = g := by
  simp only [GasLimits.consume, Int.sub_zero]

/-- The loads of a list, written out: the loaded cells and the gas change. -/
@[vm_run] theorem VmState.loadsAfter_eq (st : VmState) (cells : List Cell) :
    st.loadsAfter cells =
      { st with loadedCells := cellsLoadedAfterList st.loadedCells cells,
                gas := st.gas.consume (cellLoadGasList st.loadedCells cells) } := by
  induction cells generalizing st with
  | nil =>
    simp only [VmState.loadsAfter, cellsLoadedAfterList_nil, cellLoadGasList_nil, GasLimits.consume_zero]
  | cons c cs ih =>
    simp only [VmState.loadsAfter, ih, VmState.registerCellLoad_eq, cellsLoadedAfterList_cons, cellLoadGasList_cons,
      GasLimits.consume_consume]

/-- The bounds of the gas of a list of loads (25 to 100 each). -/
theorem cellLoadGasList_bounds (loaded : Array (Array UInt8)) (cells : List Cell) :
    25 * cells.length ≤ cellLoadGasList loaded cells ∧ cellLoadGasList loaded cells ≤ 100 * cells.length := by
  induction cells generalizing loaded with
  | nil => simp [cellLoadGasList_nil]
  | cons c cs ih =>
    have := cellLoadGas_bounds loaded c
    have := ih (cellsLoadedAfter loaded c)
    simp only [cellLoadGasList_cons, List.length_cons]
    omega

/-- The gas when the loads of `cells` run out of gas. -/
@[irreducible] def loadsOutGas (st : VmState) (cells : List Cell) : GasLimits := (st.loadsUntilOut cells).gas

/-- The loaded cells when the loads of `cells` run out of gas. -/
@[irreducible] def loadsOutLoaded (st : VmState) (cells : List Cell) : Array (Array UInt8) :=
  (st.loadsUntilOut cells).loadedCells

theorem VmState.loadsUntilOut_fields (st : VmState) (cells : List Cell) :
    st.loadsUntilOut cells =
      { st with loadedCells := (st.loadsUntilOut cells).loadedCells, gas := (st.loadsUntilOut cells).gas } := by
  induction cells generalizing st with
  | nil => rfl
  | cons c cs ih =>
    simp only [VmState.loadsUntilOut]
    split
    · rw [VmState.registerCellLoad_eq]
    · rw [ih]; simp only [VmState.registerCellLoad_eq]

/-- The state when the loads of `cells` run out of gas, written out. -/
@[vm_run] theorem VmState.loadsUntilOut_eq (st : VmState) (cells : List Cell) :
    st.loadsUntilOut cells = { st with loadedCells := loadsOutLoaded st cells, gas := loadsOutGas st cells } := by
  unfold loadsOutLoaded loadsOutGas
  exact VmState.loadsUntilOut_fields st cells

/-! ## Creations -/

/-- The state at the first of `n` creations that exhausts the gas (after all of them if none does). -/
def VmState.createsUntilOut (st : VmState) : Nat → VmState
  | 0 => st
  | n + 1 => if (st.consumeGas cellCreateGasPrice).gasExhaustedNow then st.consumeGas cellCreateGasPrice
    else (st.consumeGas cellCreateGasPrice).createsUntilOut n

/-- The gas when `n` creations run out of gas. -/
@[irreducible] def createsOutGas (st : VmState) (n : Nat) : GasLimits := (st.createsUntilOut n).gas

theorem VmState.createsUntilOut_fields (st : VmState) (n : Nat) :
    st.createsUntilOut n = { st with gas := (st.createsUntilOut n).gas } := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    simp only [VmState.createsUntilOut]
    split
    · rfl
    · rw [ih]; rfl

@[vm_run] theorem VmState.createsUntilOut_eq (st : VmState) (n : Nat) :
    st.createsUntilOut n = { st with gas := createsOutGas st n } := by
  unfold createsOutGas
  exact VmState.createsUntilOut_fields st n

theorem VmState.consumeGas_consumeGas (st : VmState) (a b : Int) :
    (st.consumeGas a).consumeGas b = st.consumeGas (a + b) := by
  simp only [VmState.consumeGas, GasLimits.consume_consume]

/-- **`n` cell creations** (C++ `register_cell_create`, each out of gas at once), in closed form. -/
@[vm_run] theorem VM.run_chargeCellCreates (n : Nat) (st : VmState) :
    ExceptT.run (VM.chargeCellCreates n) st =
      if (n != 0 && (st.createsUntilOut n).gasExhaustedNow) = true then
        (.error .outOfGas, st.createsUntilOut n)
      else (.ok (), st.consumeGas (n * cellCreateGasPrice)) := by
  have key : ∀ (l : List Nat) (st : VmState),
      ExceptT.run (forIn l PUnit.unit fun _ _ => do
          VM.consumeGas cellCreateGasPrice; pure (ForInStep.yield PUnit.unit) : VM PUnit) st =
        if (l.length != 0 && (st.createsUntilOut l.length).gasExhaustedNow) = true then
          (.error .outOfGas, st.createsUntilOut l.length)
        else (.ok PUnit.unit, st.consumeGas (l.length * cellCreateGasPrice)) := by
    intro l
    induction l with
    | nil =>
      intro st
      simp [VmState.consumeGas, GasLimits.consume_zero]
      rfl
    | cons a l ih =>
      intro st
      simp only [List.forIn_cons, VM.run_bind, VM.run_consumeGas]
      by_cases hx : (st.consumeGas cellCreateGasPrice).gasExhaustedNow = true
      · rw [if_pos hx]
        simp only [List.length_cons, VmState.createsUntilOut, hx, if_true, Bool.and_true, VM.bindRes_error]
        rfl
      · rw [if_neg hx, VM.bindRes_ok]
        simp only [VM.run_pure, VM.bindRes_ok]
        rw [ih, VmState.consumeGas_consumeGas]
        have e : cellCreateGasPrice + ↑l.length * cellCreateGasPrice = ↑(a :: l).length * cellCreateGasPrice := by
          simp only [List.length_cons, cellCreateGasPrice]; omega
        rw [e]
        simp only [List.length_cons, VmState.createsUntilOut, hx, Bool.false_eq_true, if_false]
        by_cases hl : l.length = 0
        · simp [hl, VmState.createsUntilOut, hx]
        · have h1 : (l.length != 0) = true := by simpa using hl
          have h2 : (l.length + 1 != 0) = true := by simp
          simp only [h1, h2, Bool.true_and]
  simp only [VM.chargeCellCreates, VM.run_bind, Std.Range.forIn_eq_forIn_range']
  have hsz : [:n].size = n := by simp [Std.Range.size]
  rw [hsz]
  rw [show (forIn (List.range' 0 n) PUnit.unit fun _ _ => do
      VM.consumeGas cellCreateGasPrice; pure (ForInStep.yield PUnit.unit) : VM PUnit).run st =
      ExceptT.run (forIn (List.range' 0 n) PUnit.unit fun _ _ => do
        VM.consumeGas cellCreateGasPrice; pure (ForInStep.yield PUnit.unit) : VM PUnit) st from rfl, key]
  simp only [List.length_range']
  split <;> rfl

end TvmLean

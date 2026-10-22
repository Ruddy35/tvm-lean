import TvmLean.Proofs.Exec.Spec.Dispatch

/-!
# Specifications: dictionary lookups

In the format of `Proofs/Exec/Spec/Stack.lean`, on any dictionary (a symbolic root cell). The
dictionary is seen through its abstract map `Dict.get root key` (the value slice of `key`, `none`
if absent: the lookup of the model with the default resolver, which refuses exotic cells). A
lookup that succeeds (`dictLookupLoads root key = .ok (r, loads)`: the value and the cells visited
after the root) gives `Dict.get (some root) key = r` (`Dict.get_of_lookupLoads`), and the VM's
lookup, whose resolver follows libraries, the same result (`dictLookupWithCells_of_rejectSpecial`).
The loads are charged in order (`VM.registerCellLoadList`), their gas symbolic.

* `DICT{I,U}GET` (`dictGet true unsigned false`) and `DICTGET` (slice keys, `dictGet false _ false`):
  `dictGetInt_found`, `dictGetInt_notFound`, `dictGetInt_noKey`, `dictGetInt_empty`,
  `dictGetSlice_found`, `dictGetSlice_notFound`, `dictGetSlice_short`.
* the `*REF` forms (the value is one reference, dict_err else): `dictGetIntRef_found`,
  `dictGetIntRef_notFound`.

For a concrete dictionary and key both facts are closed and the kernel decides them
(`Proofs/Exec/Tactic.lean`, as for the method dispatch).
-/

namespace TvmLean

/-- The abstract map of a dictionary: the value of `key` in the dictionary `root` (`none` the
empty dictionary), as the lookup of the model finds it with the default resolver; `none` if the
key is absent or the lookup fails (an ill-formed dictionary, an exotic cell). -/
def Dict.get (root : Option Cell) (key : BitString) : Option Slice :=
  match dictLookupWithCells root key with
  | .ok (v, _) => v
  | .error _ => none

/-- The empty dictionary maps every key to nothing. -/
@[simp] theorem Dict.get_none (key : BitString) : Dict.get none key = none := rfl

/-- A lookup that succeeded finds the value of the abstract map. -/
theorem Dict.get_of_lookupLoads {root : Cell} {key : BitString} {r : Option Slice} {loads : List Cell}
    (h : dictLookupLoads root key = .ok (r, loads)) : Dict.get (some root) key = r := by
  obtain ⟨cells, hc, _⟩ := Spec.dictLookupLoads_ok h
  simp [Dict.get, hc]

namespace Spec

/-- `DICT{I,U}GET` (C++ `exec_dict_get`, dictops.cpp) when the key is found: the root and the
visited cells are loaded, the value slice and `-1` are pushed. -/
@[vm_spec] theorem dictGetInt_found (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (key : BitString) (val : Slice) (loads : List Cell)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hkey : dictKeyBits? idx n.toNat unsigned = some key)
    (hlook : dictLookupLoads root key = .ok (some val, loads)) :
    ExceptT.run (execInstr (.dictGet true unsigned false)) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => do VM.push (.slice val); VM.pushSmallInt (-1)) := by
  obtain ⟨cells, hc, hl⟩ := dictLookupLoads_ok hlook
  have hc' : ∀ libs gv refused, dictLookupWithCells (some root) key
      (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (some val, cells) :=
    fun libs gv refused => dictLookupWithCells_of_rejectSpecial _ (resolvesOrdinary_library libs gv refused) _ _ _ hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hkey, hc', hn1, hn', VM.cellResolver, VM.forIn_registerCellLoad, hl]

/-- `DICT{I,U}GET` when the key is not in the dictionary: the root and the visited cells are
loaded, `0` is pushed. -/
@[vm_spec] theorem dictGetInt_notFound (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (key : BitString) (loads : List Cell)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hkey : dictKeyBits? idx n.toNat unsigned = some key)
    (hlook : dictLookupLoads root key = .ok (none, loads)) :
    ExceptT.run (execInstr (.dictGet true unsigned false)) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => VM.pushSmallInt 0) := by
  obtain ⟨cells, hc, hl⟩ := dictLookupLoads_ok hlook
  have hc' : ∀ libs gv refused, dictLookupWithCells (some root) key
      (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (none, cells) :=
    fun libs gv refused => dictLookupWithCells_of_rejectSpecial _ (resolvesOrdinary_library libs gv refused) _ _ _ hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hkey, hc', hn1, hn', VM.cellResolver, VM.forIn_registerCellLoad, hl]

/-- `DICT{I,U}GET` with a key out of the range of `n`-bit keys: not found (`0`), nothing loaded. -/
@[vm_spec] theorem dictGetInt_noKey (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hkey : dictKeyBits? idx n.toNat unsigned = none) :
    ExceptT.run (execInstr (.dictGet true unsigned false)) st =
      (.ok (), { st with stack := s.push (.int (.num 0)) }) := by
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hkey, hn1, hn', VM.popMaybeCell]

/-- `DICT{I,U}GET` on the empty dictionary (`null`): not found (`0`). -/
@[vm_spec] theorem dictGetInt_empty (st : VmState) (s : Stack) (idx : Int) (n : Int) (unsigned : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push .null).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictGet true unsigned false)) st =
      (.ok (), { st with stack := s.push (.int (.num 0)) }) := by
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned <;>
    (vm_simp [hs, hk, hn1, hn', VM.popMaybeCell, dictLookupWithCells_none, VM.forIn_registerCellLoad]
     try rfl)

/-- `DICT{I,U}GETREF` when the key is found: the value must be exactly one reference (dict_err
else), which is pushed with `-1`. -/
@[vm_spec] theorem dictGetIntRef_found (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (key : BitString) (val : Slice) (loads : List Cell)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hkey : dictKeyBits? idx n.toNat unsigned = some key)
    (hlook : dictLookupLoads root key = .ok (some val, loads)) :
    ExceptT.run (execInstr (.dictGet true unsigned true)) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => if val.bitsRemaining = 0 ∧ val.refsRemaining = 1 then
            do VM.push (.cell (val.cell.refs[val.refPos]!)); VM.pushSmallInt (-1)
          else throw .dictErr) := by
  obtain ⟨cells, hc, hl⟩ := dictLookupLoads_ok hlook
  have hc' : ∀ libs gv refused, dictLookupWithCells (some root) key
      (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (some val, cells) :=
    fun libs gv refused => dictLookupWithCells_of_rejectSpecial _ (resolvesOrdinary_library libs gv refused) _ _ _ hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hkey, hc', hn1, hn', VM.cellResolver, VM.forIn_registerCellLoad, hl]

/-- `DICT{I,U}GETREF` when the key is not in the dictionary: `0`. -/
@[vm_spec] theorem dictGetIntRef_notFound (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (key : BitString) (loads : List Cell)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hkey : dictKeyBits? idx n.toNat unsigned = some key)
    (hlook : dictLookupLoads root key = .ok (none, loads)) :
    ExceptT.run (execInstr (.dictGet true unsigned true)) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => VM.pushSmallInt 0) := by
  obtain ⟨cells, hc, hl⟩ := dictLookupLoads_ok hlook
  have hc' : ∀ libs gv refused, dictLookupWithCells (some root) key
      (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (none, cells) :=
    fun libs gv refused => dictLookupWithCells_of_rejectSpecial _ (resolvesOrdinary_library libs gv refused) _ _ _ hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hkey, hc', hn1, hn', VM.cellResolver, VM.forIn_registerCellLoad, hl]

/-- `DICTGET` (slice keys, C++ `exec_dict_get`) when the first `n` bits of the key slice are found:
the root and the visited cells are loaded, the value slice and `-1` are pushed. -/
@[vm_spec] theorem dictGetSlice_found (st : VmState) (s : Stack) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (val : Slice) (loads : List Cell)
    (hs : st.stack = ((s.push (.slice k)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hk : k.haveBits n.toNat = true)
    (hlook : dictLookupLoads root (k.readBits n.toNat) = .ok (some val, loads)) :
    ExceptT.run (execInstr (.dictGet false unsigned false)) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => do VM.push (.slice val); VM.pushSmallInt (-1)) := by
  obtain ⟨cells, hc, hl⟩ := dictLookupLoads_ok hlook
  have hc' : ∀ libs gv refused, dictLookupWithCells (some root) (k.readBits n.toNat)
      (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (some val, cells) :=
    fun libs gv refused => dictLookupWithCells_of_rejectSpecial _ (resolvesOrdinary_library libs gv refused) _ _ _ hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hk, hc', hn1, hn', VM.cellResolver, VM.forIn_registerCellLoad, hl]

/-- `DICTGET` (slice keys) when the key is not in the dictionary: `0`. -/
@[vm_spec] theorem dictGetSlice_notFound (st : VmState) (s : Stack) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (loads : List Cell)
    (hs : st.stack = ((s.push (.slice k)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hk : k.haveBits n.toNat = true)
    (hlook : dictLookupLoads root (k.readBits n.toNat) = .ok (none, loads)) :
    ExceptT.run (execInstr (.dictGet false unsigned false)) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => VM.pushSmallInt 0) := by
  obtain ⟨cells, hc, hl⟩ := dictLookupLoads_ok hlook
  have hc' : ∀ libs gv refused, dictLookupWithCells (some root) (k.readBits n.toNat)
      (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (none, cells) :=
    fun libs gv refused => dictLookupWithCells_of_rejectSpecial _ (resolvesOrdinary_library libs gv refused) _ _ _ hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hk, hc', hn1, hn', VM.cellResolver, VM.forIn_registerCellLoad, hl]

/-- `DICTGET` (slice keys) with a key slice shorter than `n` bits: cell_und, nothing loaded. -/
@[vm_spec] theorem dictGetSlice_short (st : VmState) (s : Stack) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool)
    (hs : st.stack = ((s.push (.slice k)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hk : k.haveBits n.toNat = false) :
    ExceptT.run (execInstr (.dictGet false unsigned false)) st = (.error .cellUnd, { st with stack := s }) := by
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hk, hn1, hn', VM.popMaybeCell]

end Spec

end TvmLean

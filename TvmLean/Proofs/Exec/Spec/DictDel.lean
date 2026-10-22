import TvmLean.Proofs.Exec.Spec.DictSet

/-!
# Specifications: lookups and deletes on symbolic dictionaries

`DICTGET` and `DICTDEL` (all key forms) on a well-formed dictionary (`Dict.WF`), stated through the
map of the dictionary (`Dict.get`, `Dict.value`), as `Proofs/Exec/Spec/DictSet.lean` states the
sets:

* `DICT{I,U}GET{REF}` and `DICTGET{REF}`: `Spec.dictGetInt_wf`, `Spec.dictGetSlice_wf`: the root
  and the cells on the key's path loaded (`VM.loadOrd`), then the value `Dict.get` finds pushed
  with `-1`, or `0` (`Dict.getRun`);
* `DICT{I,U}DEL` and `DICTDEL`: `Spec.dictDelInt`, `Spec.dictDelSlice` (and on `null`,
  `Spec.dictDelIntEmpty`, `Spec.dictDelSliceEmpty`): the loads, the cells created charged, the
  new root and the flag pushed (`Dict.delRun`), the result `Dict.delRes` known through
  `Dict.value_delRes` (the key gone, every other key as before) and `Dict.WF.delRes`.

The handlers are written again with their tails named (`DictTail.dictGet`, `DictTail.dictDel`,
the same code: `DictTail.getHandler_eq`, `DictTail.delHandler_eq`), so that `vm_simp` runs the pops
and leaves the tail, which `DictTail.getTail_run` and `DictTail.delTail_run` state on a
well-formed dictionary.
-/

namespace DictTail

open TvmLean

/-- The tail of `DICTGET` after the key is read (`TvmLean/Semantics/Exec/Dict/DictGet.lean`). -/
def getTail (dictCell? : Option Cell) (keyBits : BitString) (byRef : Bool) : VM Unit := do
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()
  match dictLookupWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits with
  | .error e =>
      let loadedAll := dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictCell? keyBits
      let loaded :=
        match dictCell? with
        | none => loadedAll
        | some root => loadedAll.filter (fun c => c != root)
      for c in loaded do
        VM.registerCellLoad c
      throw e
  | .ok (none, loaded) =>
      let loaded :=
        match dictCell? with
        | none => loaded
        | some root => loaded.filter (fun c => c != root)
      for c in loaded do
        VM.registerCellLoad c
      VM.pushSmallInt 0
  | .ok (some valueSlice, loaded) =>
      let loaded :=
        match dictCell? with
        | none => loaded
        | some root => loaded.filter (fun c => c != root)
      for c in loaded do
        VM.registerCellLoad c
      if byRef then
        if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
          let c := valueSlice.cell.refs[valueSlice.refPos]!
          VM.push (.cell c)
          VM.pushSmallInt (-1)
        else
          throw .dictErr
      else
        VM.push (.slice valueSlice)
        VM.pushSmallInt (-1)

/-- The handler of `DICTGET`, with its tail named. -/
def dictGet (intKey unsigned byRef : Bool) : VM Unit := do
  VM.checkUnderflow 3
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let keyBits? : Option BitString ←
    if intKey then
      let idx ← VM.popIntFinite
      pure (dictKeyBits? idx n unsigned)
    else
      let keySlice ← VM.popSlice
      if keySlice.haveBits n then
        pure (some (keySlice.readBits n))
      else
        throw .cellUnd
  match keyBits? with
  | none =>
      VM.pushSmallInt 0
  | some keyBits => getTail dictCell? keyBits byRef

/-- `pushBool` of `TvmLean/Semantics/Exec/Dict/Ext.lean` (private there). -/
def pushBool (b : Bool) : VM Unit :=
  VM.pushSmallInt (if b then -1 else 0)

/-- `pushDictRoot` of `TvmLean/Semantics/Exec/Dict/Ext.lean` (private there). -/
def pushDictRoot (c? : Option Cell) : VM Unit := do
  match c? with
  | none => VM.push .null
  | some c => VM.push (.cell c)

/-- `consumeCreatedGas` of `TvmLean/Semantics/Exec/Dict/Ext.lean` (private there). -/
def consumeCreatedGas (created : Nat) : VM Unit :=
  VM.chargeCellCreates created

/-- `registerLoaded` of `TvmLean/Semantics/Exec/Dict/Ext.lean` (private there). -/
def registerLoaded (loaded : Array Cell) : VM Unit := do
  for c in loaded do
    VM.registerCellLoad c

/-- `prechargeRootLoad` of `TvmLean/Semantics/Exec/Dict/Ext.lean` (private there). -/
def prechargeRootLoad (dictCell? : Option Cell) : VM Unit := do
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()

/-- `loadedWithoutRoot` of `TvmLean/Semantics/Exec/Dict/Ext.lean` (private there). -/
def loadedWithoutRoot (dictCell? : Option Cell) (loaded : Array Cell) : Array Cell :=
  match dictCell? with
  | none => loaded
  | some root => loaded.filter (fun c => c != root)

/-- The tail of `DICTDEL` after the key is read. -/
def delTail (dictCell? : Option Cell) (keyBits : BitString) : VM Unit := do
  prechargeRootLoad dictCell?
  match dictDeleteWithLoads (resolve := (← VM.cellResolver)) dictCell? keyBits with
  | .error (e, loaded0) =>
      registerLoaded (loadedWithoutRoot dictCell? loaded0)
      throw e
  | .ok (oldVal?, newRoot?, created, loaded) =>
      let loaded := loadedWithoutRoot dictCell? loaded
      registerLoaded loaded
      consumeCreatedGas created
      pushDictRoot newRoot?
      pushBool (oldVal?.isSome)

/-- The handler of `DICTDEL` (`.dictExt (.del ..)`), with its tail named. -/
def dictDel (intKey unsigned : Bool) : VM Unit := do
  VM.checkUnderflow 3
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let keyBits? : Option BitString ←
    if intKey then
      let idx ← VM.popIntFinite
      pure (dictKeyBits? idx n unsigned)
    else
      let keySlice ← VM.popSlice
      if keySlice.haveBits n then
        pure (some (keySlice.readBits n))
      else
        throw .cellUnd
  match keyBits? with
  | none =>
      throw .rangeChk
  | some keyBits => delTail dictCell? keyBits

end DictTail

namespace TvmLean

/-! ## Lookups -/

/-- The cells a lookup of `key` loads after the root (`DICTGET` skips the copies of the root). -/
@[irreducible] def Dict.getRest (root : Cell) (key : BitString) : List Cell :=
  match dictLookupWithCells (some root) key with
  | .ok (_, cells) => (cells.filter (fun c => c != root)).toList
  | .error _ => []

/-- **A lookup on a well-formed dictionary**, as `DICTGET` runs it: the root and the cells on the
key's path loaded (`VM.loadOrd`), then the value of the map pushed with `-1` (with `byRef`, the
reference the value must consist of, dict_err else), or `0` if the key is absent. -/
def Dict.getRun (root : Cell) (key : BitString) (byRef : Bool) : VM Unit := do
  VM.loadOrd (root :: Dict.getRest root key)
  match Dict.get (some root) key with
  | none => VM.pushSmallInt 0
  | some v =>
      if byRef then
        if v.bitsRemaining == 0 && v.refsRemaining == 1 then
          VM.push (.cell (v.cell.refs[v.refPos]!))
          VM.pushSmallInt (-1)
        else
          throw .dictErr
      else
        VM.push (.slice v)
        VM.pushSmallInt (-1)

theorem DictTail.filter_ord {cells : Array Cell} (root : Cell) (h : ∀ x ∈ cells.toList, x.special = false) :
    ∀ x ∈ (cells.filter (fun c => c != root)).toList, x.special = false := by
  intro x hx
  simp only [Array.toList_filter, List.mem_filter] at hx
  exact h x hx.1

/-- **The tail of `DICTGET` on a well-formed dictionary is `Dict.getRun`.** The lookup with the
VM's resolver is the lookup with the default resolver (`lookup_resolve`), it succeeds, and the
cells it visits are ordinary (`lookup_loaded`): their loads are one closed form. -/
theorem DictTail.getTail_run (st : VmState) (root : Cell) (key : BitString) (byRef : Bool)
    (hwf : Dict.WF (some root) key.size) :
    ExceptT.run (DictTail.getTail (some root) key byRef) st = ExceptT.run (Dict.getRun root key byRef) st := by
  obtain ⟨⟨v, cells⟩, hl⟩ := hwf key rfl
  have hres : ∀ libs gv refused, dictLookupWithCells (some root) key
      (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (v, cells) := by
    intro libs gv refused
    rw [DictMap.lookup_resolve _ (resolvesOrdinary_library libs gv refused) hwf rfl]
    exact hl
  have hord := DictTail.filter_ord root (DictMap.lookup_loaded hwf hl)
  have hget : Dict.get (some root) key = v := by simp [Dict.get, hl]
  have hrest : Dict.getRest root key = (cells.filter (fun c => c != root)).toList := by
    unfold Dict.getRest; rw [hl]
  have hc := DictMap.WF_root_ordinary hwf
  unfold DictTail.getTail Dict.getRun
  rw [hget, hrest]
  simp only [VM.run_bind, VM.run_registerCellLoad_ordinary root st hc, VM.run_loadOrd_cons]
  split
  · rfl
  · cases v with
    | none =>
      simp only [VM.bindRes_ok, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, hres,
        VM.forIn_registerCellLoad, VM.run_registerCellLoadList_ord _ hord, VM.bindRes_bindRes_pure]
    | some v =>
      simp only [VM.bindRes_ok, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, hres,
        VM.forIn_registerCellLoad, VM.run_registerCellLoadList_ord _ hord, VM.bindRes_bindRes_pure]

/-- `DICTGET` runs as `DictTail.dictGet` (the same code). -/
theorem DictTail.getHandler_eq (intKey unsigned byRef : Bool) (st : VmState) :
    ExceptT.run (execInstr (.dictGet intKey unsigned byRef)) st =
      ExceptT.run (DictTail.dictGet intKey unsigned byRef) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

/-- The value of a reference read back (`DICT*GETREF` after `DICT*SETREF`): a value whose contents
are the reference `c` alone has no bits and one reference, `c`. -/
theorem DictTail.getElem_of_extract {a : Array Cell} {i : Nat} {c : Cell} (h : a.extract i a.size = #[c]) :
    a[i]! = c := by
  have hs := congrArg Array.size h
  simp only [Array.size_extract, List.size_toArray, List.length_cons, List.length_nil] at hs
  have hlt : i < a.size := by omega
  have h0 := congrArg (fun x => x[0]!) h
  simp only at h0
  rw [getElem!_pos a i hlt]
  rw [getElem!_pos (a.extract i a.size) 0 (by simp; omega)] at h0
  simp only [Array.getElem_extract, Nat.add_zero] at h0
  simpa using h0

theorem Slice.ref_of_toCellRemaining {v : Slice} {c : Cell}
    (h : v.toCellRemaining = (DictMap.refB c).finalize) :
    v.bitsRemaining = 0 ∧ v.refsRemaining = 1 ∧ v.cell.refs[v.refPos]! = c := by
  simp only [Slice.toCellRemaining, DictMap.refB, Builder.finalize, Cell.mkOrdinary, Cell.mk.injEq] at h
  obtain ⟨hb, hr, -⟩ := h
  have hbs := congrArg Array.size hb
  have hrs := congrArg Array.size hr
  simp only [Array.size_extract, List.size_toArray, List.length_nil, List.length_cons] at hbs hrs
  exact ⟨by simp only [Slice.bitsRemaining]; omega, by simp only [Slice.refsRemaining]; omega,
    DictTail.getElem_of_extract hr⟩

/-- **Get after `DICTSET`**: the new root maps the key to a value with the contents stored. -/
theorem Dict.get_setSet {root : Option Cell} {key : BitString} {vb : Builder} {c : Cell} {created : Nat}
    {rest : List Cell} (hwf : Dict.WF root key.size) (h : Dict.setSetRes root key vb = .ok (c, created, rest)) :
    ∃ v, Dict.get (some c) key = some v ∧ v.toCellRemaining = vb.finalize := by
  have hv := Dict.value_setSet hwf h key rfl
  rw [if_pos rfl] at hv
  unfold Dict.value at hv
  cases hg : Dict.get (some c) key with
  | none => rw [hg] at hv; cases hv
  | some v => rw [hg] at hv; exact ⟨v, rfl, Option.some.inj hv⟩

/-! ## Deletes -/

/-- The cells a delete loads after the root (the copies of the root skipped). -/
def Dict.withoutRoot (root : Option Cell) (loaded : Array Cell) : List Cell :=
  (DictTail.loadedWithoutRoot root loaded).toList

/-- **The result of a delete** (C++ `dict_lookup_delete`) of `key` from the dictionary `root`:
whether the key was found, the new root, the number of cells created and the cells loaded after
the root; or the error with the cells loaded before it. As the model computes it (default
resolver); never unfolded by `vm_run`: known through `Dict.value_delRes` and `Dict.WF.delRes`. -/
@[irreducible] def Dict.delRes (root : Option Cell) (key : BitString) :
    Except (Excno × List Cell) (Bool × Option Cell × Nat × List Cell) :=
  match dictDeleteWithLoads root key with
  | .ok (old, r, created, loaded) => .ok (old.isSome, r, created, Dict.withoutRoot root loaded)
  | .error (e, loaded) => .error (e, Dict.withoutRoot root loaded)

/-- **A delete on a well-formed dictionary**, as `DICTDEL` runs it: the root and the cells on the
key's path loaded (`VM.loadOrd`), the cells created charged, the new root (`null` if empty) and the
flag of the key found pushed. -/
def Dict.delRun (root : Option Cell) (key : BitString) : VM Unit :=
  match Dict.delRes root key with
  | .error (e, rest) => do VM.loadOrd (Dict.loadsOf root rest); throw e
  | .ok (found, newRoot?, created, rest) => do
      VM.loadOrd (Dict.loadsOf root rest)
      VM.chargeCellCreates created
      match newRoot? with
      | none => VM.push .null
      | some c => VM.push (.cell c)
      VM.pushSmallInt (if found then -1 else 0)

/-- **Get after a delete, on the map**: the key is absent, every other key of the same length as
before; the flag tells whether the key had a value. -/
theorem Dict.value_delRes {root root' : Option Cell} {key : BitString} {found : Bool} {created : Nat}
    {rest : List Cell} (hwf : Dict.WF root key.size) (h : Dict.delRes root key = .ok (found, root', created, rest)) :
    found = (Dict.value root key).isSome ∧
      ∀ key' : BitString, key'.size = key.size →
        Dict.value root' key' = if key' = key then none else Dict.value root key' := by
  unfold Dict.delRes at h
  split at h
  · rename_i old r cr loaded hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -, -⟩ := h
    obtain ⟨h1, h2⟩ := Dict.value_deleteAny hwf hd
    refine ⟨?_, h2⟩
    rw [h1]
    cases old <;> rfl
  · cases h

/-- A delete keeps a dictionary well-formed. -/
theorem Dict.WF.delRes {root root' : Option Cell} {key : BitString} {found : Bool} {created : Nat}
    {rest : List Cell} {n : Nat} (hwf : Dict.WF root n) (hk : key.size = n)
    (h : Dict.delRes root key = .ok (found, root', created, rest)) : Dict.WF root' n := by
  subst hk
  unfold Dict.delRes at h
  split at h
  · rename_i old r cr loaded hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -, -⟩ := h
    exact Dict.WF.delete hwf hd
  · cases h

/-- **The tail of `DICTDEL` on a well-formed dictionary is `Dict.delRun`.** The delete with the
VM's resolver is the delete with the default resolver (`delete_resolve`), and the cells it loads
are ordinary (`deleteWithLoads_loaded`): their loads are one closed form. -/
theorem DictTail.delTail_run (st : VmState) (root : Option Cell) (key : BitString)
    (hwf : Dict.WF root key.size) :
    ExceptT.run (DictTail.delTail root key) st = ExceptT.run (Dict.delRun root key) st := by
  unfold DictTail.delTail Dict.delRun
  cases root with
  | none =>
    have hd : ∀ r, dictDeleteWithLoads none key r = .ok (none, none, 0, #[]) := fun _ => rfl
    have hres : Dict.delRes none key = .ok (false, none, 0, []) := by
      unfold Dict.delRes; rw [hd]; rfl
    rw [hres]
    simp only [DictTail.prechargeRootLoad, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure,
      VM.bindRes_ok, hd, Dict.loadsOf_none]
    rfl
  | some c =>
    have hc := DictMap.WF_root_ordinary hwf
    have hdr : ∀ libs gv refused, dictDeleteWithLoads (some c) key
        (fun c => (libraryResolveLoads libs gv c refused).2) = dictDeleteWithLoads (some c) key := by
      intro libs gv refused
      simp only [dictDeleteWithLoads]
      exact DictMap.delete_resolve _ (resolvesOrdinary_library libs gv refused) key.size c key 0 hwf
    have hord := DictMap.deleteWithLoads_loaded hwf
    cases hdel : dictDeleteWithLoads (some c) key with
    | error el =>
      obtain ⟨e, loaded⟩ := el
      have hres : Dict.delRes (some c) key = .error (e, Dict.withoutRoot (some c) loaded) := by
        unfold Dict.delRes; rw [hdel]
      rw [hdel] at hord
      simp only [DictMap.delLoads] at hord
      have hord' := DictTail.filter_ord c hord
      rw [hres]
      simp only [DictTail.prechargeRootLoad, VM.run_bind, VM.run_registerCellLoad_ordinary c st hc,
        Dict.loadsOf_some, Dict.withoutRoot, DictTail.loadedWithoutRoot, VM.run_loadOrd_cons]
      split
      · rfl
      · simp only [VM.bindRes_ok, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, hdr, hdel,
          DictTail.registerLoaded, VM.forIn_registerCellLoad,
          VM.run_registerCellLoadList_ord _ hord', VM.bindRes_bindRes_pure]
    | ok res =>
      obtain ⟨old, r, created, loaded⟩ := res
      have hres : Dict.delRes (some c) key = .ok (old.isSome, r, created, Dict.withoutRoot (some c) loaded) := by
        unfold Dict.delRes; rw [hdel]
      rw [hdel] at hord
      simp only [DictMap.delLoads] at hord
      have hord' := DictTail.filter_ord c hord
      rw [hres]
      simp only [DictTail.prechargeRootLoad, VM.run_bind, VM.run_registerCellLoad_ordinary c st hc,
        Dict.loadsOf_some, Dict.withoutRoot, DictTail.loadedWithoutRoot, VM.run_loadOrd_cons]
      split
      · rfl
      · simp only [VM.bindRes_ok, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, hdr, hdel,
          DictTail.registerLoaded, VM.forIn_registerCellLoad,
          VM.run_registerCellLoadList_ord _ hord', VM.bindRes_bindRes_pure, DictTail.consumeCreatedGas,
          DictTail.pushDictRoot, DictTail.pushBool]
        cases r <;> rfl

/-- `DICTDEL` runs as `DictTail.dictDel` (the same code). -/
theorem DictTail.delHandler_eq (intKey unsigned : Bool) (st : VmState) :
    ExceptT.run (execInstr (.dictExt (.del intKey unsigned))) st =
      ExceptT.run (DictTail.dictDel intKey unsigned) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl


/-! ## The specifications -/

namespace Spec

/-- C++ `exec_dict_get` (dictops.cpp:208) with an integer key (`DICT{I,U}GET{REF}`), on a well-formed
dictionary: `Dict.getRun` (a key out of the range of `n`-bit keys is not found: `0`). -/
@[vm_spec] theorem dictGetInt_wf (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned byRef : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictGet true unsigned byRef)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.ok (), { st with stack := s.push (.int (.num 0)) })
      | some key => ExceptT.run (Dict.getRun root key byRef) { st with stack := s } := by
  rw [DictTail.getHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictGet, hs, hk, hn1, hn', VM.popMaybeCell]
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← DictTail.getTail_run _ _ _ _ hwf']
    vm_simp [DictTail.dictGet, hs, hk, hn1, hn', VM.popMaybeCell]

/-- C++ `exec_dict_get` (dictops.cpp:208) with a slice key (`DICTGET{REF}`), on a well-formed
dictionary: `Dict.getRun` of the first `n` bits of the key (cell_und if it is shorter). -/
@[vm_spec] theorem dictGetSlice_wf (st : VmState) (s : Stack) (k : Slice) (root : Cell) (n : Int)
    (unsigned byRef : Bool)
    (hs : st.stack = ((s.push (.slice k)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictGet false unsigned byRef)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.getRun root (k.readBits n.toNat) byRef) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.getHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← DictTail.getTail_run _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictGet, hs, hk, hn1, hn', VM.popMaybeCell]
  · rw [if_neg hk]
    vm_simp [DictTail.dictGet, hs, hk, hn1, hn', VM.popMaybeCell]

/-- C++ `exec_dict_delete` (dictops.cpp:375) with an integer key (`DICT{I,U}DEL`), on a well-formed
dictionary: `Dict.delRun` (range_chk if the key is out of the range of `n`-bit keys). -/
@[vm_spec] theorem dictDelInt (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int) (unsigned : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictExt (.del true unsigned))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s })
      | some key => ExceptT.run (Dict.delRun (some root) key) { st with stack := s } := by
  rw [DictTail.delHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictDel, hs, hk, hn1, hn', VM.popMaybeCell]
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← DictTail.delTail_run _ _ _ hwf']
    vm_simp [DictTail.dictDel, hs, hk, hn1, hn', VM.popMaybeCell]

/-- C++ `exec_dict_delete` (dictops.cpp:375) with an integer key on the empty dictionary (`null`):
`Dict.delRun none` (nothing found, nothing loaded). -/
@[vm_spec] theorem dictDelIntEmpty (st : VmState) (s : Stack) (idx : Int) (n : Int) (unsigned : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push .null).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictExt (.del true unsigned))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s })
      | some key => ExceptT.run (Dict.delRun none key) { st with stack := s } := by
  rw [DictTail.delHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictDel, hs, hk, hn1, hn', VM.popMaybeCell]
  | some key =>
    dsimp only
    rw [← DictTail.delTail_run _ _ _ (Dict.WF.empty _)]
    vm_simp [DictTail.dictDel, hs, hk, hn1, hn', VM.popMaybeCell]

/-- C++ `exec_dict_delete` (dictops.cpp:375) with a slice key (`DICTDEL`), on a well-formed
dictionary: `Dict.delRun` of the first `n` bits of the key (cell_und if it is shorter). -/
@[vm_spec] theorem dictDelSlice (st : VmState) (s : Stack) (k : Slice) (root : Cell) (n : Int) (unsigned : Bool)
    (hs : st.stack = ((s.push (.slice k)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictExt (.del false unsigned))) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.delRun (some root) (k.readBits n.toNat)) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.delHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← DictTail.delTail_run _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictDel, hs, hk, hn1, hn', VM.popMaybeCell]
  · rw [if_neg hk]
    vm_simp [DictTail.dictDel, hs, hk, hn1, hn', VM.popMaybeCell]

/-- C++ `exec_dict_delete` (dictops.cpp:375) with a slice key on the empty dictionary (`null`):
`Dict.delRun none`. -/
@[vm_spec] theorem dictDelSliceEmpty (st : VmState) (s : Stack) (k : Slice) (n : Int) (unsigned : Bool)
    (hs : st.stack = ((s.push (.slice k)).push .null).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictExt (.del false unsigned))) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.delRun none (k.readBits n.toNat)) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.delHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    rw [← DictTail.delTail_run _ _ _ (Dict.WF.empty _)]
    vm_simp [DictTail.dictDel, hs, hk, hn1, hn', VM.popMaybeCell]
  · rw [if_neg hk]
    vm_simp [DictTail.dictDel, hs, hk, hn1, hn', VM.popMaybeCell]

end Spec


/-! ## Well-formedness, discharged -/

/-- The size of a dictionary key: a literal, or the key of an integer (`dictKeyBits?_size`) or of a
slice (`Slice.readBits_size_of_haveBits`) found in the context. -/
syntax "vm_dict_key" : tactic

macro_rules
  | `(tactic| vm_dict_key) => `(tactic| first
      | rfl
      | (simp only [Int.reduceToNat, List.size_toArray, List.length_cons, List.length_nil]; done)
      | exact dictKeyBits?_size (by assumption)
      | exact Slice.readBits_size_of_haveBits (by assumption))

/-- More ways to prove `Dict.WF root n` for `vm_dict_wf` (`macro_rules` add them; none here). -/
syntax "vm_dict_wf_ext" : tactic

macro_rules | `(tactic| vm_dict_wf_ext) => `(tactic| fail "vm_dict_wf_ext: no rule")

/-- `vm_dict_wf`: a goal `Dict.WF root n` from the context: a hypothesis (the key length a literal
or not), the empty dictionary, or the result of a set or a delete (a hypothesis
`Dict.setSetRes root key vb = .ok (c, ..)`, `Dict.setRes ..`, `Dict.delRes ..`, which `vm_run`
leaves when it splits on it) of a dictionary that is well-formed in turn (`Dict.WF.setSet`,
`Dict.WF.setRes`, `Dict.WF.delRes`, and the rules of `vm_dict_wf_ext`). Fails at once on any other
goal. -/
syntax "vm_dict_wf" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| vm_dict_wf) => withMainContext do
    let t ← whnfR (← instantiateMVars (← getMainTarget))
    unless t.isAppOfArity ``Dict.WF 2 do throwError "vm_dict_wf: the goal is not `Dict.WF`"
    evalTactic (← `(tactic| first
      | with_reducible assumption
      | exact Dict.WF.empty _
      | (simp only [Int.reduceToNat]; with_reducible assumption)
      | (refine Dict.WF.setSet ?_ ?_ (by assumption) <;> first | vm_dict_wf | vm_dict_key)
      | (refine Dict.WF.setRes ?_ ?_ (by assumption) <;> first | vm_dict_wf | vm_dict_key)
      | (refine Dict.WF.delRes ?_ ?_ (by assumption) <;> first | vm_dict_wf | vm_dict_key)
      | vm_dict_wf_ext))

/-- The discharger of `vm_simp` and `vm_run` (`vm_disch`) also proves `Dict.WF` (`vm_dict_wf`), the
condition of the specifications on well-formed dictionaries. -/
macro_rules | `(tactic| vm_disch) => `(tactic| vm_dict_wf)

end TvmLean

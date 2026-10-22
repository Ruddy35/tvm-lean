import TvmLean.Proofs.Exec.Dict.SetGet
import TvmLean.Proofs.Exec.Spec.DictDel

/-!
# Specifications: lookup-and-set on symbolic dictionaries

`DICT{,I,U}SETGET{,REF}`, `...REPLACEGET{,REF}`, `...ADDGET{,REF}` (`.dictExt (.mutGet ..)`) and
`DICT{,I,U}{SET,REPLACE,ADD}GETB` (`.dictExt (.mutGetB ..)`) on a well-formed dictionary or on
`null`, stated through the map of the dictionary, as `Proofs/Exec/Spec/DictSet.lean` states the
sets:

* `Spec.dictSetGet{Int,Slice}{,Ref,B}{,Empty}`: `Dict.setGetRun`: the root and the cells on the
  key's path loaded (`VM.loadOrd`), the cells created charged, the new root pushed, then the old
  value (`Dict.pushOld`: the slice, or with `REF` the reference it must consist of) and the flag,
  or the flag alone;
* the result `Dict.setGetRes` is known through `Dict.value_setGetRes` (the old value is the
  value the key had; the map after it as after the set) and `Dict.WF.setGetRes`.

The handlers are written again with their tails named (`DictTail.mutGet`, `DictTail.mutGetB`,
the same code: `DictTail.mutGetHandler_eq`, `DictTail.mutGetBHandler_eq`), the tails stated once
(`DictTail.setGetWith_run`).
-/

namespace DictTail

open TvmLean

/-- `extractRefOrThrow` of `TvmLean/Semantics/Exec/Dict/Ext.lean` (private there). -/
def extractRefOrThrow (valueSlice : Slice) : VM Cell := do
  if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
    return valueSlice.cell.refs[valueSlice.refPos]!
  else
    throw .dictErr

/-- The tail of the lookup-and-set instructions for a function `setF` of the resolver, pushing an
old value with `pushOld`. -/
def setGetWith (dictCell? : Option Cell) (keyBits : BitString)
    (setF : (Cell → Except Excno Cell) → Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell))
    (pushOld : Slice → VM Unit) (ok_f : Bool) : VM Unit := do
  prechargeRootLoad dictCell?
  match setF (← VM.cellResolver) with
  | .error e =>
      let loaded := loadedWithoutRoot dictCell? (dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictCell? keyBits)
      registerLoaded loaded
      throw e
  | .ok (oldVal?, newRoot?, _ok, created, loaded) =>
      let loaded := loadedWithoutRoot dictCell? loaded
      registerLoaded loaded
      VM.chargeDictSetCreates newRoot? created (dictKeyPath · keyBits)
      pushDictRoot newRoot?
      match oldVal? with
      | some oldVal => pushOld oldVal
      | none => pushBool (!ok_f)

/-- The handler of `.dictExt (.mutGet ..)` (`TvmLean/Semantics/Exec/Dict/Ext.lean`) in a mode that
sets (`.set`, `.replace`, `.add`, as `setMode`), with the tails named. -/
def mutGetSet (intKey unsigned byRef : Bool) (setMode : DictSetMode) : VM Unit := do
  VM.checkUnderflow 4
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let keyBits? : Option BitString ←
    if intKey then
      let idxVal ← VM.popInt
      match idxVal with
      | .nan => throw .rangeChk
      | .num idx =>
          match dictKeyBits? idx n unsigned with
          | some bs => pure (some bs)
          | none => throw .rangeChk
    else
      let keySlice ← VM.popSlice
      if keySlice.haveBits n then
        pure (some (keySlice.readBits n))
      else
        pure none
  let ok_f : Bool := setMode != .add
  if byRef then
    let newValueRef ← VM.popCell
    let keyBits ←
      match keyBits? with
      | some bs => pure bs
      | none => throw .cellUnd
    setGetWith dictCell? keyBits
      (fun r => dictLookupSetRefWithCells (resolve := r) dictCell? keyBits newValueRef setMode)
      (fun oldVal => do
        let c ← extractRefOrThrow oldVal
        VM.push (.cell c)
        pushBool ok_f) ok_f
  else
    let newValue ← VM.popSlice
    let keyBits ←
      match keyBits? with
      | some bs => pure bs
      | none => throw .cellUnd
    setGetWith dictCell? keyBits
      (fun r => dictLookupSetSliceWithCells (resolve := r) dictCell? keyBits newValue setMode)
      (fun oldVal => do
        VM.push (.slice oldVal)
        pushBool ok_f) ok_f

/-- The handler of `.dictExt (.mutGetB ..)`, with its tail named. -/
def mutGetB (intKey unsigned : Bool) (mode : DictSetMode) : VM Unit := do
  VM.checkUnderflow 4
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let keyBits? : Option BitString ←
    if intKey then
      let idxVal ← VM.popInt
      match idxVal with
      | .nan => throw .rangeChk
      | .num idx =>
          match dictKeyBits? idx n unsigned with
          | some bs => pure (some bs)
          | none => throw .rangeChk
    else
      let keySlice ← VM.popSlice
      if keySlice.haveBits n then
        pure (some (keySlice.readBits n))
      else
        pure none
  let newValue ← VM.popBuilder
  let keyBits ←
    match keyBits? with
    | some bs => pure bs
    | none => throw .cellUnd
  let ok_f : Bool := mode != .add
  setGetWith dictCell? keyBits
    (fun r => dictLookupSetBuilderWithCells (resolve := r) dictCell? keyBits newValue mode)
    (fun oldVal => do
      VM.push (.slice oldVal)
      pushBool ok_f) ok_f

end DictTail

namespace TvmLean

/-! ## The lookup-and-set as the specifications state it -/

/-- The mode of the set of a lookup-and-set instruction (`.del` does not set). -/
def Dict.setModeOf : DictMutMode → DictSetMode
  | .set => .set
  | .replace => .replace
  | .add => .add
  | .del => .set

@[vm_run] theorem Dict.setModeOf_set : Dict.setModeOf .set = .set := rfl
@[vm_run] theorem Dict.setModeOf_replace : Dict.setModeOf .replace = .replace := rfl
@[vm_run] theorem Dict.setModeOf_add : Dict.setModeOf .add = .add := rfl

/-- **The result of a lookup-and-set** (C++ `dict.lookup_set`) of `key` to the value `vb` in mode
`mode`: the old value, the new root, whether it changed, the number of cells created and the cells
loaded after the root. As the model computes it (default resolver); never unfolded by `vm_run`:
known through `Dict.value_setGetRes` and `Dict.WF.setGetRes`. -/
@[irreducible] def Dict.setGetRes (root : Option Cell) (key : BitString) (vb : Builder) (mode : DictSetMode) :
    Except Excno (Option Slice × Option Cell × Bool × Nat × List Cell) :=
  match dictLookupSetGenAuxWithCells root key (DictMap.storeB vb) mode with
  | .ok (old, r, ok, c, loaded) => .ok (old, r, ok, c, Dict.withoutRoot root loaded)
  | .error e => .error e

/-- The cells a lookup of `key` visits after the root (charged when a lookup-and-set fails). -/
@[irreducible] def Dict.visitedWithoutRoot (root : Option Cell) (key : BitString) : List Cell :=
  Dict.withoutRoot root (dictLookupVisitedCells root key)

/-- The old value pushed by a lookup-and-set: the slice, or with `byRef` the reference it must
consist of (dict_err else); then the flag `okf`. -/
def Dict.pushOld (old : Slice) (byRef okf : Bool) : VM Unit :=
  if byRef then
    if old.bitsRemaining == 0 && old.refsRemaining == 1 then do
      VM.push (.cell (old.cell.refs[old.refPos]!))
      VM.pushSmallInt (if okf then -1 else 0)
    else
      throw .dictErr
  else do
    VM.push (.slice old)
    VM.pushSmallInt (if okf then -1 else 0)

/-- **A lookup-and-set on a well-formed dictionary**, as the instructions run it: the root and the
cells on the key's path loaded (`VM.loadOrd`), the cells created charged, the new root pushed, then
the old value and the flag `mode != .add` (`Dict.pushOld`), or the opposite flag alone. -/
def Dict.setGetRun (root : Option Cell) (key : BitString) (vb : Builder) (mode : DictSetMode) (byRef : Bool) :
    VM Unit :=
  match Dict.setGetRes root key vb mode with
  | .error e => do VM.loadOrd (Dict.loadsOf root (Dict.visitedWithoutRoot root key)); throw e
  | .ok (old?, newRoot?, _, created, rest) => do
      VM.loadOrd (Dict.loadsOf root rest)
      VM.chargeDictSetCreates newRoot? created (dictKeyPath · key)
      match newRoot? with
      | none => VM.push .null
      | some c => VM.push (.cell c)
      match old? with
      | some old => Dict.pushOld old byRef (mode != .add)
      | none => VM.pushSmallInt (if !(mode != .add) then -1 else 0)

/-- **Get after a lookup-and-set, on the map**: the old value is the value the key had; after it,
the key maps to the value stored if the dictionary changed (`ok`), every other key as before. -/
theorem Dict.value_setGetRes {root root' : Option Cell} {key : BitString} {vb : Builder} {mode : DictSetMode}
    {old : Option Slice} {ok : Bool} {created : Nat} {rest : List Cell} (hwf : Dict.WF root key.size)
    (h : Dict.setGetRes root key vb mode = .ok (old, root', ok, created, rest)) :
    old.map Slice.toCellRemaining = Dict.value root key ∧
      ∀ key' : BitString, key'.size = key.size →
        Dict.value root' key' = if ok = true ∧ key' = key then some vb.finalize else Dict.value root key' := by
  unfold Dict.setGetRes at h
  split at h
  · rename_i old' r ok' cr loaded hres
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, -, -⟩ := h
    have hold := DictMap.val_lookupSet_old Cell.rejectSpecial _ mode _ root key rfl _ hres
    rw [DictMap.val_eq_value hwf rfl] at hold
    refine ⟨(Except.ok.inj hold).symm, fun key' hk' => ?_⟩
    have hset := DictMap.lookupSet_set hres
    cases ok' with
    | true =>
      rw [Dict.value_set hwf hset key' hk']
      by_cases hkk : key' = key
      · simp [hkk]
      · simp [hkk]
    | false =>
      rw [DictMap.set_unchanged hset]
      simp
  · cases h

/-- A lookup-and-set keeps a dictionary well-formed. -/
theorem Dict.WF.setGetRes {root root' : Option Cell} {key : BitString} {vb : Builder} {mode : DictSetMode}
    {old : Option Slice} {ok : Bool} {created : Nat} {rest : List Cell} {n : Nat} (hwf : Dict.WF root n)
    (hk : key.size = n) (h : Dict.setGetRes root key vb mode = .ok (old, root', ok, created, rest)) :
    Dict.WF root' n := by
  subst hk
  unfold Dict.setGetRes at h
  split at h
  · rename_i old' r ok' cr loaded hres
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -, -, -⟩ := h
    exact Dict.WF.set hwf (DictMap.lookupSet_set hres)
  · cases h

/-- In mode `.set` a lookup-and-set always changes the dictionary. -/
theorem Dict.setGetRes_set_ok {root root' : Option Cell} {key : BitString} {vb : Builder}
    {old : Option Slice} {ok : Bool} {created : Nat} {rest : List Cell}
    (h : Dict.setGetRes root key vb .set = .ok (old, root', ok, created, rest)) : ok = true := by
  unfold Dict.setGetRes at h
  split at h
  · rename_i old' r ok' cr loaded hres
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, -, -⟩ := h
    exact DictMap.set_set_changed _ root key rfl _ (DictMap.lookupSet_set hres)
  · cases h

/-! ## The tails -/

/-- **The tail of a lookup-and-set on a well-formed dictionary is `Dict.setGetRun`.** -/
theorem DictTail.setGetWith_run (st : VmState) (root : Option Cell) (key : BitString) (vb : Builder)
    (mode : DictSetMode) (byRef : Bool)
    (setF : (Cell → Except Excno Cell) → Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell))
    (pushOld : Slice → VM Unit) (hwf : Dict.WF root key.size)
    (hset : ∀ libs gv refused, setF (fun c => (libraryResolveLoads libs gv c refused).2) =
      dictLookupSetGenAuxWithCells root key (DictMap.storeB vb) mode)
    (hpush : ∀ old, pushOld old = Dict.pushOld old byRef (mode != .add)) :
    ExceptT.run (DictTail.setGetWith root key setF pushOld (mode != .add)) st =
      ExceptT.run (Dict.setGetRun root key vb mode byRef) st := by
  have hvis : ∀ libs gv refused,
      dictLookupVisitedCells root key (fun c => (libraryResolveLoads libs gv c refused).2) =
        dictLookupVisitedCells root key :=
    fun libs gv refused => DictMap.visited_resolve _ (resolvesOrdinary_library libs gv refused) hwf
  have hpo : pushOld = fun old => Dict.pushOld old byRef (mode != .add) := funext hpush
  subst hpo
  unfold DictTail.setGetWith Dict.setGetRun
  cases root with
  | none =>
    cases hres : dictLookupSetGenAuxWithCells none key (DictMap.storeB vb) mode with
    | error e =>
      have h2 : Dict.setGetRes none key vb mode = .error e := by unfold Dict.setGetRes; rw [hres]
      have hV : Dict.visitedWithoutRoot none key = [] := by unfold Dict.visitedWithoutRoot; rfl
      rw [h2, hV]
      simp only [DictTail.prechargeRootLoad, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure,
        VM.bindRes_ok, hset, hres, Dict.loadsOf_none]
      rfl
    | ok res =>
      rcases res with ⟨old, r, ok, cr, loaded⟩
      have hl : loaded = #[] := set_none_loaded (DictMap.lookupSet_set hres)
      subst hl
      have h2 : Dict.setGetRes none key vb mode = .ok (old, r, ok, cr, []) := by
        unfold Dict.setGetRes; rw [hres]; rfl
      rw [h2]
      simp only [DictTail.prechargeRootLoad, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure,
        VM.bindRes_ok, hset, hres, Dict.loadsOf_none, DictTail.registerLoaded, DictTail.loadedWithoutRoot,
        VM.forIn_registerCellLoad, DictTail.pushDictRoot, DictTail.pushBool]
      cases r <;> cases old <;> rfl
  | some c =>
    have hc := DictMap.WF_root_ordinary hwf
    cases hres : dictLookupSetGenAuxWithCells (some c) key (DictMap.storeB vb) mode with
    | error e =>
      obtain ⟨restV, hV, hordV⟩ := DictMap.visited_loaded hwf
      have hall : ∀ x ∈ (dictLookupVisitedCells (some c) key).toList, x.special = false := by
        rw [hV]
        intro x hx
        simp only [Array.toList_append, List.mem_append] at hx
        rcases hx with hx | hx
        · simp at hx; subst hx; exact hc
        · exact hordV x hx
      have hordV' := DictTail.filter_ord c hall
      have h2 : Dict.setGetRes (some c) key vb mode = .error e := by unfold Dict.setGetRes; rw [hres]
      have hVr : Dict.visitedWithoutRoot (some c) key =
          ((dictLookupVisitedCells (some c) key).filter (fun x => x != c)).toList := by
        unfold Dict.visitedWithoutRoot; rfl
      rw [h2, hVr]
      simp only [DictTail.prechargeRootLoad, VM.run_bind, VM.run_registerCellLoad_ordinary c st hc,
        Dict.loadsOf_some, VM.run_loadOrd_cons]
      split
      · rfl
      · simp only [VM.bindRes_ok, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, hset, hres, hvis,
          DictTail.registerLoaded, DictTail.loadedWithoutRoot, VM.forIn_registerCellLoad,
          VM.run_registerCellLoadList_ord _ hordV', VM.bindRes_bindRes_pure]
    | ok res =>
      rcases res with ⟨old, r, ok, cr, loaded⟩
      obtain ⟨rest, hl, hord⟩ := DictMap.set_loaded _ c key rfl hwf _ (DictMap.lookupSet_set hres)
      simp only at hl
      subst hl
      have hord' := DictTail.filter_ord (cells := #[c] ++ rest) c (fun x hx => by
        simp only [Array.toList_append, List.mem_append] at hx
        rcases hx with hx | hx
        · simp at hx; subst hx; exact hc
        · exact hord x hx)
      have h2 : Dict.setGetRes (some c) key vb mode =
          .ok (old, r, ok, cr, (((#[c] ++ rest).filter (fun x => x != c)).toList)) := by
        unfold Dict.setGetRes; rw [hres]; rfl
      rw [h2]
      simp only [DictTail.prechargeRootLoad, VM.run_bind, VM.run_registerCellLoad_ordinary c st hc,
        Dict.loadsOf_some, VM.run_loadOrd_cons]
      split
      · rfl
      · simp only [VM.bindRes_ok, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, hset, hres,
          DictTail.registerLoaded, DictTail.loadedWithoutRoot, VM.forIn_registerCellLoad,
          VM.run_registerCellLoadList_ord _ hord', VM.bindRes_bindRes_pure, DictTail.pushDictRoot,
          DictTail.pushBool]
        cases r <;> cases old <;> rfl


theorem DictTail.setGetSlice_run (st : VmState) (root : Option Cell) (key : BitString) (val : Slice)
    (mode : DictSetMode) (hwf : Dict.WF root key.size) :
    ExceptT.run (DictTail.setGetWith root key
        (fun r => dictLookupSetSliceWithCells (resolve := r) root key val mode)
        (fun oldVal => do
          VM.push (.slice oldVal)
          DictTail.pushBool (mode != .add)) (mode != .add)) st =
      ExceptT.run (Dict.setGetRun root key (DictMap.sliceB val) mode false) st := by
  refine DictTail.setGetWith_run st root key _ mode false _ _ hwf (fun libs gv refused => ?_) (fun old => rfl)
  rw [DictMap.dictLookupSetSliceWithCells_eq,
    DictMap.lookupSet_resolve _ (resolvesOrdinary_library libs gv refused) _ _ _ root key rfl hwf]

theorem DictTail.setGetRef_run (st : VmState) (root : Option Cell) (key : BitString) (c : Cell)
    (mode : DictSetMode) (hwf : Dict.WF root key.size) :
    ExceptT.run (DictTail.setGetWith root key
        (fun r => dictLookupSetRefWithCells (resolve := r) root key c mode)
        (fun oldVal => do
          let c ← DictTail.extractRefOrThrow oldVal
          VM.push (.cell c)
          DictTail.pushBool (mode != .add)) (mode != .add)) st =
      ExceptT.run (Dict.setGetRun root key (DictMap.refB c) mode true) st := by
  refine DictTail.setGetWith_run st root key _ mode true _ _ hwf (fun libs gv refused => ?_) (fun old => ?_)
  · rw [DictMap.dictLookupSetRefWithCells_eq,
      DictMap.lookupSet_resolve _ (resolvesOrdinary_library libs gv refused) _ _ _ root key rfl hwf]
  · unfold Dict.pushOld DictTail.extractRefOrThrow
    simp only [if_true]
    split <;> rfl

theorem DictTail.setGetBuilder_run (st : VmState) (root : Option Cell) (key : BitString) (vb : Builder)
    (mode : DictSetMode) (hwf : Dict.WF root key.size) :
    ExceptT.run (DictTail.setGetWith root key
        (fun r => dictLookupSetBuilderWithCells (resolve := r) root key vb mode)
        (fun oldVal => do
          VM.push (.slice oldVal)
          DictTail.pushBool (mode != .add)) (mode != .add)) st =
      ExceptT.run (Dict.setGetRun root key vb mode false) st := by
  refine DictTail.setGetWith_run st root key _ mode false _ _ hwf (fun libs gv refused => ?_) (fun old => rfl)
  rw [DictMap.dictLookupSetBuilderWithCells_eq,
    DictMap.lookupSet_resolve _ (resolvesOrdinary_library libs gv refused) _ _ _ root key rfl hwf]

/-- `.dictExt (.mutGet ..)` in a mode that sets runs as `DictTail.mutGetSet` (the same code, once
the mode is known). -/
theorem DictTail.mutGetHandler_eq (intKey unsigned byRef : Bool) (mode : DictMutMode) (hmode : mode ≠ .del)
    (st : VmState) :
    ExceptT.run (execInstr (.dictExt (.mutGet intKey unsigned byRef mode))) st =
      ExceptT.run (DictTail.mutGetSet intKey unsigned byRef (Dict.setModeOf mode)) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  cases mode
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hmode

/-- `.dictExt (.mutGetB ..)` runs as `DictTail.mutGetB` (the same code). -/
theorem DictTail.mutGetBHandler_eq (intKey unsigned : Bool) (mode : DictSetMode) (st : VmState) :
    ExceptT.run (execInstr (.dictExt (.mutGetB intKey unsigned mode))) st =
      ExceptT.run (DictTail.mutGetB intKey unsigned mode) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl


/-! ## The specifications -/

namespace Spec

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with an integer key and a slice value (`DICT{I,U}{SET,REPLACE,ADD}GET`), on a well-formed dictionary: `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetInt (st : VmState) (s : Stack) (val : Slice) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictMutMode)
    (hs : st.stack = ((((s.push (.slice val)).push (.int (.num idx))).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (hmode : mode ≠ .del) :
    ExceptT.run (execInstr (.dictExt (.mutGet true unsigned false mode))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.slice val) })
      | some key => ExceptT.run (Dict.setGetRun (some root) key (DictMap.sliceB val) (Dict.setModeOf mode) false) { st with stack := s } := by
  rw [DictTail.mutGetHandler_eq _ _ _ _ hmode]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  generalize Dict.setModeOf mode = setMode
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← DictTail.setGetSlice_run _ _ _ _ _ hwf']
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with an integer key and a slice value (`DICT{I,U}{SET,REPLACE,ADD}GET`), on the empty dictionary (`null`): `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetIntEmpty (st : VmState) (s : Stack) (val : Slice) (idx : Int) (n : Int)
    (unsigned : Bool) (mode : DictMutMode)
    (hs : st.stack = ((((s.push (.slice val)).push (.int (.num idx))).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hmode : mode ≠ .del) :
    ExceptT.run (execInstr (.dictExt (.mutGet true unsigned false mode))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.slice val) })
      | some key => ExceptT.run (Dict.setGetRun none key (DictMap.sliceB val) (Dict.setModeOf mode) false) { st with stack := s } := by
  rw [DictTail.mutGetHandler_eq _ _ _ _ hmode]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  generalize Dict.setModeOf mode = setMode
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    dsimp only
    rw [← DictTail.setGetSlice_run _ _ _ _ _ hwf']
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with an integer key and a reference value (`DICT{I,U}{SET,REPLACE,ADD}GETREF`), on a well-formed dictionary: `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetIntRef (st : VmState) (s : Stack) (val : Cell) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictMutMode)
    (hs : st.stack = ((((s.push (.cell val)).push (.int (.num idx))).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (hmode : mode ≠ .del) :
    ExceptT.run (execInstr (.dictExt (.mutGet true unsigned true mode))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.cell val) })
      | some key => ExceptT.run (Dict.setGetRun (some root) key (DictMap.refB val) (Dict.setModeOf mode) true) { st with stack := s } := by
  rw [DictTail.mutGetHandler_eq _ _ _ _ hmode]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  generalize Dict.setModeOf mode = setMode
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← DictTail.setGetRef_run _ _ _ _ _ hwf']
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with an integer key and a reference value (`DICT{I,U}{SET,REPLACE,ADD}GETREF`), on the empty dictionary (`null`): `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetIntRefEmpty (st : VmState) (s : Stack) (val : Cell) (idx : Int) (n : Int)
    (unsigned : Bool) (mode : DictMutMode)
    (hs : st.stack = ((((s.push (.cell val)).push (.int (.num idx))).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hmode : mode ≠ .del) :
    ExceptT.run (execInstr (.dictExt (.mutGet true unsigned true mode))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.cell val) })
      | some key => ExceptT.run (Dict.setGetRun none key (DictMap.refB val) (Dict.setModeOf mode) true) { st with stack := s } := by
  rw [DictTail.mutGetHandler_eq _ _ _ _ hmode]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  generalize Dict.setModeOf mode = setMode
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    dsimp only
    rw [← DictTail.setGetRef_run _ _ _ _ _ hwf']
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with a slice key and a slice value (`DICT{SET,REPLACE,ADD}GET`), on a well-formed dictionary: `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetSlice (st : VmState) (s : Stack) (val : Slice) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictMutMode)
    (hs : st.stack = ((((s.push (.slice val)).push (.slice k)).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (hmode : mode ≠ .del) :
    ExceptT.run (execInstr (.dictExt (.mutGet false unsigned false mode))) st =
      if k.haveBits n.toNat then
        ExceptT.run (Dict.setGetRun (some root) (k.readBits n.toNat) (DictMap.sliceB val) (Dict.setModeOf mode) false) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.mutGetHandler_eq _ _ _ _ hmode]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  generalize Dict.setModeOf mode = setMode
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← DictTail.setGetSlice_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with a slice key and a slice value (`DICT{SET,REPLACE,ADD}GET`), on the empty dictionary (`null`): `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetSliceEmpty (st : VmState) (s : Stack) (val : Slice) (k : Slice) (n : Int)
    (unsigned : Bool) (mode : DictMutMode)
    (hs : st.stack = ((((s.push (.slice val)).push (.slice k)).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hmode : mode ≠ .del) :
    ExceptT.run (execInstr (.dictExt (.mutGet false unsigned false mode))) st =
      if k.haveBits n.toNat then
        ExceptT.run (Dict.setGetRun none (k.readBits n.toNat) (DictMap.sliceB val) (Dict.setModeOf mode) false) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.mutGetHandler_eq _ _ _ _ hmode]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  generalize Dict.setModeOf mode = setMode
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    rw [← DictTail.setGetSlice_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with a slice key and a reference value (`DICT{SET,REPLACE,ADD}GETREF`), on a well-formed dictionary: `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetSliceRef (st : VmState) (s : Stack) (val : Cell) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictMutMode)
    (hs : st.stack = ((((s.push (.cell val)).push (.slice k)).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (hmode : mode ≠ .del) :
    ExceptT.run (execInstr (.dictExt (.mutGet false unsigned true mode))) st =
      if k.haveBits n.toNat then
        ExceptT.run (Dict.setGetRun (some root) (k.readBits n.toNat) (DictMap.refB val) (Dict.setModeOf mode) true) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.mutGetHandler_eq _ _ _ _ hmode]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  generalize Dict.setModeOf mode = setMode
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← DictTail.setGetRef_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with a slice key and a reference value (`DICT{SET,REPLACE,ADD}GETREF`), on the empty dictionary (`null`): `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetSliceRefEmpty (st : VmState) (s : Stack) (val : Cell) (k : Slice) (n : Int)
    (unsigned : Bool) (mode : DictMutMode)
    (hs : st.stack = ((((s.push (.cell val)).push (.slice k)).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hmode : mode ≠ .del) :
    ExceptT.run (execInstr (.dictExt (.mutGet false unsigned true mode))) st =
      if k.haveBits n.toNat then
        ExceptT.run (Dict.setGetRun none (k.readBits n.toNat) (DictMap.refB val) (Dict.setModeOf mode) true) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.mutGetHandler_eq _ _ _ _ hmode]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  generalize Dict.setModeOf mode = setMode
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    rw [← DictTail.setGetRef_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.mutGetSet, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with an integer key and a builder value (`DICT{I,U}{SET,REPLACE,ADD}GETB`), on a well-formed dictionary: `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetIntB (st : VmState) (s : Stack) (val : Builder) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictSetMode)
    (hs : st.stack = ((((s.push (.builder val)).push (.int (.num idx))).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictExt (.mutGetB true unsigned mode))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.builder val) })
      | some key => ExceptT.run (Dict.setGetRun (some root) key val mode false) { st with stack := s } := by
  rw [DictTail.mutGetBHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.mutGetB, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← DictTail.setGetBuilder_run _ _ _ _ _ hwf']
    vm_simp [DictTail.mutGetB, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with an integer key and a builder value (`DICT{I,U}{SET,REPLACE,ADD}GETB`), on the empty dictionary (`null`): `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetIntBEmpty (st : VmState) (s : Stack) (val : Builder) (idx : Int) (n : Int)
    (unsigned : Bool) (mode : DictSetMode)
    (hs : st.stack = ((((s.push (.builder val)).push (.int (.num idx))).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictExt (.mutGetB true unsigned mode))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.builder val) })
      | some key => ExceptT.run (Dict.setGetRun none key val mode false) { st with stack := s } := by
  rw [DictTail.mutGetBHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.mutGetB, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    dsimp only
    rw [← DictTail.setGetBuilder_run _ _ _ _ _ hwf']
    vm_simp [DictTail.mutGetB, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with a slice key and a builder value (`DICT{SET,REPLACE,ADD}GETB`), on a well-formed dictionary: `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetSliceB (st : VmState) (s : Stack) (val : Builder) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictSetMode)
    (hs : st.stack = ((((s.push (.builder val)).push (.slice k)).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictExt (.mutGetB false unsigned mode))) st =
      if k.haveBits n.toNat then
        ExceptT.run (Dict.setGetRun (some root) (k.readBits n.toNat) val mode false) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.mutGetBHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← DictTail.setGetBuilder_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.mutGetB, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.mutGetB, hs, hk, hn1, hn']

/-- A lookup-and-set (C++ `exec_dict_setget`, dictops.cpp:316) with a slice key and a builder value (`DICT{SET,REPLACE,ADD}GETB`), on the empty dictionary (`null`): `Dict.setGetRun`. -/
@[vm_spec] theorem dictSetGetSliceBEmpty (st : VmState) (s : Stack) (val : Builder) (k : Slice) (n : Int)
    (unsigned : Bool) (mode : DictSetMode)
    (hs : st.stack = ((((s.push (.builder val)).push (.slice k)).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictExt (.mutGetB false unsigned mode))) st =
      if k.haveBits n.toNat then
        ExceptT.run (Dict.setGetRun none (k.readBits n.toNat) val mode false) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.mutGetBHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    rw [← DictTail.setGetBuilder_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.mutGetB, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.mutGetB, hs, hk, hn1, hn']

end Spec


/-- `vm_dict_wf` also follows a lookup-and-set (`Dict.WF.setGetRes`). -/
macro_rules
  | `(tactic| vm_dict_wf_ext) =>
    `(tactic| (refine Dict.WF.setGetRes ?_ ?_ (by assumption) <;> first | vm_dict_wf | vm_dict_key))

end TvmLean

import TvmLean.Proofs.Exec.Dict.Loaded

/-!
# Specifications: dictionary sets on symbolic dictionaries

`DICT{,I,U}SET{,REF}`, `...ADD`, `...REPLACE` and `DICT{,I,U}SETB` (and their `ADD`/`REPLACE`
forms) on a well-formed dictionary (`Dict.WF`) or on `null`, in the format of
`Proofs/Exec/Spec/Stack.lean`. The value stored is a builder (`DictMap.sliceB`, `DictMap.refB`, or
the builder itself), the update is seen through the map of the dictionary:

* mode `.set`: `Spec.dictSet{Int,IntRef,Slice,SliceRef,IntB,SliceB}{,Empty}_set`, running
  `Dict.setRunSet`: the root and the cells on the key's path loaded (`VM.loadOrd`), the cells
  created charged, the new root pushed; its result `Dict.setSetRes` known through
  `Dict.value_setSet` (the key maps to the value stored, every other key as before) and
  `Dict.WF.setSet`;
* modes `.add` and `.replace`: the same names with `_flag`, running `Dict.setRun` (the flag of the
  change pushed after the root), known through `Dict.value_setRes`, `Dict.setRes_unchanged` and
  `Dict.WF.setRes`.

An integer key out of the range of `n`-bit keys raises range_chk, a slice key shorter than `n` bits
cell_und.
-/

/-! ## The handlers, with their tails named

The handlers of `DICTSET` and `DICTSETB` (`TvmLean/Semantics/Exec/Dict/DictSet.lean`,
`DictSetB.lean`), written again with the part after the pops as a definition of its own
(`DictTail.setSlice` and the like): the same code, so the same programs (`handler_eq`, by `rfl`).
They are outside the namespace `TvmLean`, so that `vm_simp` runs the pops and keeps the tail
whole, which `DictTail.setWith_run` then states. -/

namespace DictTail

open TvmLean

/-- `dropFirstRootLoad` of `TvmLean/Semantics/Exec/Dict/DictSet.lean` (private there). -/
def dropFirstRootLoad (dictCell? : Option Cell) (loaded : Array Cell) : Array Cell :=
  match dictCell? with
  | none => loaded
  | some root =>
      Id.run do
        let mut skipped : Bool := false
        let mut out : Array Cell := #[]
        for c in loaded do
          if (!skipped) && c == root then
            skipped := true
          else
            out := out.push c
        out

/-- The tail of the set instructions for a set function `setF` of the resolver (the three value
forms differ only in it). -/
def setWith (dictCell? : Option Cell) (keyBits : BitString)
    (setF : (Cell → Except Excno Cell) → Except Excno (Option Cell × Bool × Nat × Array Cell))
    (mode : DictSetMode) : VM Unit := do
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()
  match setF (← VM.cellResolver) with
  | .error e =>
      let loaded := dropFirstRootLoad dictCell? (dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictCell? keyBits)
      for c in loaded do
        VM.registerCellLoad c
      throw e
  | .ok (newRoot?, ok, created, loaded) =>
      let loaded := dropFirstRootLoad dictCell? loaded
      for c in loaded do
        VM.registerCellLoad c
      VM.chargeDictSetCreates newRoot? created (dictKeyPath · keyBits)
      match newRoot? with
      | none => VM.push .null
      | some c => VM.push (.cell c)
      if mode == .set then
        if !ok then
          throw .fatal
      else
        VM.pushSmallInt (if ok then -1 else 0)

/-- The tail of `DICTSET{REF}` with a reference value. -/
def setRef (dictCell? : Option Cell) (keyBits : BitString) (valRef : Cell) (mode : DictSetMode) : VM Unit := do
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()
  match dictSetRefWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits valRef mode with
  | .error e =>
      let loaded := dropFirstRootLoad dictCell? (dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictCell? keyBits)
      for c in loaded do
        VM.registerCellLoad c
      throw e
  | .ok (newRoot?, ok, created, loaded) =>
      let loaded := dropFirstRootLoad dictCell? loaded
      for c in loaded do
        VM.registerCellLoad c
      VM.chargeDictSetCreates newRoot? created (dictKeyPath · keyBits)
      match newRoot? with
      | none => VM.push .null
      | some c => VM.push (.cell c)
      if mode == .set then
        if !ok then
          throw .fatal
      else
        VM.pushSmallInt (if ok then -1 else 0)

/-- The tail of `DICTSET` with a slice value. -/
def setSlice (dictCell? : Option Cell) (keyBits : BitString) (valSlice : Slice) (mode : DictSetMode) : VM Unit := do
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()
  match dictSetSliceWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits valSlice mode with
  | .error e =>
      let loaded := dropFirstRootLoad dictCell? (dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictCell? keyBits)
      for c in loaded do
        VM.registerCellLoad c
      throw e
  | .ok (newRoot?, ok, created, loaded) =>
      let loaded := dropFirstRootLoad dictCell? loaded
      for c in loaded do
        VM.registerCellLoad c
      VM.chargeDictSetCreates newRoot? created (dictKeyPath · keyBits)
      match newRoot? with
      | none => VM.push .null
      | some c => VM.push (.cell c)
      if mode == .set then
        if !ok then
          throw .fatal
      else
        VM.pushSmallInt (if ok then -1 else 0)

/-- The handler of `DICTSET` (`execInstrDictDictSet`) with its tails named. -/
def dictSet (intKey unsigned byRef : Bool) (mode : DictSetMode) : VM Unit := do
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
  if byRef then
    let valRef ← VM.popCell
    let keyBits ←
      match keyBits? with
      | some bs => pure bs
      | none => throw .cellUnd
    setRef dictCell? keyBits valRef mode
  else
    let valSlice ← VM.popSlice
    let keyBits ←
      match keyBits? with
      | some bs => pure bs
      | none => throw .cellUnd
    setSlice dictCell? keyBits valSlice mode

/-- The tail of `DICTSETB` with a builder value. -/
def setBuilder (dictCell? : Option Cell) (keyBits : BitString) (newVal : Builder) (mode : DictSetMode) : VM Unit := do
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()
  match dictSetBuilderWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits newVal mode with
  | .error e =>
      let loaded := dropFirstRootLoad dictCell? (dictLookupVisitedCells (resolve := (← VM.cellResolver)) dictCell? keyBits)
      for c in loaded do
        VM.registerCellLoad c
      throw e
  | .ok (newRoot?, ok, created, loaded) =>
      let loaded := dropFirstRootLoad dictCell? loaded
      for c in loaded do
        VM.registerCellLoad c
      VM.chargeDictSetCreates newRoot? created (dictKeyPath · keyBits)
      match newRoot? with
      | none => VM.push .null
      | some c => VM.push (.cell c)
      if mode == .set then
        if !ok then
          throw .fatal
      else
        VM.pushSmallInt (if ok then -1 else 0)

/-- The handler of `DICTSETB` (`execInstrDictDictSetB`) with its tail named. -/
def dictSetB (intKey unsigned : Bool) (mode : DictSetMode) : VM Unit := do
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
  let newVal ← VM.popBuilder
  let keyBits ←
    match keyBits? with
    | some bs => pure bs
    | none => throw .cellUnd
  setBuilder dictCell? keyBits newVal mode

end DictTail

namespace TvmLean

/-! ## The update as the specifications state it -/

/-- The cells an update loads: the root (if any), then the others. -/
def Dict.loadsOf : Option Cell → List Cell → List Cell
  | some c, rest => c :: rest
  | none, rest => rest

@[vm_run] theorem Dict.loadsOf_some (c : Cell) (rest : List Cell) : Dict.loadsOf (some c) rest = c :: rest := rfl
@[vm_run] theorem Dict.loadsOf_none (rest : List Cell) : Dict.loadsOf none rest = rest := rfl

/-- The set of the model (`dictSetGenAuxWithCells`, default resolver) of the value `vb`, as a term
that is never unfolded. -/
@[irreducible] def Dict.setResRaw (root : Option Cell) (key : BitString) (vb : Builder) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) :=
  dictSetGenAuxWithCells root key (DictMap.storeB vb) mode

/-- **The result of a set** (C++ `dict_set`) of `key` to the value `vb` in mode `mode` on the
dictionary `root`: the new root, whether it changed, the number of cells created, and the cells
loaded after the root; as the model computes it (default resolver). Never unfolded by `vm_run`:
it is known through `Dict.value_setRes` and `Dict.WF.setRes`. -/
@[irreducible] def Dict.setRes (root : Option Cell) (key : BitString) (vb : Builder) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × List Cell) :=
  match Dict.setResRaw root key vb mode with
  | .ok (r, ok, c, loaded) => .ok (r, ok, c, loaded.toList.drop 1)
  | .error e => .error e

/-- The cells a lookup of `key` visits after the root (charged when a set fails). -/
@[irreducible] def Dict.visitedRest (root : Option Cell) (key : BitString) : List Cell :=
  (dictLookupVisitedCells root key).toList.drop 1

/-- **A set on a well-formed dictionary**, as `DICTSET` runs it: the root and the cells on the
key's path loaded (`VM.loadOrd`), the cells created charged, the new root pushed, then (but in
mode `.set`) the flag of the change. -/
def Dict.setRun (root : Option Cell) (key : BitString) (vb : Builder) (mode : DictSetMode) : VM Unit :=
  match Dict.setRes root key vb mode with
  | .error e => do VM.loadOrd (Dict.loadsOf root (Dict.visitedRest root key)); throw e
  | .ok (newRoot?, ok, created, rest) => do
      VM.loadOrd (Dict.loadsOf root rest)
      VM.chargeDictSetCreates newRoot? created (dictKeyPath · key)
      match newRoot? with
      | none => VM.push .null
      | some c => VM.push (.cell c)
      if mode == .set then
        if !ok then
          throw .fatal
      else
        VM.pushSmallInt (if ok then -1 else 0)

theorem Dict.setRes_ok {root : Option Cell} {key : BitString} {vb : Builder} {mode : DictSetMode}
    {r : Option Cell} {ok : Bool} {c : Nat} {loaded : Array Cell}
    (h : Dict.setResRaw root key vb mode = .ok (r, ok, c, loaded)) :
    Dict.setRes root key vb mode = .ok (r, ok, c, loaded.toList.drop 1) := by
  unfold Dict.setRes; rw [h]

theorem Dict.setRes_error {root : Option Cell} {key : BitString} {vb : Builder} {mode : DictSetMode}
    {e : Excno} (h : Dict.setResRaw root key vb mode = .error e) :
    Dict.setRes root key vb mode = .error e := by
  unfold Dict.setRes; rw [h]

/-! ## Loads -/

theorem VM.run_loadOrd_cons (c : Cell) (cs : List Cell) (st : VmState) :
    ExceptT.run (VM.loadOrd (c :: cs)) st =
      if (st.registerCellLoad c).gasExhaustedNow then (.error .outOfGas, st.registerCellLoad c)
      else ExceptT.run (VM.loadOrd cs) (st.registerCellLoad c) := by
  simp only [VM.run_loadOrd, List.isEmpty_cons, Bool.not_false, Bool.true_and, VmState.loadsAfter,
    VmState.loadsUntilOut]
  by_cases hx : (st.registerCellLoad c).gasExhaustedNow = true
  · rw [if_pos (VmState.gasExhaustedNow_loadsAfter cs hx), if_pos hx, if_pos hx]
  · rw [if_neg hx, if_neg hx]
    cases cs with
    | nil => simp [VmState.loadsAfter, hx]
    | cons d ds => simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and]

theorem DictTail.dropFirstRootLoad_cons (c : Cell) (rest : Array Cell) :
    DictTail.dropFirstRootLoad (some c) (#[c] ++ rest) = rest := by
  simp only [DictTail.dropFirstRootLoad, Id.run]
  rw [← Array.forIn_toList, Array.toList_append]
  have hb : (c == c) = true := Cell.beq_self c
  simp [hb]
  rw [← Array.forIn_toList]
  have key : ∀ (l : List Cell) (out : Array Cell),
      (forIn (m := Id) l (⟨out, true⟩ : MProd (Array Cell) Bool) fun c_1 r =>
        if r.snd = false ∧ (c_1 == c) = true then pure (ForInStep.yield ⟨r.fst, true⟩)
        else pure (ForInStep.yield ⟨r.fst.push c_1, r.snd⟩)) = ⟨out ++ l.toArray, true⟩ := by
    intro l
    induction l with
    | nil => intro out; simp; rfl
    | cons a l ih =>
      intro out
      simp only [List.forIn_cons, Bool.true_eq_false, false_and, if_false]
      show forIn (m := Id) l _ _ = _
      rw [ih]
      simp
  rw [key]
  show (#[] ++ rest.toList.toArray) = rest
  simp

/-! ## The tails -/

theorem DictTail.setSlice_eq (d : Option Cell) (k : BitString) (v : Slice) (m : DictSetMode) :
    DictTail.setSlice d k v m = DictTail.setWith d k (fun r => dictSetSliceWithCells d k v m r) m := rfl

theorem DictTail.setRef_eq (d : Option Cell) (k : BitString) (v : Cell) (m : DictSetMode) :
    DictTail.setRef d k v m = DictTail.setWith d k (fun r => dictSetRefWithCells d k v m r) m := rfl

theorem set_none_loaded {key : BitString} {sv : Builder → Except Excno Builder} {mode : DictSetMode}
    {r : Cell → Except Excno Cell} {res : Option Cell × Bool × Nat × Array Cell}
    (h : dictSetGenAuxWithCells none key sv mode r = .ok res) : res.2.2.2 = #[] := by
  rw [dictSetGenAuxWithCells.eq_def] at h
  dsimp only [bind, Except.bind] at h
  repeat' (first | (cases h; done) | split at h)
  all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)

/-- **The tail of a set instruction on a well-formed dictionary is `Dict.setRun`.** The set with
the VM's resolver is the set with the default resolver (`set_resolve`); the root and the cells
after it are ordinary (`set_loaded`, `visited_loaded`), their loads one closed form. -/
theorem DictTail.setWith_run (st : VmState) (root : Option Cell) (key : BitString) (vb : Builder)
    (mode : DictSetMode)
    (setF : (Cell → Except Excno Cell) → Except Excno (Option Cell × Bool × Nat × Array Cell))
    (hwf : Dict.WF root key.size)
    (hset : ∀ libs gv refused, setF (fun c => (libraryResolveLoads libs gv c refused).2) =
      Dict.setResRaw root key vb mode) :
    ExceptT.run (DictTail.setWith root key setF mode) st = ExceptT.run (Dict.setRun root key vb mode) st := by
  have hvis : ∀ libs gv refused,
      dictLookupVisitedCells root key (fun c => (libraryResolveLoads libs gv c refused).2) =
        dictLookupVisitedCells root key :=
    fun libs gv refused => DictMap.visited_resolve _ (resolvesOrdinary_library libs gv refused) hwf
  unfold DictTail.setWith Dict.setRun
  cases root with
  | none =>
    have hV : dictLookupVisitedCells none key = #[] := rfl
    have hVr : Dict.visitedRest none key = [] := by unfold Dict.visitedRest; rfl
    cases hres : Dict.setResRaw none key vb mode with
    | error e =>
      rw [Dict.setRes_error hres]
      simp only [VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, VM.bindRes_ok, hset, hres, hvis, hV,
        hVr, Dict.loadsOf_none]
      rfl
    | ok res =>
      rcases res with ⟨r, ok, cr, loaded⟩
      have hl : loaded = #[] := by
        have := hres
        unfold Dict.setResRaw at this
        exact set_none_loaded this
      subst hl
      rw [Dict.setRes_ok hres]
      simp only [VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, VM.bindRes_ok, hset, hres,
        Dict.loadsOf_none]
      rfl
  | some c =>
    have hc := DictMap.WF_root_ordinary hwf
    cases hres : Dict.setResRaw (some c) key vb mode with
    | error e =>
      obtain ⟨restV, hV, hordV⟩ := DictMap.visited_loaded hwf
      have hVr : Dict.visitedRest (some c) key = restV.toList := by
        unfold Dict.visitedRest; rw [hV]; simp
      rw [Dict.setRes_error hres]
      simp only [VM.run_bind, VM.run_registerCellLoad_ordinary c st hc, Dict.loadsOf_some, hVr,
        VM.run_loadOrd_cons]
      split
      · rfl
      · simp only [VM.bindRes_ok, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, hset, hres, hvis, hV,
          DictTail.dropFirstRootLoad_cons, VM.forIn_registerCellLoad,
          VM.run_registerCellLoadList_ord restV.toList hordV, VM.bindRes_bindRes_pure]
    | ok res =>
      rcases res with ⟨r, ok, cr, loaded⟩
      obtain ⟨rest, hl, hord⟩ := DictMap.set_loaded _ c key rfl hwf _ (by unfold Dict.setResRaw at hres; exact hres)
      simp only at hl
      subst hl
      rw [Dict.setRes_ok hres]
      have hdrop : ((#[c] ++ rest).toList.drop 1) = rest.toList := by simp
      simp only [VM.run_bind, VM.run_registerCellLoad_ordinary c st hc, Dict.loadsOf_some, hdrop,
        VM.run_loadOrd_cons]
      split
      · rfl
      · simp only [VM.bindRes_ok, VM.cellResolver, VM.run_bind, VM.run_get, VM.run_pure, hset, hres,
          DictTail.dropFirstRootLoad_cons, VM.forIn_registerCellLoad,
          VM.run_registerCellLoadList_ord rest.toList hord, VM.bindRes_bindRes_pure]

theorem Dict.setResRaw_slice {root : Option Cell} {key : BitString} (hwf : Dict.WF root key.size) (val : Slice)
    (mode : DictSetMode) (libs : Array Cell) (gv : Nat) (refused : Array BitString) :
    dictSetSliceWithCells root key val mode (fun c => (libraryResolveLoads libs gv c refused).2) =
      Dict.setResRaw root key (DictMap.sliceB val) mode := by
  unfold Dict.setResRaw
  rw [DictMap.dictSetSliceWithCells_eq,
    DictMap.set_resolve _ (resolvesOrdinary_library libs gv refused) _ _ _ root key rfl hwf]

theorem Dict.setResRaw_ref {root : Option Cell} {key : BitString} (hwf : Dict.WF root key.size) (c : Cell)
    (mode : DictSetMode) (libs : Array Cell) (gv : Nat) (refused : Array BitString) :
    dictSetRefWithCells root key c mode (fun c => (libraryResolveLoads libs gv c refused).2) =
      Dict.setResRaw root key (DictMap.refB c) mode := by
  unfold Dict.setResRaw
  rw [DictMap.dictSetRefWithCells_eq,
    DictMap.set_resolve _ (resolvesOrdinary_library libs gv refused) _ _ _ root key rfl hwf]

theorem DictTail.setSlice_run (st : VmState) (root : Option Cell) (key : BitString) (val : Slice)
    (mode : DictSetMode) (hwf : Dict.WF root key.size) :
    ExceptT.run (DictTail.setSlice root key val mode) st =
      ExceptT.run (Dict.setRun root key (DictMap.sliceB val) mode) st := by
  rw [DictTail.setSlice_eq]
  exact DictTail.setWith_run st root key _ mode _ hwf (Dict.setResRaw_slice hwf val mode)

theorem DictTail.setRef_run (st : VmState) (root : Option Cell) (key : BitString) (c : Cell)
    (mode : DictSetMode) (hwf : Dict.WF root key.size) :
    ExceptT.run (DictTail.setRef root key c mode) st =
      ExceptT.run (Dict.setRun root key (DictMap.refB c) mode) st := by
  rw [DictTail.setRef_eq]
  exact DictTail.setWith_run st root key _ mode _ hwf (Dict.setResRaw_ref hwf c mode)

theorem dictIntKey_size {idx : Int} {n : Nat} {bs : BitString} (h : intToBitsTwos idx n = .ok bs) :
    bs.size = n := by
  unfold intToBitsTwos at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i h0; cases h; simp [h0]
  · split at h
    · cases h
    · split at h
      · cases h; simp
      · cases h; simp

/-- The key of an integer is as long as the keys. -/
theorem dictKeyBits?_size {idx : Int} {n : Nat} {unsigned : Bool} {key : BitString}
    (h : dictKeyBits? idx n unsigned = some key) : key.size = n := by
  unfold dictKeyBits? at h
  split at h
  · rename_i hn; split at h
    · cases h; simp [hn]
    · cases h
  · split at h
    · dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases h; simp
    · dsimp only at h
      split at h
      · cases h
      · split at h
        · rename_i bs hbs; cases h; exact dictIntKey_size hbs
        · cases h

/-- `DICTSET` runs as `DictTail.dictSet` (the same code). -/
theorem DictTail.handler_eq (intKey unsigned byRef : Bool) (mode : DictSetMode) (st : VmState) :
    ExceptT.run (execInstr (.dictSet intKey unsigned byRef mode)) st =
      ExceptT.run (DictTail.dictSet intKey unsigned byRef mode) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

theorem DictTail.setBuilder_eq (d : Option Cell) (k : BitString) (v : Builder) (m : DictSetMode) :
    DictTail.setBuilder d k v m = DictTail.setWith d k (fun r => dictSetBuilderWithCells d k v m r) m := rfl

theorem Dict.setResRaw_builder {root : Option Cell} {key : BitString} (hwf : Dict.WF root key.size) (vb : Builder)
    (mode : DictSetMode) (libs : Array Cell) (gv : Nat) (refused : Array BitString) :
    dictSetBuilderWithCells root key vb mode (fun c => (libraryResolveLoads libs gv c refused).2) =
      Dict.setResRaw root key vb mode := by
  unfold Dict.setResRaw
  rw [DictMap.dictSetBuilderWithCells_eq,
    DictMap.set_resolve _ (resolvesOrdinary_library libs gv refused) _ _ _ root key rfl hwf]

theorem DictTail.setBuilder_run (st : VmState) (root : Option Cell) (key : BitString) (vb : Builder)
    (mode : DictSetMode) (hwf : Dict.WF root key.size) :
    ExceptT.run (DictTail.setBuilder root key vb mode) st = ExceptT.run (Dict.setRun root key vb mode) st := by
  rw [DictTail.setBuilder_eq]
  exact DictTail.setWith_run st root key _ mode _ hwf (Dict.setResRaw_builder hwf vb mode)

/-- `DICTSETB` runs as `DictTail.dictSetB` (the same code). -/
theorem DictTail.handlerB_eq (intKey unsigned : Bool) (mode : DictSetMode) (st : VmState) :
    ExceptT.run (execInstr (.dictSetB intKey unsigned mode)) st =
      ExceptT.run (DictTail.dictSetB intKey unsigned mode) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

/-! ## `DICTSET`: the new root and the value -/

/-- **The result of `DICTSET`** (mode `.set`): the new root (never empty), the number of cells
created and the cells loaded after the root. Never unfolded by `vm_run`; known through
`Dict.value_setSet` and `Dict.WF.setSet`. -/
@[irreducible] def Dict.setSetRes (root : Option Cell) (key : BitString) (vb : Builder) :
    Except Excno (Cell × Nat × List Cell) :=
  match Dict.setResRaw root key vb .set with
  | .ok (some c, _, created, loaded) => .ok (c, created, loaded.toList.drop 1)
  | .ok (none, _, _, _) => .error .fatal
  | .error e => .error e

/-- **`DICTSET` on a well-formed dictionary** (mode `.set`): the root and the cells on the key's
path loaded, the cells created charged, the new root pushed. -/
def Dict.setRunSet (root : Option Cell) (key : BitString) (vb : Builder) : VM Unit :=
  match Dict.setSetRes root key vb with
  | .error e => do VM.loadOrd (Dict.loadsOf root (Dict.visitedRest root key)); throw e
  | .ok (c, created, rest) => do
      VM.loadOrd (Dict.loadsOf root rest)
      VM.chargeDictSetCreates (some c) created (dictKeyPath · key)
      VM.push (.cell c)

/-- A set that changes the dictionary returns a root. -/
theorem DictMap.set_changed_root {r : Cell → Except Excno Cell} {sv : Builder → Except Excno Builder}
    {mode : DictSetMode} {root root' : Option Cell} {key : BitString} {created : Nat} {loaded : Array Cell}
    (h : dictSetGenAuxWithCells root key sv mode r = .ok (root', true, created, loaded)) : ∃ c, root' = some c := by
  rw [dictSetGenAuxWithCells.eq_def] at h
  cases root with
  | none =>
    dsimp only [bind, Except.bind] at h
    repeat' (first | (cases h; done) | (simp [pure, Except.pure] at h; done) | split at h)
    all_goals (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h)
    all_goals first | exact ⟨_, h.1.symm⟩ | (simp at h)
  | some c =>
    dsimp only [bind, Except.bind] at h
    repeat' (first | (cases h; done) | (simp [pure, Except.pure] at h; done) | split at h)
    all_goals (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h)
    all_goals first | exact ⟨_, h.1.symm⟩ | (simp at h)

/-- In mode `.set`, the set runs as `Dict.setRunSet`. -/
theorem Dict.setRun_set (st : VmState) (root : Option Cell) (key : BitString) (vb : Builder) :
    ExceptT.run (Dict.setRun root key vb .set) st = ExceptT.run (Dict.setRunSet root key vb) st := by
  unfold Dict.setRun Dict.setRunSet
  cases hres : Dict.setResRaw root key vb .set with
  | error e =>
    have h2 : Dict.setSetRes root key vb = .error e := by unfold Dict.setSetRes; rw [hres]
    rw [Dict.setRes_error hres, h2]
  | ok res =>
    rcases res with ⟨r, ok, cr, loaded⟩
    have hraw := hres
    unfold Dict.setResRaw at hraw
    have hok : ok = true := DictMap.set_set_changed _ root key rfl _ hraw
    subst hok
    obtain ⟨c, rfl⟩ := DictMap.set_changed_root hraw
    have h2 : Dict.setSetRes root key vb = .ok (c, cr, loaded.toList.drop 1) := by
      unfold Dict.setSetRes; rw [hres]
    rw [Dict.setRes_ok hres, h2]
    simp only [VM.run_bind]
    rfl

/-- **Get after `DICTSET`, on the map**: the new root maps `key` to the value stored and every other
key of the same length as before. -/
theorem Dict.value_setSet {root : Option Cell} {key : BitString} {vb : Builder} {c : Cell} {created : Nat}
    {rest : List Cell} (hwf : Dict.WF root key.size) (h : Dict.setSetRes root key vb = .ok (c, created, rest))
    (key' : BitString) (hk' : key'.size = key.size) :
    Dict.value (some c) key' = if key' = key then some vb.finalize else Dict.value root key' := by
  unfold Dict.setSetRes Dict.setResRaw at h
  split at h
  · rename_i c' ok cr loaded hres
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    have hok : ok = true := DictMap.set_set_changed _ root key rfl _ hres
    subst hok
    exact Dict.value_set hwf hres key' hk'
  · cases h
  · cases h

/-- `DICTSET` keeps a dictionary well-formed. -/
theorem Dict.WF.setSet {root : Option Cell} {key : BitString} {vb : Builder} {c : Cell} {created : Nat}
    {rest : List Cell} {n : Nat} (hwf : Dict.WF root n) (hk : key.size = n)
    (h : Dict.setSetRes root key vb = .ok (c, created, rest)) : Dict.WF (some c) n := by
  subst hk
  unfold Dict.setSetRes Dict.setResRaw at h
  split at h
  · rename_i c' ok cr loaded hres
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    exact Dict.WF.set hwf hres
  · cases h
  · cases h

/-- **Get after `DICT*SET`/`ADD`/`REPLACE`, on the map**: if the dictionary changed (`ok`), `key`
maps to the value stored and every other key as before. -/
theorem Dict.value_setRes {root root' : Option Cell} {key : BitString} {vb : Builder} {mode : DictSetMode}
    {created : Nat} {rest : List Cell} (hwf : Dict.WF root key.size)
    (h : Dict.setRes root key vb mode = .ok (root', true, created, rest))
    (key' : BitString) (hk' : key'.size = key.size) :
    Dict.value root' key' = if key' = key then some vb.finalize else Dict.value root key' := by
  unfold Dict.setRes Dict.setResRaw at h
  split at h
  · rename_i r ok cr loaded hres
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -, -⟩ := h
    exact Dict.value_set hwf hres key' hk'
  · cases h

/-- A set that does not change the dictionary (`ADD` of a present key, `REPLACE` of an absent one)
leaves the root. -/
theorem Dict.setRes_unchanged {root root' : Option Cell} {key : BitString} {vb : Builder} {mode : DictSetMode}
    {created : Nat} {rest : List Cell} (h : Dict.setRes root key vb mode = .ok (root', false, created, rest)) :
    root' = root := by
  unfold Dict.setRes Dict.setResRaw at h
  split at h
  · rename_i r ok cr loaded hres
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -, -⟩ := h
    exact DictMap.set_unchanged hres
  · cases h

/-- A set keeps a dictionary well-formed. -/
theorem Dict.WF.setRes {root root' : Option Cell} {key : BitString} {vb : Builder} {mode : DictSetMode}
    {ok : Bool} {created : Nat} {rest : List Cell} {n : Nat} (hwf : Dict.WF root n) (hk : key.size = n)
    (h : Dict.setRes root key vb mode = .ok (root', ok, created, rest)) : Dict.WF root' n := by
  subst hk
  unfold Dict.setRes Dict.setResRaw at h
  split at h
  · rename_i r ok' cr loaded hres
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -, -⟩ := h
    exact Dict.WF.set hwf hres
  · cases h

theorem Slice.readBits_size_of_haveBits {k : Slice} {n : Nat} (h : k.haveBits n = true) : (k.readBits n).size = n := by
  simp only [Slice.haveBits, decide_eq_true_eq] at h
  simp only [Slice.readBits, Array.size_extract]
  omega

namespace Spec

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with an integer key and a slice value (`DICT{I,U}SET`, ...), on a well-formed dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetInt_set (st : VmState) (s : Stack) (val : Slice) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.slice val)).push (.int (.num idx))).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictSet true unsigned false .set)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.slice val) })
      | some key => ExceptT.run (Dict.setRunSet (some root) key (DictMap.sliceB val)) { st with stack := s } := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← Dict.setRun_set]
    rw [← DictTail.setSlice_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with an integer key and a slice value (`DICT{I,U}SET`, ...), on a well-formed dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetInt_flag (st : VmState) (s : Stack) (val : Slice) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.slice val)).push (.int (.num idx))).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSet true unsigned false mode)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.slice val) })
      | some key => ExceptT.run (Dict.setRun (some root) key (DictMap.sliceB val) mode) { st with stack := s } := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← DictTail.setSlice_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with an integer key and a slice value (`DICT{I,U}SET`, ...), on the empty dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetIntEmpty_set (st : VmState) (s : Stack) (val : Slice) (idx : Int) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.slice val)).push (.int (.num idx))).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictSet true unsigned false .set)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.slice val) })
      | some key => ExceptT.run (Dict.setRunSet none key (DictMap.sliceB val)) { st with stack := s } := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    dsimp only
    rw [← Dict.setRun_set]
    rw [← DictTail.setSlice_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with an integer key and a slice value (`DICT{I,U}SET`, ...), on the empty dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetIntEmpty_flag (st : VmState) (s : Stack) (val : Slice) (idx : Int) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.slice val)).push (.int (.num idx))).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSet true unsigned false mode)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.slice val) })
      | some key => ExceptT.run (Dict.setRun none key (DictMap.sliceB val) mode) { st with stack := s } := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    dsimp only
    rw [← DictTail.setSlice_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with an integer key and a reference value (`DICT{I,U}SETREF`, ...), on a well-formed dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetIntRef_set (st : VmState) (s : Stack) (val : Cell) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.cell val)).push (.int (.num idx))).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictSet true unsigned true .set)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.cell val) })
      | some key => ExceptT.run (Dict.setRunSet (some root) key (DictMap.refB val)) { st with stack := s } := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← Dict.setRun_set]
    rw [← DictTail.setRef_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with an integer key and a reference value (`DICT{I,U}SETREF`, ...), on a well-formed dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetIntRef_flag (st : VmState) (s : Stack) (val : Cell) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.cell val)).push (.int (.num idx))).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSet true unsigned true mode)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.cell val) })
      | some key => ExceptT.run (Dict.setRun (some root) key (DictMap.refB val) mode) { st with stack := s } := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← DictTail.setRef_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with an integer key and a reference value (`DICT{I,U}SETREF`, ...), on the empty dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetIntRefEmpty_set (st : VmState) (s : Stack) (val : Cell) (idx : Int) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.cell val)).push (.int (.num idx))).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictSet true unsigned true .set)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.cell val) })
      | some key => ExceptT.run (Dict.setRunSet none key (DictMap.refB val)) { st with stack := s } := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    dsimp only
    rw [← Dict.setRun_set]
    rw [← DictTail.setRef_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with an integer key and a reference value (`DICT{I,U}SETREF`, ...), on the empty dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetIntRefEmpty_flag (st : VmState) (s : Stack) (val : Cell) (idx : Int) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.cell val)).push (.int (.num idx))).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSet true unsigned true mode)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.cell val) })
      | some key => ExceptT.run (Dict.setRun none key (DictMap.refB val) mode) { st with stack := s } := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    dsimp only
    rw [← DictTail.setRef_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with a slice key and a slice value (`DICTSET`, ...), on a well-formed dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetSlice_set (st : VmState) (s : Stack) (val : Slice) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.slice val)).push (.slice k)).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictSet false unsigned false .set)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRunSet (some root) (k.readBits n.toNat) (DictMap.sliceB val)) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← Dict.setRun_set]
    rw [← DictTail.setSlice_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with a slice key and a slice value (`DICTSET`, ...), on a well-formed dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetSlice_flag (st : VmState) (s : Stack) (val : Slice) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.slice val)).push (.slice k)).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSet false unsigned false mode)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRun (some root) (k.readBits n.toNat) (DictMap.sliceB val) mode) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← DictTail.setSlice_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with a slice key and a slice value (`DICTSET`, ...), on the empty dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetSliceEmpty_set (st : VmState) (s : Stack) (val : Slice) (k : Slice) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.slice val)).push (.slice k)).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictSet false unsigned false .set)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRunSet none (k.readBits n.toNat) (DictMap.sliceB val)) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    rw [← Dict.setRun_set]
    rw [← DictTail.setSlice_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with a slice key and a slice value (`DICTSET`, ...), on the empty dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetSliceEmpty_flag (st : VmState) (s : Stack) (val : Slice) (k : Slice) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.slice val)).push (.slice k)).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSet false unsigned false mode)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRun none (k.readBits n.toNat) (DictMap.sliceB val) mode) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    rw [← DictTail.setSlice_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with a slice key and a reference value (`DICTSETREF`, ...), on a well-formed dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetSliceRef_set (st : VmState) (s : Stack) (val : Cell) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.cell val)).push (.slice k)).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictSet false unsigned true .set)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRunSet (some root) (k.readBits n.toNat) (DictMap.refB val)) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← Dict.setRun_set]
    rw [← DictTail.setRef_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with a slice key and a reference value (`DICTSETREF`, ...), on a well-formed dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetSliceRef_flag (st : VmState) (s : Stack) (val : Cell) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.cell val)).push (.slice k)).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSet false unsigned true mode)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRun (some root) (k.readBits n.toNat) (DictMap.refB val) mode) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← DictTail.setRef_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with a slice key and a reference value (`DICTSETREF`, ...), on the empty dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetSliceRefEmpty_set (st : VmState) (s : Stack) (val : Cell) (k : Slice) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.cell val)).push (.slice k)).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictSet false unsigned true .set)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRunSet none (k.readBits n.toNat) (DictMap.refB val)) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    rw [← Dict.setRun_set]
    rw [← DictTail.setRef_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with a slice key and a reference value (`DICTSETREF`, ...), on the empty dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetSliceRefEmpty_flag (st : VmState) (s : Stack) (val : Cell) (k : Slice) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.cell val)).push (.slice k)).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSet false unsigned true mode)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRun none (k.readBits n.toNat) (DictMap.refB val) mode) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    rw [← DictTail.setRef_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSet, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with an integer key and a builder value (`DICT{I,U}SETB`, ...), on a well-formed dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetIntB_set (st : VmState) (s : Stack) (val : Builder) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.builder val)).push (.int (.num idx))).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictSetB true unsigned .set)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.builder val) })
      | some key => ExceptT.run (Dict.setRunSet (some root) key val) { st with stack := s } := by
  rw [DictTail.handlerB_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← Dict.setRun_set]
    rw [← DictTail.setBuilder_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with an integer key and a builder value (`DICT{I,U}SETB`, ...), on a well-formed dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetIntB_flag (st : VmState) (s : Stack) (val : Builder) (idx : Int) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.builder val)).push (.int (.num idx))).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSetB true unsigned mode)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.builder val) })
      | some key => ExceptT.run (Dict.setRun (some root) key val mode) { st with stack := s } := by
  rw [DictTail.handlerB_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← DictTail.setBuilder_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with an integer key and a builder value (`DICT{I,U}SETB`, ...), on the empty dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetIntBEmpty_set (st : VmState) (s : Stack) (val : Builder) (idx : Int) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.builder val)).push (.int (.num idx))).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictSetB true unsigned .set)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.builder val) })
      | some key => ExceptT.run (Dict.setRunSet none key val) { st with stack := s } := by
  rw [DictTail.handlerB_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    dsimp only
    rw [← Dict.setRun_set]
    rw [← DictTail.setBuilder_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with an integer key and a builder value (`DICT{I,U}SETB`, ...), on the empty dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetIntBEmpty_flag (st : VmState) (s : Stack) (val : Builder) (idx : Int) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.builder val)).push (.int (.num idx))).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSetB true unsigned mode)) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s.push (.builder val) })
      | some key => ExceptT.run (Dict.setRun none key val mode) { st with stack := s } := by
  rw [DictTail.handlerB_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']
  | some key =>
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    dsimp only
    rw [← DictTail.setBuilder_run _ _ _ _ _ hwf']
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with a slice key and a builder value (`DICTSETB`, ...), on a well-formed dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetSliceB_set (st : VmState) (s : Stack) (val : Builder) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.builder val)).push (.slice k)).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictSetB false unsigned .set)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRunSet (some root) (k.readBits n.toNat) val) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handlerB_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← Dict.setRun_set]
    rw [← DictTail.setBuilder_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with a slice key and a builder value (`DICTSETB`, ...), on a well-formed dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetSliceB_flag (st : VmState) (s : Stack) (val : Builder) (k : Slice) (root : Cell) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.builder val)).push (.slice k)).push (.cell root)).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSetB false unsigned mode)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRun (some root) (k.readBits n.toNat) val mode) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handlerB_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← DictTail.setBuilder_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.set` with a slice key and a builder value (`DICTSETB`, ...), on the empty dictionary: `Dict.setRunSet`. -/
@[vm_spec] theorem dictSetSliceBEmpty_set (st : VmState) (s : Stack) (val : Builder) (k : Slice) (n : Int)
    (unsigned : Bool) (hs : st.stack = ((((s.push (.builder val)).push (.slice k)).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictSetB false unsigned .set)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRunSet none (k.readBits n.toNat) val) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handlerB_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    rw [← Dict.setRun_set]
    rw [← DictTail.setBuilder_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']

/-- C++ `exec_dict_set` (dictops.cpp:272) in mode `.add` or `.replace` with a slice key and a builder value (`DICTSETB`, ...), on the empty dictionary: `Dict.setRun`, then the flag. -/
@[vm_spec] theorem dictSetSliceBEmpty_flag (st : VmState) (s : Stack) (val : Builder) (k : Slice) (n : Int)
    (unsigned : Bool) (mode : DictSetMode) (hs : st.stack = ((((s.push (.builder val)).push (.slice k)).push .null).push (.int (.num n))))
    (hn : 0 ≤ n ∧ n ≤ 1023) (_hmode : mode ≠ .set) :
    ExceptT.run (execInstr (.dictSetB false unsigned mode)) st =
      if k.haveBits n.toNat then ExceptT.run (Dict.setRun none (k.readBits n.toNat) val mode) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.handlerB_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF none key.size := Dict.WF.empty _
    rw [← DictTail.setBuilder_run _ _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']
  · rw [if_neg hk]
    vm_simp [DictTail.dictSetB, hs, hk, hn1, hn']

end Spec

end TvmLean

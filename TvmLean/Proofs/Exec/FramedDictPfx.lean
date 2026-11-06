import TvmLean.Proofs.Exec.FramedDictOptRef

/-!
# `PFXDICTGETQ`, `PFXDICTGET`, `PFXDICT{SET,REPLACE,ADD}`, `PFXDICTDEL` on any dictionary, framed

The lookup of a prefix in a prefix dictionary whose cells a run does not know, and the set or delete
of a key in one, are framed (`TvmLean.Framed.ExecFramed`, `TvmLean/Proofs/Exec/Framed.lean`): the
instruction changes the stack, the gas, the loaded cells and libraries only; it fails only with an
exception of code 2 or more. `PFXDICTGETQ` pushes the key (any slice) and `0`, or the prefix found,
its value, the rest of the key (any slices) and `-1`; `PFXDICTGET` the prefix, value and rest;
`PFXDICTSET`/`REPLACE`/`ADD` and `PFXDICTDEL` the new root (null or a cell) and a flag.
`PFXDICTGETJMP`, `PFXDICTGETEXEC` and `PFXDICTSWITCH` jump: they are not framed.

* `pfxLookupPrefixWithCells_err`, `pfxSetGenAuxWithCells_err`, `pfxLookupDeleteWithCells_err`,
  `slicePrefix_real`: the private walks of TvmLean/Semantics/Exec/Dict/Ext.lean (reached by
  `private%`, `private_eq%`) fail only with cell_und, dict_err or cell_ov;
* `DictTail.pfxGet`, `DictTail.pfxSet`, `DictTail.pfxDel`: the handlers, the same code
  (`DictTail.pfxGetHandler_eq`, ...);
* `Framed.pfxGetQ_framed`, `Framed.pfxGet_framed`, `Framed.pfxSet_framed`, `Framed.pfxDel_framed`,
  tactics `vm_pfx_getq_any`, `vm_pfx_get_any`, `vm_pfx_set_any`, `vm_pfx_del_any`.
-/

namespace TvmLean.Framed

open TvmLean

/-! ## Errors of the walks -/

theorem ErrDel.throw {α : Type} {e : Excno} (he : 2 ≤ e.toInt) (l : Array Cell) :
    ErrDel (MonadExcept.throw (e, l) : Except (Excno × Array Cell) α) := by
  intro e' l' h
  have h' : (Except.error (e, l) : Except (Excno × Array Cell) α) = .error (e', l') := h
  injection h' with h''
  injection h'' with h1 _
  subst h1
  exact he

/-- The lookup of a prefix below a node fails only with an exception of code 2 or more (cell_und,
dict_err). -/
theorem pfxLookupPrefixGo_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) (keyBits : BitString)
    (keyLen : Nat) (m : Nat) :
    ∀ (cell : Cell) (nRem pos : Nat) (loaded : Array Cell),
      ErrDel ((private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixGo) keyBits keyLen
        cell nRem m pos loaded r) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro cell nRem pos loaded
    rw [private_eq% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixGo]
    repeat' (first
      | exact ErrDel.pure _ | exact ErrDel.ok _
      | exact ErrDel.throw (by decide) _
      | exact ErrDel.throw (ErrDict.real (parseDictLabel_err _ _ r hr) _ (by assumption)) _
      | exact ih _ (by omega) _ _ _ _
      | (refine ErrDel.bind ?_ (fun _ => ?_))
      | (refine ErrDel.dite (fun _ => ?_) (fun _ => ?_)) | (refine ErrDel.ite ?_ ?_) | split
      | (dsimp only))

/-- **The lookup of a prefix fails only with an exception of code 2 or more.** -/
theorem pfxLookupPrefixWithCells_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r)
    (root : Option Cell) (keyBits : BitString) (keyLen n : Nat) :
    ErrDel ((private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells) root keyBits
      keyLen n r) := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells
  split
  · exact ErrDel.pure _
  · exact pfxLookupPrefixGo_err r hr _ _ _ _ _ _ _

set_option maxHeartbeats 4000000 in
/-- **The set of a prefix dictionary fails only with an exception of code 2 or more**, if the value
it stores does (by induction on the key's length). -/
theorem pfxSetGenAuxWithCells_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r)
    (storeVal : Builder → Except Excno Builder) (hs : ∀ b, ErrReal (storeVal b)) (mode : DictSetMode) (k : Nat) :
    ∀ (root : Option Cell) (key : BitString) (n : Nat), key.size = k →
      ErrDel ((private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells) root key n
        storeVal mode r) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro root key n hk
    rw [private_eq% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells]
    repeat' (first
      | exact ErrDel.pure _ | exact ErrDel.ok _
      | exact ErrDel.throw (by decide) _
      | exact ErrDel.withLoads (hs _) _
      | exact ErrDel.withLoads (ErrDict.real (parseDictLabel_err _ _ r hr)) _
      | exact ErrDel.withLoads (builderStoreBitsChecked_real _ _) _
      | exact ErrDel.withLoads (builderAppendCellChecked_real _ _) _
      | exact ErrDel.withLoads (builderStoreRefChecked_real _ _) _
      | exact ErrDel.underCell (ih _ (by simp only [Array.size_extract]; omega) _ _ _ rfl) _
      | (refine ErrDel.bind ?_ (fun _ => ?_))
      | (refine ErrDel.dite (fun _ => ?_) (fun _ => ?_)) | (refine ErrDel.ite ?_ ?_) | split
      | (dsimp only))

/-- The measure of the recursion of the delete: the key below a fork the key's label matches is
shorter. -/
theorem pfxDel_measure {key lb : BitString} {k len : Nat} (hk : key.size = k)
    (hl : ¬ bitsCommonPrefixLen lb (key.take (min key.size len)) < len) (he : ¬ len = key.size) :
    (key.extract (len + 1) key.size).size < k := by
  have hb := bitsCommonPrefixLen_le_right lb (key.take (min key.size len))
  simp only [Array.size_extract, Array.take_eq_extract] at *
  omega

set_option maxHeartbeats 4000000 in
/-- **The delete of a key from a prefix dictionary fails only with an exception of code 2 or more**
(by induction on the key's length). -/
theorem pfxLookupDeleteWithCells_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) (k : Nat) :
    ∀ (root : Option Cell) (key : BitString) (n : Nat), key.size = k →
      ErrDel ((private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupDeleteWithCells) root key n r) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro root key n hk
    rw [private_eq% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupDeleteWithCells]
    repeat' (first
      | exact ErrDel.pure _ | exact ErrDel.ok _
      | exact ErrDel.throw (by decide) _
      | exact ErrDel.withLoads (ErrDict.real (parseDictLabel_err _ _ r hr)) _
      | exact ErrDel.withLoads (builderStoreBitsChecked_real _ _) _
      | exact ErrDel.withLoads (builderAppendCellChecked_real _ _) _
      | exact ErrDel.underCell (ih _ (pfxDel_measure hk (by assumption) (by assumption)) _ _ _ rfl) _
      | exact ErrDel.underCell (ih _ (by simp only [Array.size_extract]; omega) _ _ _ rfl) _
      | (refine ErrDel.bind ?_ (fun _ => ?_))
      | (refine ErrDel.dite (fun _ => ?_) (fun _ => ?_)) | (refine ErrDel.ite ?_ ?_) | split
      | (dsimp only))

/-- The cut of a prefix off a slice fails only with cell_und. -/
theorem slicePrefix_err (s : Slice) (bits refs : Nat) :
    ErrReal ((private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix) s bits refs) := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix
  repeat' (first
    | exact ErrReal.ok _ | exact ErrReal.pure _
    | exact ErrReal.throw (by decide)
    | (refine ErrReal.bind ?_ (fun _ => ?_)) | (refine ErrReal.ite ?_ ?_) | split | (dsimp only))

theorem pfxLookupPrefixWithCells_real {root : Option Cell} {keyBits : BitString} {keyLen n : Nat}
    {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno} {l : Array Cell}
    (h : (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells) root keyBits
      keyLen n (fun c => (libraryResolveLoads libs gv c refused).2) = .error (e, l)) : 2 ≤ e.toInt :=
  pfxLookupPrefixWithCells_err _ (resolverCellUnd_library _ _ _) _ _ _ _ e l h

theorem pfxSetSliceWithCells_real {root : Option Cell} {key : BitString} {n : Nat} {v : Slice}
    {mode : DictSetMode} {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno} {l : Array Cell}
    (h : (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells) root key n
      (fun b => builderAppendCellChecked b v.toCellRemaining) mode
      (fun c => (libraryResolveLoads libs gv c refused).2) = .error (e, l)) : 2 ≤ e.toInt :=
  pfxSetGenAuxWithCells_err _ (resolverCellUnd_library _ _ _) _
    (fun b => builderAppendCellChecked_real b v.toCellRemaining) mode _ root key n rfl e l h

theorem pfxLookupDeleteWithCells_real {root : Option Cell} {key : BitString} {n : Nat}
    {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno} {l : Array Cell}
    (h : (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupDeleteWithCells) root key n
      (fun c => (libraryResolveLoads libs gv c refused).2) = .error (e, l)) : 2 ≤ e.toInt :=
  pfxLookupDeleteWithCells_err _ (resolverCellUnd_library _ _ _) _ root key n rfl e l h

theorem slicePrefix_real {s : Slice} {bits refs : Nat} {e : Excno}
    (h : (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix) s bits refs = .error e) :
    2 ≤ e.toInt :=
  slicePrefix_err s bits refs e h

macro_rules
  | `(tactic| steps_err) => `(tactic| first
      | exact pfxLookupPrefixWithCells_real (by assumption)
      | exact pfxSetSliceWithCells_real (by assumption)
      | exact pfxLookupDeleteWithCells_real (by assumption)
      | exact slicePrefix_real (by assumption))

/-! ## The relations -/

/-- What `PFXDICTGETQ` leaves on the stack `s` under its three arguments: the key and `0`, or the
prefix found, its value, the rest of the key and `-1` (slices). -/
def PfxGetQOk (s s' : Stack) : Prop :=
  (∃ k : Slice, s' = (s.push (.slice k)).push (.int (.num 0))) ∨
    ∃ (p v r : Slice), s' = (((s.push (.slice p)).push (.slice v)).push (.slice r)).push (.int (.num (-1)))

/-- What `PFXDICTGET` leaves on the stack `s` under its three arguments: the prefix found, its
value and the rest of the key (slices). -/
abbrev PfxGetOk (s s' : Stack) : Prop :=
  ∃ (p v r : Slice), s' = ((s.push (.slice p)).push (.slice v)).push (.slice r)

/-- What `PFXDICT{SET,REPLACE,ADD}` and `PFXDICTDEL` leave on the stack `s` under their arguments:
the new root (null or a cell) and a flag (any integer: `-1` or `0`). -/
def RootFlagOk (s s' : Stack) : Prop :=
  (∃ f : Int, s' = (s.push .null).push (.int (.num f))) ∨
    (∃ (c : Cell) (f : Int), s' = (s.push (.cell c)).push (.int (.num f)))

/-- `PfxGetQOk` of the stack under the three arguments (the key, the dictionary, the key length). -/
abbrev PfxGetQOk3 (s s' : Stack) : Prop :=
  ∃ (s0 : Stack) (a b c : Value), s = ((s0.push a).push b).push c ∧ PfxGetQOk s0 s'

/-- `PfxGetOk` of the stack under the three arguments. -/
abbrev PfxGetOk3 (s s' : Stack) : Prop :=
  ∃ (s0 : Stack) (a b c : Value), s = ((s0.push a).push b).push c ∧ PfxGetOk s0 s'

/-- `RootFlagOk` of the stack under the three arguments of `PFXDICTDEL`. -/
abbrev RootFlagOk3 (s s' : Stack) : Prop :=
  ∃ (s0 : Stack) (a b c : Value), s = ((s0.push a).push b).push c ∧ RootFlagOk s0 s'

/-- `RootFlagOk` of the stack under the four arguments of `PFXDICTSET` (the value, the key, the
dictionary, the key length). -/
abbrev RootFlagOk4 (s s' : Stack) : Prop :=
  ∃ (s0 : Stack) (a b c d : Value), s = (((s0.push a).push b).push c).push d ∧ RootFlagOk s0 s'

macro_rules
  | `(tactic| steps_close) => `(tactic| (intros; subst_vars; first
      | exact ⟨_, _, _, _, rfl, Or.inl ⟨_, rfl⟩⟩
      | exact ⟨_, _, _, _, rfl, Or.inr ⟨_, _, _, rfl⟩⟩
      | exact ⟨_, _, _, _, rfl, ⟨_, _, _, rfl⟩⟩
      | exact ⟨_, _, _, _, rfl, Or.inr ⟨_, _, rfl⟩⟩
      | exact ⟨_, _, _, _, _, rfl, Or.inl ⟨_, rfl⟩⟩
      | exact ⟨_, _, _, _, _, rfl, Or.inr ⟨_, _, rfl⟩⟩))

end TvmLean.Framed

/-! ## The handlers with their private helpers named -/

namespace DictTail

open TvmLean

/-- `DictExt.pushBool` (private in TvmLean/Semantics/Exec/Dict/Ext.lean): the same code. -/
def extPushBool (b : Bool) : VM Unit :=
  VM.pushSmallInt (if b then -1 else 0)

/-- `DictExt.pfxLookupPrefixWithCells` (private, recursive: the definition itself). -/
abbrev extPfxLookupPrefixWithCells :=
  private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells

/-- `DictExt.pfxSetGenAuxWithCells` (private, recursive: the definition itself). -/
abbrev extPfxSetGenAuxWithCells :=
  private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells

/-- `DictExt.pfxLookupDeleteWithCells` (private, recursive: the definition itself). -/
abbrev extPfxLookupDeleteWithCells :=
  private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupDeleteWithCells

/-- `DictExt.slicePrefix` (private: the definition itself). -/
abbrev extSlicePrefix :=
  private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix

/-- The handler of `PFXDICT{SET,REPLACE,ADD}` (`execInstrDictExt`): the same code. -/
def pfxSet (mode : DictSetMode) : VM Unit := do
  -- C++ `exec_pfx_dict_set` (dictops.cpp:570): `check_underflow(4)` from version 9, 3 before
  VM.checkUnderflow (if (← get).globalVersion ≥ 9 then 4 else 3)
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let keySlice ← VM.popSlice
  let newValue ← VM.popSlice
  let keyBits : BitString := keySlice.readBits keySlice.bitsRemaining
  if keyBits.size > n then
    extPushDictRoot dictCell?
    extPushBool false
  else
    extPrechargeRootLoad dictCell?
    let storeVal : Builder → Except Excno Builder :=
      fun b => builderAppendCellChecked b newValue.toCellRemaining
    match extPfxSetGenAuxWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits n storeVal mode with
    | .error (e, loaded0) =>
        -- the nodes loaded before the error are charged, then the error is raised (C++ order)
        extRegisterLoaded (extLoadedWithoutRoot dictCell? loaded0)
        throw e
    | .ok (newRoot?, ok, created, loaded0) =>
        let loaded := extLoadedWithoutRoot dictCell? loaded0
        extRegisterLoaded loaded
        VM.chargeDictSetCreates newRoot? created (pfxDictKeyPath · keyBits n)
        extPushDictRoot newRoot?
        extPushBool ok

/-- The handler of `PFXDICTDEL` (`execInstrDictExt`): the same code. -/
def pfxDel : VM Unit := do
  -- C++ `exec_pfx_dict_delete` (dictops.cpp:584): `check_underflow(3)` from version 9, 2 before
  VM.checkUnderflow (if (← get).globalVersion ≥ 9 then 3 else 2)
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let keySlice ← VM.popSlice
  let keyBits : BitString := keySlice.readBits keySlice.bitsRemaining
  if keyBits.size > n then
    extPushDictRoot dictCell?
    extPushBool false
  else
    extPrechargeRootLoad dictCell?
    match extPfxLookupDeleteWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits n with
    | .error (e, loaded0) =>
        -- the nodes loaded before the error are charged, then the error is raised (C++ order)
        extRegisterLoaded (extLoadedWithoutRoot dictCell? loaded0)
        throw e
    | .ok (oldVal?, newRoot?, created, loaded0) =>
        let loaded := extLoadedWithoutRoot dictCell? loaded0
        extRegisterLoaded loaded
        extConsumeCreatedGas created
        let ok := oldVal?.isSome
        -- Update root only if deletion succeeded.
        let outRoot? := if ok then newRoot? else dictCell?
        extPushDictRoot outRoot?
        extPushBool ok

/-- The handler of `PFXDICTGET{Q,,JMP,EXEC}` (`execInstrDictExt`): the same code. -/
def pfxGet (kind : PfxDictGetKind) : VM Unit := do
  VM.checkUnderflow 3
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let cs0 ← VM.popSlice
  extPrechargeRootLoad dictCell?
  let keyBits : BitString := cs0.readBits cs0.bitsRemaining
  match extPfxLookupPrefixWithCells (resolve := (← VM.cellResolver)) dictCell? keyBits keyBits.size n with
  | .error (e, loaded0) =>
      -- the nodes loaded before the error are charged, then the error is raised (C++ order)
      let loaded :=
        match dictCell? with
        | none => loaded0
        | some root => loaded0.filter (fun c => c != root)
      extRegisterLoaded loaded
      throw e
  | .ok (none, _pos, loaded) =>
      -- Not found / cannot parse.
      let loaded :=
        match dictCell? with
        | none => loaded
        | some root => loaded.filter (fun c => c != root)
      extRegisterLoaded loaded
      match kind with
      | .get | .getExec =>
          throw .cellUnd
      | .getQ =>
          VM.push (.slice cs0)
          extPushBool false
      | .getJmp =>
          VM.push (.slice cs0)
  | .ok (some valueSlice, pfxLen, loaded0) =>
      let loaded :=
        match dictCell? with
        | none => loaded0
        | some root => loaded0.filter (fun c => c != root)
      extRegisterLoaded loaded
      let (pfxSlice, cs1) ←
        match extSlicePrefix cs0 pfxLen 0 with
        | .ok x => pure x
        | .error e => throw e
      VM.push (.slice pfxSlice)
      match kind with
      | .getQ | .get =>
          VM.push (.slice valueSlice)
      | .getJmp | .getExec =>
          pure ()
      VM.push (.slice cs1)
      match kind with
      | .getQ =>
          extPushBool true
      | .get =>
          pure ()
      | .getJmp | .getExec =>
          let cont : Continuation := .ordinary valueSlice (.quit 0) OrdCregs.empty OrdCdata.empty
          modify fun st =>
            match kind with
            | .getExec => st.callTo cont
            | _ => st.jumpTo cont

end DictTail

namespace TvmLean

set_option maxHeartbeats 1000000 in
/-- `PFXDICT{SET,REPLACE,ADD}` runs as `DictTail.pfxSet` (the same code). -/
theorem DictTail.pfxSetHandler_eq (mode : DictSetMode) (st : VmState) :
    ExceptT.run (execInstr (.dictExt (.pfxSet mode))) st = ExceptT.run (DictTail.pfxSet mode) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

set_option maxHeartbeats 1000000 in
/-- `PFXDICTDEL` runs as `DictTail.pfxDel` (the same code). -/
theorem DictTail.pfxDelHandler_eq (st : VmState) :
    ExceptT.run (execInstr (.dictExt .pfxDel)) st = ExceptT.run DictTail.pfxDel st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

set_option maxHeartbeats 1000000 in
/-- `PFXDICTGET{Q,,JMP,EXEC}` runs as `DictTail.pfxGet` (the same code). -/
theorem DictTail.pfxGetHandler_eq (kind : PfxDictGetKind) (st : VmState) :
    ExceptT.run (execInstr (.dictExt (.pfxGet kind))) st = ExceptT.run (DictTail.pfxGet kind) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

end TvmLean

namespace TvmLean.Framed

open TvmLean

/-! ## The handlers, framed -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`PFXDICT{SET,REPLACE,ADD}` on any stack is framed**: the stack under its four arguments
`RootFlagOk`. -/
theorem Steps.pfxSet (mode : DictSetMode) :
    Steps (DictTail.pfxSet mode) (fun _ s s' => RootFlagOk4 s s') := by
  unfold DictTail.pfxSet DictTail.extPushDictRoot DictTail.extPushBool
  simp only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind]
  steps_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`PFXDICTDEL` on any stack is framed**: the stack under its three arguments `RootFlagOk`. -/
theorem Steps.pfxDel : Steps DictTail.pfxDel (fun _ s s' => RootFlagOk3 s s') := by
  unfold DictTail.pfxDel DictTail.extPushDictRoot DictTail.extPushBool
  simp only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind]
  steps_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`PFXDICTGETQ` on any stack is framed**: the stack under its three arguments `PfxGetQOk`. -/
theorem Steps.pfxGetQ : Steps (DictTail.pfxGet .getQ) (fun _ s s' => PfxGetQOk3 s s') := by
  unfold DictTail.pfxGet DictTail.extPushBool
  simp only [VM.cellResolver, VM.pushSmallInt, bind_assoc, pure_bind]
  steps_auto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`PFXDICTGET` on any stack is framed**: the stack under its three arguments `PfxGetOk`. -/
theorem Steps.pfxGet : Steps (DictTail.pfxGet .get) (fun _ s s' => PfxGetOk3 s s') := by
  unfold DictTail.pfxGet
  simp only [VM.cellResolver, bind_assoc, pure_bind]
  steps_auto

/-- The top three entries of a stack written out, and the stack under them. -/
theorem push3_inj {s s0 : Stack} {a b c a' b' c' : Value}
    (e : ((s.push a).push b).push c = ((s0.push a').push b').push c') : s = s0 := by
  obtain ⟨_, e1⟩ := Array.push_eq_push.mp e
  obtain ⟨_, e2⟩ := Array.push_eq_push.mp e1
  obtain ⟨_, e3⟩ := Array.push_eq_push.mp e2
  exact e3

/-- The top four entries of a stack written out, and the stack under them. -/
theorem push4_inj {s s0 : Stack} {a b c d a' b' c' d' : Value}
    (e : (((s.push a).push b).push c).push d = (((s0.push a').push b').push c').push d') : s = s0 := by
  obtain ⟨_, e1⟩ := Array.push_eq_push.mp e
  exact push3_inj e1

/-- **`PFXDICTGETQ` on any dictionary is framed**: from a stack `s a b c`, `PfxGetQOk s`, or an
exception of code 2 or more. -/
theorem pfxGetQ_framed (s : Stack) (a b c : Value) (st : VmState) (hs : st.stack = ((s.push a).push b).push c) :
    ExecFramed (.dictExt (.pfxGet .getQ)) (PfxGetQOk s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.pfxGetQ st
  rw [← DictTail.pfxGetHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, a', b', c', e, hok⟩ := h2 () h
  rw [hs] at e
  rw [push3_inj e]
  exact hok

/-- **`PFXDICTGET` on any dictionary is framed**: from a stack `s a b c`, `PfxGetOk s`, or an
exception of code 2 or more. -/
theorem pfxGet_framed (s : Stack) (a b c : Value) (st : VmState) (hs : st.stack = ((s.push a).push b).push c) :
    ExecFramed (.dictExt (.pfxGet .get)) (PfxGetOk s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.pfxGet st
  rw [← DictTail.pfxGetHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, a', b', c', e, hok⟩ := h2 () h
  rw [hs] at e
  rw [push3_inj e]
  exact hok

/-- **`PFXDICTDEL` on any dictionary is framed**: from a stack `s a b c`, `RootFlagOk s`, or an
exception of code 2 or more. -/
theorem pfxDel_framed (s : Stack) (a b c : Value) (st : VmState) (hs : st.stack = ((s.push a).push b).push c) :
    ExecFramed (.dictExt .pfxDel) (RootFlagOk s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.pfxDel st
  rw [← DictTail.pfxDelHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, a', b', c', e, hok⟩ := h2 () h
  rw [hs] at e
  rw [push3_inj e]
  exact hok

/-- **`PFXDICT{SET,REPLACE,ADD}` on any dictionary is framed**: from a stack `s a b c d`,
`RootFlagOk s`, or an exception of code 2 or more. -/
theorem pfxSet_framed (mode : DictSetMode) (s : Stack) (a b c d : Value) (st : VmState)
    (hs : st.stack = (((s.push a).push b).push c).push d) :
    ExecFramed (.dictExt (.pfxSet mode)) (RootFlagOk s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.pfxSet mode st
  rw [← DictTail.pfxSetHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, a', b', c', d', e, hok⟩ := h2 () h
  rw [hs] at e
  rw [push4_inj e]
  exact hok

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_pfx_getq_any`: the run in the goal is about to run `PFXDICTGETQ` on a prefix dictionary it
does not know: by `Framed.runWith_framed3` and `Framed.pfxGetQ_framed`, two goals: `P` of a result
that commits nothing, and `P` of the runs from the state after it with a stack
`Framed.PfxGetQOk s`, any gas, loaded cells and libraries. -/
elab "vm_pfx_getq_any" : tactic =>
  Exec.framedAny "vm_pfx_getq_any" 3 ``DictExtInstr.pfxGet 1 ``Framed.pfxGetQ_framed
    (fun args => do return (← whnfR args[0]!).isConstOf ``PfxDictGetKind.getQ) false

open Lean Meta Elab Tactic in
/-- `vm_pfx_get_any`: as `vm_pfx_getq_any`, for `PFXDICTGET` (`Framed.PfxGetOk s`). -/
elab "vm_pfx_get_any" : tactic =>
  Exec.framedAny "vm_pfx_get_any" 3 ``DictExtInstr.pfxGet 1 ``Framed.pfxGet_framed
    (fun args => do return (← whnfR args[0]!).isConstOf ``PfxDictGetKind.get) false

open Lean Meta Elab Tactic in
/-- `vm_pfx_del_any`: as `vm_pfx_getq_any`, for `PFXDICTDEL` (`Framed.RootFlagOk s`). -/
elab "vm_pfx_del_any" : tactic =>
  Exec.framedAny "vm_pfx_del_any" 3 ``DictExtInstr.pfxDel 0 ``Framed.pfxDel_framed

open Lean Meta Elab Tactic in
/-- `vm_pfx_set_any`: as `vm_pfx_getq_any`, for `PFXDICT{SET,REPLACE,ADD}` on a stack of four entries
(`Framed.RootFlagOk s`). -/
elab "vm_pfx_set_any" : tactic =>
  Exec.framedAny "vm_pfx_set_any" 4 ``DictExtInstr.pfxSet 1 ``Framed.pfxSet_framed

end TvmLean

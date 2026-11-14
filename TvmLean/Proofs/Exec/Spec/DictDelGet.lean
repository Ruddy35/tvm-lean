import TvmLean.Proofs.Exec.Spec.DictSetGet

/-!
# Specifications: delete-and-get on symbolic dictionaries

`DICT{,I,U}DELGET{,REF}` (`.dictExt (.mutGet intKey unsigned byRef .del)`) on a well-formed
dictionary or on `null`, stated through the map of the dictionary, as
`Proofs/Exec/Spec/DictDel.lean` states `DICT{,I,U}DEL`:

* `Spec.dictDelGet{Int,Slice}{,Empty}`: `Dict.delGetRun`: the root and the cells on the key's path
  loaded (`VM.loadOrd`), the cells created charged, the new root (`null` if empty) pushed, then the
  old value and `-1` (`Dict.pushOld`: the slice, or with `REF` the reference it must consist of,
  dict_err else), or `0` alone;
* the result `Dict.delGetRes` is known through `Dict.value_delGetRes` (the old value is the value
  the key had; after it the key is absent, every other key as before) and `Dict.WF.delGetRes`.

The lookup-and-set specifications (`Spec.dictSetGet*`, `Proofs/Exec/Spec/DictSetGet.lean`) take
`mode ≠ .del`: in mode `.del` the handler runs other code (C++ `exec_dict_deleteget`, not
`exec_dict_setget`), written again here with its tail named (`DictTail.mutGetDel`,
`DictTail.delGetTail`, the same code: `DictTail.mutGetDelHandler_eq`), the tail stated once
(`DictTail.delGetTail_run`).
-/

namespace DictTail

open TvmLean

/-- The tail of `DICT{,I,U}DELGET{,REF}` after the key is read, pushing an old value with
`pushOld`. -/
def delGetWith (dictCell? : Option Cell) (keyBits : BitString) (pushOld : Slice → VM Unit) : VM Unit := do
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
      match oldVal? with
      | none =>
          pushBool false
      | some oldVal =>
          pushOld oldVal

/-- The tail of `DICT{,I,U}DELGET{,REF}`: the old value pushed as a slice, or with `byRef` as the
reference it must consist of. -/
def delGetTail (dictCell? : Option Cell) (keyBits : BitString) (byRef : Bool) : VM Unit :=
  if byRef then
    delGetWith dictCell? keyBits (fun oldVal => do
      let c ← extractRefOrThrow oldVal
      VM.push (.cell c)
      pushBool true)
  else
    delGetWith dictCell? keyBits (fun oldVal => do
      VM.push (.slice oldVal)
      pushBool true)

/-- The handler of `.dictExt (.mutGet ..)` in mode `.del` (`TvmLean/Semantics/Exec/Dict/Ext.lean`),
with its tail named. -/
def mutGetDel (intKey unsigned byRef : Bool) : VM Unit := do
  VM.checkUnderflow 3
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let keyBits? : Option BitString ←
    if intKey then
      let idx ← VM.popIntFinite
      match dictKeyBits? idx n unsigned with
      | some bs => pure (some bs)
      | none => throw .rangeChk
    else
      let keySlice ← VM.popSlice
      if keySlice.haveBits n then
        pure (some (keySlice.readBits n))
      else
        throw .cellUnd
  let keyBits ←
    match keyBits? with
    | some bs => pure bs
    | none => throw .cellUnd
  delGetTail dictCell? keyBits byRef

end DictTail

namespace TvmLean

/-! ## The delete-and-get as the specifications state it -/

/-- **The result of a delete-and-get** (C++ `dict.lookup_delete`, crypto/vm/dict.cpp:1189) of `key`
from the dictionary `root`: the old value (none if the key was absent), the new root, the number of
cells created and the cells loaded after the root; or the error with the cells loaded before it. As
the model computes it (default resolver); never unfolded by `vm_run`: known through
`Dict.value_delGetRes` and `Dict.WF.delGetRes`. -/
@[irreducible] def Dict.delGetRes (root : Option Cell) (key : BitString) :
    Except (Excno × List Cell) (Option Slice × Option Cell × Nat × List Cell) :=
  match dictDeleteWithLoads root key with
  | .ok (old, r, created, loaded) => .ok (old, r, created, Dict.withoutRoot root loaded)
  | .error (e, loaded) => .error (e, Dict.withoutRoot root loaded)

/-- **A delete-and-get on a well-formed dictionary**, as `DICT{,I,U}DELGET{,REF}` run it: the root
and the cells on the key's path loaded (`VM.loadOrd`), the cells created charged, the new root
(`null` if empty) pushed, then the old value and `-1` (`Dict.pushOld`), or `0` if the key was
absent. -/
def Dict.delGetRun (root : Option Cell) (key : BitString) (byRef : Bool) : VM Unit :=
  match Dict.delGetRes root key with
  | .error (e, rest) => do VM.loadOrd (Dict.loadsOf root rest); throw e
  | .ok (old?, newRoot?, created, rest) => do
      VM.loadOrd (Dict.loadsOf root rest)
      VM.chargeCellCreates created
      match newRoot? with
      | none => VM.push .null
      | some c => VM.push (.cell c)
      match old? with
      | none => VM.pushSmallInt 0
      | some old => Dict.pushOld old byRef true

/-- **Get after a delete-and-get, on the map**: the old value is the value the key had; after it
the key is absent, every other key of the same length as before. -/
theorem Dict.value_delGetRes {root root' : Option Cell} {key : BitString} {old : Option Slice} {created : Nat}
    {rest : List Cell} (hwf : Dict.WF root key.size)
    (h : Dict.delGetRes root key = .ok (old, root', created, rest)) :
    old.map Slice.toCellRemaining = Dict.value root key ∧
      ∀ key' : BitString, key'.size = key.size →
        Dict.value root' key' = if key' = key then none else Dict.value root key' := by
  unfold Dict.delGetRes at h
  split at h
  · rename_i old' r cr loaded hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -, -⟩ := h
    obtain ⟨h1, h2⟩ := Dict.value_deleteAny hwf hd
    exact ⟨h1.symm, h2⟩
  · cases h

/-- A delete-and-get keeps a dictionary well-formed. -/
theorem Dict.WF.delGetRes {root root' : Option Cell} {key : BitString} {old : Option Slice} {created : Nat}
    {rest : List Cell} {n : Nat} (hwf : Dict.WF root n) (hk : key.size = n)
    (h : Dict.delGetRes root key = .ok (old, root', created, rest)) : Dict.WF root' n := by
  subst hk
  unfold Dict.delGetRes at h
  split at h
  · rename_i old' r cr loaded hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -, -⟩ := h
    exact Dict.WF.delete hwf hd
  · cases h

/-! ## The tails -/

/-- **The tail of a delete-and-get on a well-formed dictionary is `Dict.delGetRun`.** The delete
with the VM's resolver is the delete with the default resolver (`delete_resolve`), and the cells it
loads are ordinary (`deleteWithLoads_loaded`): their loads are one closed form. -/
theorem DictTail.delGetWith_run (st : VmState) (root : Option Cell) (key : BitString) (byRef : Bool)
    (pushOld : Slice → VM Unit) (hwf : Dict.WF root key.size)
    (hpush : ∀ old, pushOld old = Dict.pushOld old byRef true) :
    ExceptT.run (DictTail.delGetWith root key pushOld) st = ExceptT.run (Dict.delGetRun root key byRef) st := by
  have hpo : pushOld = fun old => Dict.pushOld old byRef true := funext hpush
  subst hpo
  unfold DictTail.delGetWith Dict.delGetRun
  cases root with
  | none =>
    have hd : ∀ r, dictDeleteWithLoads none key r = .ok (none, none, 0, #[]) := fun _ => rfl
    have hres : Dict.delGetRes none key = .ok (none, none, 0, []) := by
      unfold Dict.delGetRes; rw [hd]; rfl
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
      have hres : Dict.delGetRes (some c) key = .error (e, Dict.withoutRoot (some c) loaded) := by
        unfold Dict.delGetRes; rw [hdel]
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
      have hres : Dict.delGetRes (some c) key = .ok (old, r, created, Dict.withoutRoot (some c) loaded) := by
        unfold Dict.delGetRes; rw [hdel]
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
        cases r <;> cases old <;> rfl

/-- **The tail of `DICT{,I,U}DELGET{,REF}` on a well-formed dictionary is `Dict.delGetRun`.** -/
theorem DictTail.delGetTail_run (st : VmState) (root : Option Cell) (key : BitString) (byRef : Bool)
    (hwf : Dict.WF root key.size) :
    ExceptT.run (DictTail.delGetTail root key byRef) st = ExceptT.run (Dict.delGetRun root key byRef) st := by
  unfold DictTail.delGetTail
  cases byRef with
  | false =>
    rw [if_neg (show ¬ (false = true) by decide)]
    exact DictTail.delGetWith_run st root key false _ hwf (fun _ => rfl)
  | true =>
    rw [if_pos (show true = true from rfl)]
    refine DictTail.delGetWith_run st root key true _ hwf (fun old => ?_)
    unfold Dict.pushOld DictTail.extractRefOrThrow
    simp only [if_true]
    split <;> rfl

/-- `.dictExt (.mutGet ..)` in mode `.del` runs as `DictTail.mutGetDel` (the same code). -/
theorem DictTail.mutGetDelHandler_eq (intKey unsigned byRef : Bool) (st : VmState) :
    ExceptT.run (execInstr (.dictExt (.mutGet intKey unsigned byRef .del))) st =
      ExceptT.run (DictTail.mutGetDel intKey unsigned byRef) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

/-! ## The specifications -/

namespace Spec

/-- C++ `exec_dict_deleteget` (crypto/vm/dictops.cpp:402) with an integer key
(`DICT{I,U}DELGET{,REF}`), on a well-formed dictionary: `Dict.delGetRun` (dictops.cpp:423-438: the
new root, then the old value and `-1`, or `0`). The key is read by `pop_int_finite` (dictops.cpp:411);
one out of the range of `n`-bit keys is range_chk (`integer_key` is not quiet, crypto/vm/dict.cpp:418-433,
so the miss branch at dictops.cpp:412-416 is never taken). -/
@[vm_spec] theorem dictDelGetInt (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned byRef : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictExt (.mutGet true unsigned byRef .del))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s })
      | some key => ExceptT.run (Dict.delGetRun (some root) key byRef) { st with stack := s } := by
  rw [DictTail.mutGetDelHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.mutGetDel, hs, hk, hn1, hn', VM.popMaybeCell]
  | some key =>
    have hwf' : Dict.WF (some root) key.size := by rw [dictKeyBits?_size hk]; exact hwf
    dsimp only
    rw [← DictTail.delGetTail_run _ _ _ _ hwf']
    vm_simp [DictTail.mutGetDel, hs, hk, hn1, hn', VM.popMaybeCell]

/-- C++ `exec_dict_deleteget` (crypto/vm/dictops.cpp:402) with an integer key on the empty dictionary
(`null`): `Dict.delGetRun none` (nothing found, nothing loaded: `null` and `0`). -/
@[vm_spec] theorem dictDelGetIntEmpty (st : VmState) (s : Stack) (idx : Int) (n : Int) (unsigned byRef : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push .null).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictExt (.mutGet true unsigned byRef .del))) st =
      match dictKeyBits? idx n.toNat unsigned with
      | none => (.error .rangeChk, { st with stack := s })
      | some key => ExceptT.run (Dict.delGetRun none key byRef) { st with stack := s } := by
  rw [DictTail.mutGetDelHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned with
  | none => vm_simp [DictTail.mutGetDel, hs, hk, hn1, hn', VM.popMaybeCell]
  | some key =>
    dsimp only
    rw [← DictTail.delGetTail_run _ _ _ _ (Dict.WF.empty _)]
    vm_simp [DictTail.mutGetDel, hs, hk, hn1, hn', VM.popMaybeCell]

/-- C++ `exec_dict_deleteget` (crypto/vm/dictops.cpp:402) with a slice key (`DICTDELGET{,REF}`), on a
well-formed dictionary: `Dict.delGetRun` of the first `n` bits of the key (cell_und if it is
shorter, dictops.cpp:418-421). -/
@[vm_spec] theorem dictDelGetSlice (st : VmState) (s : Stack) (k : Slice) (root : Cell) (n : Int)
    (unsigned byRef : Bool)
    (hs : st.stack = ((s.push (.slice k)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) (hwf : Dict.WF (some root) n.toNat) :
    ExceptT.run (execInstr (.dictExt (.mutGet false unsigned byRef .del))) st =
      if k.haveBits n.toNat then
        ExceptT.run (Dict.delGetRun (some root) (k.readBits n.toNat) byRef) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.mutGetDelHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    have key_def : (k.readBits n.toNat).size = n.toNat := Slice.readBits_size_of_haveBits hk
    generalize hkey : k.readBits n.toNat = key at key_def
    have hwf' : Dict.WF (some root) key.size := by rw [key_def]; exact hwf
    rw [← DictTail.delGetTail_run _ _ _ _ hwf']
    rw [← hkey]
    vm_simp [DictTail.mutGetDel, hs, hk, hn1, hn', VM.popMaybeCell]
  · rw [if_neg hk]
    vm_simp [DictTail.mutGetDel, hs, hk, hn1, hn', VM.popMaybeCell]

/-- C++ `exec_dict_deleteget` (crypto/vm/dictops.cpp:402) with a slice key on the empty dictionary
(`null`): `Dict.delGetRun none`. -/
@[vm_spec] theorem dictDelGetSliceEmpty (st : VmState) (s : Stack) (k : Slice) (n : Int) (unsigned byRef : Bool)
    (hs : st.stack = ((s.push (.slice k)).push .null).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictExt (.mutGet false unsigned byRef .del))) st =
      if k.haveBits n.toNat then
        ExceptT.run (Dict.delGetRun none (k.readBits n.toNat) byRef) { st with stack := s }
      else (.error .cellUnd, { st with stack := s }) := by
  rw [DictTail.mutGetDelHandler_eq]
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  by_cases hk : k.haveBits n.toNat = true
  · rw [if_pos hk]
    rw [← DictTail.delGetTail_run _ _ _ _ (Dict.WF.empty _)]
    vm_simp [DictTail.mutGetDel, hs, hk, hn1, hn', VM.popMaybeCell]
  · rw [if_neg hk]
    vm_simp [DictTail.mutGetDel, hs, hk, hn1, hn', VM.popMaybeCell]

end Spec


/-- `vm_dict_wf` also follows a delete-and-get (`Dict.WF.delGetRes`). -/
macro_rules
  | `(tactic| vm_dict_wf_ext) =>
    `(tactic| (refine Dict.WF.delGetRes ?_ ?_ (by assumption) <;> first | vm_dict_wf | vm_dict_key))

end TvmLean

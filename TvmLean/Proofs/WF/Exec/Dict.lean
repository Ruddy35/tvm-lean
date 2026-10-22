import TvmLean.Proofs.WF.DictPrims

/-!
# The Dict family keeps states well-formed

`execInstrDict_WF : FamilyWF execInstrDict`, the last of the 14 family obligations of
`execInstr_WF`, from one theorem per handler of `TvmLean/Semantics/Exec/Dict/` (the pattern of
`Step.lean`). The handlers push the values the dictionary functions find and the roots they build;
these are well-formed by the lemmas of `DictPrims.lean` (and `dictLookupWithCells_WF` of
`Cells.lean`), restated here in the form `generalize_opaque` takes (`DictWF.lookup`,
`DictWF.setRef`, `DictWF.delete`, `DictWF.pfxSet`, ...: every argument quantified). Each handler
generalizes the dictionary functions it calls (`generalize_opaque`, `Cells.lean`), so that neither
`mvcgen` nor the kernel computes with them, and `grind` (`dict_leaf`, `dict_close`) closes the
conditions with their specifications. The private helpers of `Exec/Dict/Ext.lean` get
specifications (`DictExt.pushDictRoot_spec`, ...).

What `mvcgen` cannot take is bound by hand (`JoinPoints.lean`):

* the key a handler computes, `let keyBits? ← if intKey then ... else ...`: `mvcgen` would match on
  a value bound by `pure` (`(kernel) application type mismatch`); `dict_jp` proves the join point
  after it once, with its jumps, and leaves its body. The same with the pair `DICTIGETNEXT` binds
  (the value found and the cells loaded), the prefix and rest of the key of `PFXDICTGET` and
  `PFXDICTSWITCH`, and the mutable value and root of `DICTREMMIN` after a removal; binding them by
  hand also keeps `mvcgen` from copying the code after each join point (the `DICTMIN` handler took
  230 s, 15 s now; the handler of `Exec/Dict/Ext.lean` is split by operation, each generalizing
  only the functions it calls: its `DICTSETGET` operations took 374 s, about 50 s now);
* the `match newRoot? with | none => ... | some c => ...` of `DICTSET`, `DICTSETB` and
  `DICTREPLACEB` reuses the matcher of the private `dropFirstRootLoad` of each of their files; the
  splitters Lean 4.24 makes for these matchers in this module all get the same name, so `mvcgen`
  splits only the first of them (`failed to transform matcher`, `Unknown constant [anonymous]`,
  a `PANIC`): these handlers split the root by hand (`cases`) before `mvcgen`;
* the calls and jumps of `DICTIGETEXEC`, `PFXDICTGETEXEC`, `PFXDICTSWITCH` (`DictWF.callOrJump`,
  `VmState.WF.callTo`, `VmState.WF.jumpTo`), and the integers keys pushed (`IntVal.num`
  generalized).

`natToBits` and `Cell.mkOrdinary` are irreducible here (the key cells of `DICTGETNEXT` and
`DICTMIN` are `Cell.mkOrdinary` of the key).
-/

open Std.Do

set_option mvcgen.warning false
set_option maxHeartbeats 4000000

namespace TvmLean

attribute [local irreducible] natToBits Cell.mkOrdinary

/-- Assigns the invariant `VmState.WF` to every loop `mvcgen` left (the loops over the cells a
dictionary function loaded). -/
macro "dict_invariants" : tactic =>
  `(tactic| all_goals try exact post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩)

/-! ## The dictionary functions in the form `generalize_opaque` takes -/

theorem DictWF.lookup : ∀ root key r s cells, ResolverWF r →
    (∀ c, root = some c → c.WF) → dictLookupWithCells root key r = .ok (some s, cells) → s.WF :=
  fun _ _ _ _ _ hr hroot h => dictLookupWithCells_WF hr hroot h

theorem DictWF.minMax : ∀ root n fetchMax invertFirst r p, ResolverWF r →
    (∀ c, root = some c → c.WF) → dictMinMaxWithCells root n fetchMax invertFirst r = .ok p →
    ∀ v k, p.1 = some (v, k) → v.WF ∧ k.size ≤ n :=
  fun _ _ _ _ _ _ hr hroot h => dictMinMaxWithCells_WF hr hroot h

theorem DictWF.nearest : ∀ root hint fetchNext allowEq invertFirst r p, ResolverWF r →
    (∀ c, root = some c → c.WF) →
    dictNearestWithCells root hint fetchNext allowEq invertFirst r = .ok p →
    ∀ v k, p.1 = some (v, k) → v.WF ∧ k.size ≤ hint.size :=
  fun _ _ _ _ _ _ _ hr hroot h => dictNearestWithCells_WF hr hroot h

theorem DictWF.setRef : ∀ root key val mode r newRoot ok created loaded, ResolverWF r →
    (∀ c, root = some c → c.WF) → Cell.WF val →
    dictSetRefWithCells root key val mode r = .ok (newRoot, ok, created, loaded) →
    ∀ c, newRoot = some c → c.WF :=
  fun _ _ _ _ _ _ _ _ _ hr hroot hv h => dictSetRefWithCells_WF hr hroot hv h

theorem DictWF.setSlice : ∀ root key val mode r newRoot ok created loaded, ResolverWF r →
    (∀ c, root = some c → c.WF) → Slice.WF val →
    dictSetSliceWithCells root key val mode r = .ok (newRoot, ok, created, loaded) →
    ∀ c, newRoot = some c → c.WF :=
  fun _ _ _ _ _ _ _ _ _ hr hroot hv h => dictSetSliceWithCells_WF hr hroot hv h

theorem DictWF.setBuilder : ∀ root key val mode r newRoot ok created loaded, ResolverWF r →
    (∀ c, root = some c → c.WF) → Builder.WF val →
    dictSetBuilderWithCells root key val mode r = .ok (newRoot, ok, created, loaded) →
    ∀ c, newRoot = some c → c.WF :=
  fun _ _ _ _ _ _ _ _ _ hr hroot hv h => dictSetBuilderWithCells_WF hr hroot hv h

theorem DictWF.lookupSetRef : ∀ root key val mode r old newRoot ok created loaded, ResolverWF r →
    (∀ c, root = some c → c.WF) → Cell.WF val →
    dictLookupSetRefWithCells root key val mode r = .ok (old, newRoot, ok, created, loaded) →
    (∀ s, old = some s → s.WF) ∧ ∀ c, newRoot = some c → c.WF :=
  fun _ _ _ _ _ _ _ _ _ _ hr hroot hv h => dictLookupSetRefWithCells_WF hr hroot hv h

theorem DictWF.lookupSetSlice : ∀ root key val mode r old newRoot ok created loaded, ResolverWF r →
    (∀ c, root = some c → c.WF) → Slice.WF val →
    dictLookupSetSliceWithCells root key val mode r = .ok (old, newRoot, ok, created, loaded) →
    (∀ s, old = some s → s.WF) ∧ ∀ c, newRoot = some c → c.WF :=
  fun _ _ _ _ _ _ _ _ _ _ hr hroot hv h => dictLookupSetSliceWithCells_WF hr hroot hv h

theorem DictWF.lookupSetBuilder : ∀ root key val mode r old newRoot ok created loaded,
    ResolverWF r → (∀ c, root = some c → c.WF) → Builder.WF val →
    dictLookupSetBuilderWithCells root key val mode r = .ok (old, newRoot, ok, created, loaded) →
    (∀ s, old = some s → s.WF) ∧ ∀ c, newRoot = some c → c.WF :=
  fun _ _ _ _ _ _ _ _ _ _ hr hroot hv h => dictLookupSetBuilderWithCells_WF hr hroot hv h

theorem DictWF.delete : ∀ root key r old newRoot created loaded, ResolverWF r →
    (∀ c, root = some c → c.WF) →
    dictDeleteWithLoads root key r = .ok (old, newRoot, created, loaded) →
    (∀ s, old = some s → s.WF) ∧ ∀ c, newRoot = some c → c.WF :=
  fun _ _ _ _ _ _ _ hr hroot h => dictDeleteWithLoads_WF hr hroot h

theorem DictWF.subdict : ∀ root keyBits pfx prefixLen removePrefix r newRoot changed created
    loaded, ResolverWF r → (∀ c, root = some c → c.WF) →
    dictExtractPrefixSubdictWithCells root keyBits pfx prefixLen removePrefix r =
      .ok (newRoot, changed, created, loaded) →
    ∀ c, newRoot = some c → c.WF :=
  fun _ _ _ _ _ _ _ _ _ _ hr hroot h => dictExtractPrefixSubdictWithCells_WF hr hroot h

theorem DictWF.pfxLookup : ∀ root keyBits keyLen n r p, ResolverWF r →
    (∀ c, root = some c → c.WF) →
    (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells) root
      keyBits keyLen n r = .ok p →
    ∀ s, p.1 = some s → s.WF :=
  fun _ _ _ _ _ _ hr hroot h => pfxLookupPrefixWithCells_WF hr hroot h

theorem DictWF.pfxDelete : ∀ root key n r p, ResolverWF r → (∀ c, root = some c → c.WF) →
    (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupDeleteWithCells) root key
      n r = .ok p →
    (∀ s, p.1 = some s → s.WF) ∧ ∀ c, p.2.1 = some c → c.WF :=
  fun _ _ _ _ _ hr hroot h => pfxLookupDeleteWithCells_WF hr hroot h

theorem DictWF.slicePrefix : ∀ s bits refs p, s.WF →
    (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix) s bits refs = .ok p →
    p.1.WF ∧ p.2.WF :=
  fun _ _ _ _ hs h => slicePrefix_WF hs h

theorem DictWF.pfxSetSlice : ∀ root key n v mode r p, ResolverWF r →
    (∀ c, root = some c → c.WF) → Slice.WF v →
    (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxSetGenAuxWithCells) root key n
      (fun b => builderAppendCellChecked b v.toCellRemaining) mode r = .ok p →
    ∀ c, p.1 = some c → c.WF :=
  fun _ _ _ _ _ _ _ hr hroot hv h => pfxSetGenAuxWithCells_WF hr hroot hv h

/-- The call or jump of `DICTIGETEXEC` and `DICTIGETJMP` (`modify`): to the value found. -/
theorem DictWF.callOrJump {st : VmState} (h : st.WF) {k : Continuation} (hk : k.WF) (b : Bool) :
    (if b = true then st.callTo k else st.jumpTo k).WF := by
  split
  · exact h.callTo hk
  · exact h.jumpTo hk

/-! ## The helpers of `Exec/Dict/Ext.lean` -/

@[spec] theorem DictExt.pushBool_spec (b : Bool) :
    ⦃fun st => ⌜st.WF⌝⦄ (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pushBool) b
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pushBool
  mvcgen

@[spec] theorem DictExt.pushDictRoot_spec (c? : Option Cell) :
    ⦃fun st => ⌜st.WF ∧ ∀ c, c? = some c → c.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pushDictRoot) c?
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pushDictRoot
  mvcgen
  all_goals wf_vc

@[spec] theorem DictExt.consumeCreatedGas_spec (n : Nat) :
    ⦃fun st => ⌜st.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.consumeCreatedGas) n
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.consumeCreatedGas
  mvcgen

@[spec] theorem DictExt.registerLoaded_spec (l : Array Cell) :
    ⦃fun st => ⌜st.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.registerLoaded) l
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.registerLoaded
  mvcgen invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_vc

@[spec] theorem DictExt.prechargeRootLoad_spec (c? : Option Cell) :
    ⦃fun st => ⌜st.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.prechargeRootLoad) c?
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.prechargeRootLoad
  mvcgen

@[spec] theorem DictExt.extractRefOrThrow_spec (s : Slice) :
    ⦃fun st => ⌜st.WF ∧ s.WF⌝⦄
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.extractRefOrThrow) s
      ⦃post⟨fun c st => ⌜st.WF ∧ c.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold_private TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.extractRefOrThrow
  mvcgen
  all_goals wf_cells

/-- A condition `mvcgen` leaves on a dictionary handler: the cells and slices built, the results
of the dictionary functions (their specifications are in the context), the calls and jumps of
`DICTIGETEXEC`, `PFXDICTGETEXEC`, `PFXDICTSWITCH`, ... -/
macro "dict_leaf" : tactic => `(tactic|
  first
    | (refine DictWF.callOrJump ?_ ?_ _ <;> wf_cont)
    | (refine VmState.WF.jumpTo ?_ ?_ <;> wf_cont)
    | (refine VmState.WF.callTo ?_ ?_ <;> wf_cont)
    | (subst_vars; refine VmState.WF.jumpTo ?_ ?_ <;> wf_cont)
    | (subst_vars; refine VmState.WF.callTo ?_ ?_ <;> wf_cont)
    | (wf_cells [Cell.mkOrdinary_WF, Slice.readBits_size_le]; done)
    | (wf_cells [Slice.haveBits_iff, Slice.haveRefs_iff, Slice.WF]; done))

/-- The conditions `mvcgen` leaves on a dictionary handler: the invariant of the loops over the
cells a dictionary function loaded, then `dict_leaf`. -/
macro "dict_close" : tactic => `(tactic| (
  dict_invariants
  all_goals try exact ExceptConds.entails.refl _
  all_goals (try simp only [SPred.down_pure] at *)
  all_goals dict_leaf))

/-- The first join point of the goal, taking one argument and needing nothing of it (the key a
handler computed, `let keyBits? ← if intKey then ... else ...`, where `mvcgen` would match on a
value bound by `pure`; or the code after an `if` or a `match`): its jumps are closed by its
specification, and the goal left is its body. -/
macro "dict_jp" : tactic => `(tactic| (
  extract_lets -underBinder +onlyGivenNames jp
  have hjp : ∀ k, VM.KeepsWFIf True (jp k) := ?jp
  · clear_value jp
    mvcgen
    dict_invariants
    all_goals try exact ExceptConds.entails.refl _
    all_goals first
      | (jp_close (hjp _) <;> trivial)
      | dict_leaf
  intro k
  apply VM.KeepsWFIf.of_keeps
  intro _
  unfold jp))

/-- The loops over the cells a dictionary function loaded keep states well-formed. -/
theorem DictWF.registerLoads (cells : Array Cell) :
    (forIn cells PUnit.unit fun c _ => do
      VM.registerCellLoad c
      pure (ForInStep.yield PUnit.unit) : VM PUnit).Keeps fun _ => True := by
  refine VM.Keeps.forIn_array (fun _ => True) cells trivial fun c _ _ => ?_
  mvcgen
  all_goals wf_vc

/-! ## The handlers -/

/-- C++ `exec_store_dict` (`STDICT`): the root stored as a reference, after the check of the
builder. -/
theorem execInstrDictStdict_WF : FamilyWF execInstrDictStdict := by
  intro i next hi hnext
  unfold execInstrDictStdict
  split
  · refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec 2)) fun _ _ => ?_
    refine VM.Keeps.bind VM.popBuilder_spec fun b hb => ?_
    refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
    cases d <;> mvcgen <;>
      (try simp only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte] at *) <;>
      wf_cells [Builder.canExtendBy_iff, Builder.WF, Builder.storeBits]
  · exact hnext

/-- C++ `exec_skip_dict` (`SKIPDICT`). -/
theorem execInstrDictSkipdict_WF : FamilyWF execInstrDictSkipdict := by
  intro i next hi hnext
  mvcgen [execInstrDictSkipdict, hnext]
  all_goals wf_cells [Slice.haveBits_iff, Slice.haveRefs_iff, Slice.WF]

/-- C++ `exec_push_const_dict` (`DICTPUSHCONST`): the root the instruction carries. -/
theorem execInstrDictDictPushConst_WF : FamilyWF execInstrDictDictPushConst := by
  intro i next hi hnext
  mvcgen [execInstrDictDictPushConst, hnext]
  all_goals wf_cells [Instr.wf_dictPushConst]

/-- C++ `exec_load_dict` (`LDDICT`, `PLDDICT`, quiet or not). -/
theorem execInstrDictLddict_WF : FamilyWF execInstrDictLddict := by
  intro i next hi hnext
  mvcgen [execInstrDictLddict, hnext]
  all_goals wf_cells [Slice.haveBits_iff, Slice.haveRefs_iff, Slice.WF]

/-- C++ `exec_dict_get` (`DICTGET`, `DICTIGETREF`, ...): the value found, or its reference. -/
theorem execInstrDictDictGet_WF : FamilyWF execInstrDictDictGet := by
  intro i next hi hnext
  unfold execInstrDictDictGet
  split
  · refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec 3)) fun _ _ => ?_
    refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
    refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
    extract_lets -underBinder +onlyGivenNames jp
    have hjp : ∀ k, VM.KeepsWFIf True (jp k) := ?jp
    · clear_value jp
      mvcgen
      all_goals first
        | (jp_close (hjp _) <;> trivial)
        | wf_cells
    intro k
    apply VM.KeepsWFIf.of_keeps
    intro _
    unfold jp
    have hlk := DictWF.lookup
    generalize_opaque lk := @dictLookupWithCells at hlk
    generalize_opaque lkv := @dictLookupVisitedCells
    mvcgen
    dict_close
  · exact hnext

/-- C++ `exec_dict_get_exec` (`DICTIGETJMP`, `DICTUGETEXEC`, ...): a call or jump to the value
found. -/
theorem execInstrDictDictGetExec_WF : FamilyWF execInstrDictDictGetExec := by
  intro i next hi hnext
  unfold execInstrDictDictGetExec
  have hlk := DictWF.lookup
  generalize_opaque lk := @dictLookupWithCells at hlk
  generalize_opaque lkv := @dictLookupVisitedCells
  mvcgen [hnext]
  dict_close

/-- C++ `exec_dict_set` (`DICTSET`, `DICTIREPLACEREF`, `DICTUADD`, ...): the new root. -/
theorem execInstrDictDictSet_WF : FamilyWF execInstrDictDictSet := by
  intro i next hi hnext
  unfold execInstrDictDictSet
  split
  · refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec 4)) fun _ _ => ?_
    refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
    refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
    dict_jp
    generalize_opaque lkv := @dictLookupVisitedCells
    generalize_opaque kp := @dictKeyPath
    split
    · have hsr := DictWF.setRef
      generalize_opaque sr := @dictSetRefWithCells at hsr
      refine VM.Keeps.bind VM.popCell_spec fun v hv => ?_
      dict_jp
      dict_jp
      refine VM.Keeps.bind VM.cellResolver_spec fun r hr => ?_
      split
      · mvcgen
        dict_close
      · rename_i newRoot? ok created loaded heq
        have hroot := hsr _ _ _ _ _ _ _ _ _ hr hd hv heq
        cases newRoot? <;> mvcgen <;> dict_close
    · have hss := DictWF.setSlice
      generalize_opaque ss := @dictSetSliceWithCells at hss
      refine VM.Keeps.bind VM.popSlice_spec fun v hv => ?_
      dict_jp
      dict_jp
      refine VM.Keeps.bind VM.cellResolver_spec fun r hr => ?_
      split
      · mvcgen
        dict_close
      · rename_i newRoot? ok created loaded heq
        have hroot := hss _ _ _ _ _ _ _ _ _ hr hd hv heq
        cases newRoot? <;> mvcgen <;> dict_close
  · exact hnext

/-- C++ `exec_dict_set` with a builder (`DICTSETB`, `DICTIADDB`, ...): the new root. -/
theorem execInstrDictDictSetB_WF : FamilyWF execInstrDictDictSetB := by
  intro i next hi hnext
  unfold execInstrDictDictSetB
  split
  · refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec 4)) fun _ _ => ?_
    refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
    refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
    dict_jp
    have hsb := DictWF.setBuilder
    generalize_opaque sb := @dictSetBuilderWithCells at hsb
    refine VM.Keeps.bind VM.popBuilder_spec fun v hv => ?_
    dict_jp
    dict_jp
    refine VM.Keeps.bind VM.cellResolver_spec fun r hr => ?_
    split
    · mvcgen
      dict_close
    · rename_i newRoot? ok created loaded heq
      have hroot := hsb _ _ _ _ _ _ _ _ _ hr hd hv heq
      cases newRoot? <;> mvcgen <;> dict_close
  · exact hnext

/-- C++ `exec_dict_set` with a builder (`DICTREPLACEB`, ...): the new root. -/
theorem execInstrDictDictReplaceB_WF : FamilyWF execInstrDictDictReplaceB := by
  intro i next hi hnext
  unfold execInstrDictDictReplaceB
  split
  · refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec 4)) fun _ _ => ?_
    refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
    refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
    dict_jp
    have hsb := DictWF.setBuilder
    generalize_opaque sb := @dictSetBuilderWithCells at hsb
    refine VM.Keeps.bind VM.popBuilder_spec fun v hv => ?_
    dict_jp
    dict_jp
    refine VM.Keeps.bind VM.cellResolver_spec fun r hr => ?_
    split
    · mvcgen
      dict_close
    · rename_i newRoot? ok created loaded heq
      have hroot := hsb _ _ _ _ _ _ _ _ _ hr hd hv heq
      cases newRoot? <;> mvcgen <;> dict_close
  · exact hnext

/-- C++ `exec_dict_getnear` (`DICTGETNEXT`, `DICTIGETPREVEQ`, ...): the value found, and the key
(an integer, or a slice of a new cell no longer than the hint). -/
theorem execInstrDictDictGetNear_WF : FamilyWF execInstrDictDictGetNear := by
  intro i next hi hnext
  unfold execInstrDictDictGetNear
  split
  · refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec 3)) fun _ _ => ?_
    extract_lets -underBinder +onlyGivenNames allowEq goUp intKey unsigned sgnd maxN
    refine VM.Keeps.bind (VM.popNatUpTo_spec _) fun n hn => ?_
    refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
    have hnr := DictWF.nearest
    have hmm := DictWF.minMax
    generalize_opaque nr := @dictNearestWithCells at hnr
    generalize_opaque mm := @dictMinMaxWithCells at hmm
    split
    · -- an integer key: the nearest key, or the minimum or maximum when the key is out of range;
      -- the join point after takes the value found and the cells loaded
      refine VM.Keeps.bind (VM.Keeps.ofWF VM.popIntFinite_spec) fun key _ => ?_
      extract_lets -underBinder +onlyGivenNames jp
      have hjp : ∀ p : Option (Slice × BitString) × Array Cell,
          VM.KeepsWFIf (∀ v k, p.1 = some (v, k) → v.WF) (jp p) := ?jp
      · clear_value jp
        mvcgen
        dict_invariants
        all_goals try exact ExceptConds.entails.refl _
        all_goals (try simp only [SPred.down_pure] at *)
        all_goals first
          | (jp_close (hjp _) <;> wf_cells)
          | dict_leaf
      intro p
      apply VM.KeepsWFIf.of_keeps
      intro hp
      unfold jp
      obtain ⟨out?, loaded0⟩ := p
      generalize_opaque num := IntVal.num
      mvcgen
      dict_close
    · -- a slice key: the key found is pushed as a new cell, no longer than the hint
      mvcgen
      dict_close
  · exact hnext

/-- C++ `exec_dict_getmin` (`DICTMIN`, `DICTIREMMAXREF`, ...): the value found, the root left
after a removal, and the key (an integer, or a slice of a new cell of at most 1023 bits). -/
theorem execInstrDictDictGetMinMax_WF : FamilyWF execInstrDictDictGetMinMax := by
  intro i next hi hnext
  unfold execInstrDictDictGetMinMax
  split
  · refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec 2)) fun _ _ => ?_
    extract_lets -underBinder +onlyGivenNames byRef unsigned intKey fetchMax remove invertFirst maxN
    refine VM.Keeps.bind (VM.popNatUpTo_spec _) fun n hn => ?_
    refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
    dict_jp
    have hmm := DictWF.minMax
    generalize_opaque mm := @dictMinMaxWithCells at hmm
    refine VM.Keeps.bind VM.cellResolver_spec fun r hr => ?_
    split
    · mvcgen
      dict_close
    · mvcgen
      dict_close
    · -- the minimum or maximum found, removed if asked: the join point after the removal takes
      -- the value and the root left
      rename_i val0 keyBits loaded0 hfound
      obtain ⟨hval0, hkey⟩ := hmm _ _ _ _ _ _ hr hd hfound _ _ rfl
      have hkey' : keyBits.size ≤ 1023 := by
        have : maxN ≤ 1023 := by simp only [maxN]; split <;> (try split) <;> omega
        omega
      clear hmm
      extract_lets -underBinder +onlyGivenNames loaded0'
      refine VM.Keeps.bind (DictWF.registerLoads _) fun _ _ => ?_
      extract_lets -underBinder +onlyGivenNames val dictOut? created loaded1 jp
      have hjp : ∀ created dictOut? loaded1 val y, VM.KeepsWFIf
          (val.WF ∧ ∀ c, dictOut? = some c → c.WF) (jp created dictOut? loaded1 val y) := ?jpM
      · clear_value jp
        have hdl := DictWF.delete
        generalize_opaque dl := @dictDeleteWithLoads at hdl
        mvcgen
        dict_invariants
        all_goals try exact ExceptConds.entails.refl _
        all_goals first
          | (jp_close (hjp _ _ _ _ _) <;> wf_cells)
          | dict_leaf
      intro created dictOut? loaded1 val y
      apply VM.KeepsWFIf.of_keeps
      intro ⟨hval, hout⟩
      unfold jp
      refine VM.Keeps.bind (DictWF.registerLoads _) fun _ _ => ?_
      dict_jp
      dict_jp
      dict_jp
      dict_jp
      generalize_opaque num := IntVal.num
      mvcgen
      dict_close
  · exact hnext

/-- The newer operations of `Exec/Dict/Ext.lean`, one bullet each: C++ `exec_load_dict_slice`
(`LDDICTS`), `exec_dict_setget` and `exec_dict_deleteget`, the same with a builder,
`exec_dict_delete`, `exec_dict_get_optref`, `exec_dict_setget_optref`, `exec_subdict_get`,
`exec_pfx_dict_set`, `exec_pfx_dict_delete`, `exec_pfx_dict_get`, `exec_const_pfx_dict_switch`.
-/
theorem execInstrDictExt_WF : FamilyWF execInstrDictExt := by
  intro i next hi hnext
  unfold execInstrDictExt
  split
  · rename_i op
    split
    · -- LDDICTS
      mvcgen
      dict_close
    · -- DICT{I,U}{SET,REPLACE,ADD,DEL}GET{REF}
      refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec _)) fun _ _ => ?_
      refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
      refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
      extract_lets -underBinder +onlyGivenNames jp
      have hjp : ∀ k, VM.KeepsWFIf True (jp k) := ?jp
      · clear_value jp
        split
        · split
          · extract_lets -underBinder +onlyGivenNames jpIdx
            have hjpIdx : ∀ idx, VM.KeepsWFIf True (jpIdx idx) := ?jpIdx
            · clear_value jpIdx
              mvcgen
              all_goals first
                | (jp_close (hjpIdx _) <;> trivial)
                | wf_cells
            intro idx
            apply VM.KeepsWFIf.of_keeps
            intro _
            unfold jpIdx
            mvcgen
            all_goals first
              | (jp_close (hjp _) <;> trivial)
              | wf_cells
          · mvcgen
            all_goals first
              | (jp_close (hjp _) <;> trivial)
              | wf_cells
        · mvcgen
          all_goals first
            | (jp_close (hjp _) <;> trivial)
            | wf_cells
      intro k
      apply VM.KeepsWFIf.of_keeps
      intro _
      unfold jp
      have hdl := DictWF.delete
      have hlsr := DictWF.lookupSetRef
      have hlss := DictWF.lookupSetSlice
      generalize_opaque dl := @dictDeleteWithLoads at hdl
      generalize_opaque lsr := @dictLookupSetRefWithCells at hlsr
      generalize_opaque lss := @dictLookupSetSliceWithCells at hlss
      mvcgen
      dict_close
    · -- DICT{I,U}{SET,REPLACE,ADD}GETB
      refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec _)) fun _ _ => ?_
      refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
      refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
      dict_jp
      have hlsb := DictWF.lookupSetBuilder
      generalize_opaque lsb := @dictLookupSetBuilderWithCells at hlsb
      mvcgen
      dict_close
    · -- DICT{I,U}DEL
      refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec _)) fun _ _ => ?_
      refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
      refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
      dict_jp
      have hdl := DictWF.delete
      generalize_opaque dl := @dictDeleteWithLoads at hdl
      mvcgen
      dict_close
    · -- DICT{I,U}GETOPTREF
      refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec _)) fun _ _ => ?_
      refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
      refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
      dict_jp
      have hlk := DictWF.lookup
      generalize_opaque lk := @dictLookupWithCells at hlk
      generalize_opaque lkv := @dictLookupVisitedCells
      mvcgen
      dict_close
    · -- DICT{I,U}SETGETOPTREF
      refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec _)) fun _ _ => ?_
      refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
      refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
      dict_jp
      have hdl := DictWF.delete
      have hlsr := DictWF.lookupSetRef
      generalize_opaque dl := @dictDeleteWithLoads at hdl
      generalize_opaque lsr := @dictLookupSetRefWithCells at hlsr
      mvcgen
      dict_close
    · -- SUBDICT{I,U}{RP}GET
      refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec _)) fun _ _ => ?_
      refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
      refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
      extract_lets -underBinder +onlyGivenNames mk
      refine VM.Keeps.bind (VM.popNatUpTo_spec _) fun k hk => ?_
      dict_jp
      have hsub := DictWF.subdict
      generalize_opaque sub := @dictExtractPrefixSubdictWithCells at hsub
      generalize_opaque pv := @DictExt.dictExtractPrefixVisited
      mvcgen
      dict_close
    · -- PFXDICTSET, PFXDICTREPLACE, PFXDICTADD
      have hpst := DictWF.pfxSetSlice
      generalize_opaque pst := (private% TvmLean.Semantics.Exec.Dict.Ext
        TvmLean.DictExt.pfxSetGenAuxWithCells) at hpst
      generalize_opaque kp := @pfxDictKeyPath
      mvcgen
      dict_close
    · -- PFXDICTDEL
      have hpdl := DictWF.pfxDelete
      generalize_opaque pdl := (private% TvmLean.Semantics.Exec.Dict.Ext
        TvmLean.DictExt.pfxLookupDeleteWithCells) at hpdl
      mvcgen
      dict_close
    · -- PFXDICTGET{Q,JMP,EXEC}
      have hplk := DictWF.pfxLookup
      have hspf := DictWF.slicePrefix
      generalize_opaque plk := (private% TvmLean.Semantics.Exec.Dict.Ext
        TvmLean.DictExt.pfxLookupPrefixWithCells) at hplk
      generalize_opaque spf := (private% TvmLean.Semantics.Exec.Dict.Ext
        TvmLean.DictExt.slicePrefix) at hspf
      refine VM.Keeps.bind (VM.Keeps.ofWF (VM.checkUnderflow_spec _)) fun _ _ => ?_
      refine VM.Keeps.bind (VM.popNatUpTo_spec 1023) fun n hn => ?_
      refine VM.Keeps.bind VM.popMaybeCell_spec fun d hd => ?_
      refine VM.Keeps.bind VM.popSlice_spec fun cs0 hcs0 => ?_
      refine VM.Keeps.bind (VM.Keeps.ofWF (DictExt.prechargeRootLoad_spec _)) fun _ _ => ?_
      extract_lets -underBinder +onlyGivenNames keyBits
      refine VM.Keeps.bind VM.cellResolver_spec fun r hr => ?_
      split
      · mvcgen
        dict_close
      · mvcgen
        dict_close
      · -- the prefix found: the value, the prefix and the rest of the key, pushed or jumped to
        rename_i valueSlice pfxLen loaded0 hfound
        have hv : valueSlice.WF := hplk _ _ _ _ _ _ hr hd hfound _ rfl
        extract_lets -underBinder +onlyGivenNames loaded
        refine VM.Keeps.bind (VM.Keeps.ofWF (DictExt.registerLoaded_spec _)) fun _ _ => ?_
        extract_lets -underBinder +onlyGivenNames jp
        have hjp : ∀ p : Slice × Slice, VM.KeepsWFIf (p.1.WF ∧ p.2.WF) (jp p) := ?jpGet
        · clear_value jp
          split
          · next x heq =>
            exact VM.Keeps.bind (Q := fun y : Slice × Slice => y.1.WF ∧ y.2.WF)
              (VM.Keeps.pure' (hspf _ _ _ _ hcs0 heq)) fun y hy => (hjp y).keeps hy
          · keeps_leaf hjp
        intro p
        apply VM.KeepsWFIf.of_keeps
        intro hp
        unfold jp
        obtain ⟨pfxSlice, cs1⟩ := p
        mvcgen
        dict_close
    · -- PFXDICTSWITCH
      have hplk := DictWF.pfxLookup
      have hspf := DictWF.slicePrefix
      generalize_opaque plk := (private% TvmLean.Semantics.Exec.Dict.Ext
        TvmLean.DictExt.pfxLookupPrefixWithCells) at hplk
      generalize_opaque spf := (private% TvmLean.Semantics.Exec.Dict.Ext
        TvmLean.DictExt.slicePrefix) at hspf
      simp only [Instr.WF] at hi
      refine VM.Keeps.bind VM.popSlice_spec fun cs0 hcs0 => ?_
      refine VM.Keeps.bind (VM.Keeps.ofWF (VM.registerCellLoad_spec _)) fun _ _ => ?_
      extract_lets -underBinder +onlyGivenNames keyBits
      refine VM.Keeps.bind VM.cellResolver_spec fun r hr => ?_
      split
      · mvcgen
        dict_close
      · mvcgen
        dict_close
      · -- the prefix found: the prefix and the rest of the key pushed, a jump to the value
        rename_i valueSlice pfxLen loaded0 hfound
        have hv : valueSlice.WF := hplk _ _ _ _ _ _ hr (by simpa using hi) hfound _ rfl
        extract_lets -underBinder +onlyGivenNames loaded
        refine VM.Keeps.bind (VM.Keeps.ofWF (DictExt.registerLoaded_spec _)) fun _ _ => ?_
        extract_lets -underBinder +onlyGivenNames jp
        have hjp : ∀ p : Slice × Slice, VM.KeepsWFIf (p.1.WF ∧ p.2.WF) (jp p) := ?jpSwitch
        · clear_value jp
          split
          · next x heq =>
            exact VM.Keeps.bind (Q := fun y : Slice × Slice => y.1.WF ∧ y.2.WF)
              (VM.Keeps.pure' (hspf _ _ _ _ hcs0 heq)) fun y hy => (hjp y).keeps hy
          · keeps_leaf hjp
        intro p
        apply VM.KeepsWFIf.of_keeps
        intro hp
        unfold jp
        obtain ⟨pfxSlice, cs1⟩ := p
        mvcgen
        dict_close
  · exact hnext

/-- The Dict family keeps states well-formed. -/
theorem execInstrDict_WF : FamilyWF execInstrDict := by
  intro i next hi hnext
  unfold execInstrDict
  exact execInstrDictStdict_WF i _ hi <|
    execInstrDictSkipdict_WF i _ hi <|
    execInstrDictDictPushConst_WF i _ hi <|
    execInstrDictDictGet_WF i _ hi <|
    execInstrDictDictGetNear_WF i _ hi <|
    execInstrDictDictGetMinMax_WF i _ hi <|
    execInstrDictDictSet_WF i _ hi <|
    execInstrDictDictSetB_WF i _ hi <|
    execInstrDictDictReplaceB_WF i _ hi <|
    execInstrDictDictGetExec_WF i _ hi <|
    execInstrDictExt_WF i _ hi <|
    execInstrDictLddict_WF i _ hi <|
    hnext

end TvmLean

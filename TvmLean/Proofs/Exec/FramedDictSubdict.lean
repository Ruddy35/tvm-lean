import TvmLean.Proofs.Exec.FramedDictPfx

/-!
# `SUBDICT{,I,U}{,RP}GET` on any dictionary, framed

The subdictionary of the keys with a given prefix, in a dictionary whose cells a run does not know,
is framed (`TvmLean.Framed.ExecFramed`, `TvmLean/Proofs/Exec/Framed.lean`): the instruction changes
the stack, the gas, the loaded cells and libraries only; it pushes the new root (null or a cell); it
fails only with an exception of code 2 or more.

* `dictExtractPrefixSubdictWithCells_err`: the extraction of the model fails only with cell_und,
  dict_err, cell_ov or fatal (by induction on the length of the prefix left);
* `DictTail.subdictGet`: the handler (TvmLean/Semantics/Exec/Dict/Ext.lean), the same code
  (`DictTail.subdictGetHandler_eq`);
* `Framed.subdictGet_framed`, tactic `vm_subdict_get_any`.
-/

namespace TvmLean.Framed

open TvmLean

/-! ## Errors of the extraction -/

/-- The extraction below a node fails only with an exception of code 2 or more. -/
theorem dictExtractPrefixGo_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r) (keyBits : Nat)
    (pfx : BitString) (prefixLen : Nat) (removePrefix : Bool) (rootCell : Cell) (k : Nat) :
    ∀ (cell : Cell) (m : Nat) (loaded : Array Cell), prefixLen - m = k →
      ErrReal (dictExtractPrefixGo keyBits pfx prefixLen removePrefix rootCell cell m loaded r) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro cell m loaded hk
    rw [dictExtractPrefixGo]
    repeat' (first
      | exact ErrReal.ok _ | exact ErrReal.pure _
      | exact ErrReal.throw (by decide)
      | exact ErrDict.real (parseDictLabel_err _ _ r hr)
      | exact ErrDict.real (dictValidateNodeExt_err _ _)
      | exact builderStoreBitsChecked_real _ _ | exact builderAppendCellChecked_real _ _
      | exact ih _ (by omega) _ _ _ rfl
      | (refine ErrReal.bind ?_ (fun _ => ?_)) | (refine ErrReal.dite (fun _ => ?_) (fun _ => ?_))
      | (refine ErrReal.ite ?_ ?_) | split | (dsimp only))

/-- **The extraction of a subdictionary fails only with an exception of code 2 or more.** -/
theorem dictExtractPrefixSubdictWithCells_err (r : Cell → Except Excno Cell) (hr : ResolverCellUnd r)
    (root : Option Cell) (keyBits : Nat) (pfx : BitString) (prefixLen : Nat) (removePrefix : Bool) :
    ErrReal (dictExtractPrefixSubdictWithCells root keyBits pfx prefixLen removePrefix r) := by
  unfold dictExtractPrefixSubdictWithCells
  repeat' (first
    | exact ErrReal.ok _ | exact ErrReal.pure _
    | exact ErrReal.throw (by decide)
    | exact dictExtractPrefixGo_err r hr _ _ _ _ _ _ _ _ _ rfl
    | (refine ErrReal.bind ?_ (fun _ => ?_)) | (refine ErrReal.ite ?_ ?_) | split | (dsimp only))

theorem dictExtractPrefixSubdictWithCells_real {root : Option Cell} {keyBits : Nat} {pfx : BitString}
    {prefixLen : Nat} {removePrefix : Bool} {libs : Array Cell} {gv : Nat} {refused : Array BitString} {e : Excno}
    (h : dictExtractPrefixSubdictWithCells root keyBits pfx prefixLen removePrefix
      (fun c => (libraryResolveLoads libs gv c refused).2) = .error e) : 2 ≤ e.toInt :=
  dictExtractPrefixSubdictWithCells_err _ (resolverCellUnd_library _ _ _) _ _ _ _ _ e h

macro_rules
  | `(tactic| steps_err) => `(tactic| exact dictExtractPrefixSubdictWithCells_real (by assumption))

/-- `OptRefOk` (the new root, null or a cell) of the stack under the four arguments of
`SUBDICT*GET` (the prefix, its length, the dictionary, the key length). -/
abbrev OptRefOk4 (s s' : Stack) : Prop :=
  ∃ (s0 : Stack) (a b c d : Value), s = (((s0.push a).push b).push c).push d ∧ OptRefOk s0 s'

end TvmLean.Framed

namespace DictTail

open TvmLean

/-- The handler of `SUBDICT{,I,U}{,RP}GET` (`execInstrDictExt`): the same code. -/
def subdictGet (intKey unsigned rp : Bool) : VM Unit := do
  VM.checkUnderflow 4
  let n ← VM.popNatUpTo 1023
  let dictCell? ← VM.popMaybeCell
  let mk : Nat := if intKey then (if unsigned then 256 else 257) else 1023
  let k ← VM.popNatUpTo (Nat.min mk n)
  let prefixBits : BitString ←
    if intKey then
      let idx ← VM.popIntFinite
      match dictKeyBits? idx k unsigned with
      | some bs => pure bs
      | none => throw .cellUnd
  else
    let keySlice ← VM.popSlice
    if keySlice.haveBits k then
      pure (keySlice.readBits k)
    else
      throw .cellUnd
  if k > 0 then
    extPrechargeRootLoad dictCell?
  match dictExtractPrefixSubdictWithCells (resolve := (← VM.cellResolver)) dictCell? n prefixBits k rp with
  | .error e =>
      match dictCell? with
      | some root =>
          if k > 0 && k ≤ n then
            extRegisterLoaded (extLoadedWithoutRoot dictCell?
              (DictExt.dictExtractPrefixVisited (resolve := (← VM.cellResolver)) n prefixBits k root 0))
      | none => pure ()
      throw e
  | .ok (newRoot?, _changed, created, loaded) =>
      let loaded :=
        if k > 0 then
          extLoadedWithoutRoot dictCell? loaded
        else
          loaded
      extRegisterLoaded loaded
      extConsumeCreatedGas created
      extPushDictRoot newRoot?

end DictTail

namespace TvmLean

set_option maxHeartbeats 1000000 in
/-- `SUBDICT{,I,U}{,RP}GET` runs as `DictTail.subdictGet` (the same code). -/
theorem DictTail.subdictGetHandler_eq (intKey unsigned rp : Bool) (st : VmState) :
    ExceptT.run (execInstr (.dictExt (.subdictGet intKey unsigned rp))) st =
      ExceptT.run (DictTail.subdictGet intKey unsigned rp) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

end TvmLean

namespace TvmLean.Framed

open TvmLean

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`SUBDICT{,I,U}{,RP}GET` on any stack is framed**: the stack under its four arguments
`OptRefOk`. -/
theorem Steps.subdictGet (intKey unsigned rp : Bool) :
    Steps (DictTail.subdictGet intKey unsigned rp) (fun _ s s' => OptRefOk4 s s') := by
  unfold DictTail.subdictGet DictTail.extPushDictRoot
  simp only [VM.cellResolver, bind_assoc, pure_bind]
  cases intKey <;> (try simp only [Bool.false_eq_true, if_true, if_false]) <;> steps_auto

/-- **`SUBDICT{,I,U}{,RP}GET` on any dictionary is framed**: from a stack `s a b c d`, `OptRefOk s`,
or an exception of code 2 or more. -/
theorem subdictGet_framed (intKey unsigned rp : Bool) (s : Stack) (a b c d : Value) (st : VmState)
    (hs : st.stack = (((s.push a).push b).push c).push d) :
    ExecFramed (.dictExt (.subdictGet intKey unsigned rp)) (OptRefOk s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.subdictGet intKey unsigned rp st
  rw [← DictTail.subdictGetHandler_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, a', b', c', d', e, hok⟩ := h2 () h
  rw [hs] at e
  rw [push4_inj e]
  exact hok

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_subdict_get_any`: the run in the goal is about to run `SUBDICT{,I,U}{,RP}GET` on a
dictionary it does not know: by `Framed.runWith_framed4` and `Framed.subdictGet_framed`, two goals:
`P` of a result that commits nothing, and `P` of the runs from the state after it with a stack
`Framed.OptRefOk s`, any gas, loaded cells and libraries. -/
elab "vm_subdict_get_any" : tactic =>
  Exec.framedAny "vm_subdict_get_any" 4 ``DictExtInstr.subdictGet 3 ``Framed.subdictGet_framed

end TvmLean

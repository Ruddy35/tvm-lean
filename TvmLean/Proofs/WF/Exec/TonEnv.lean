import TvmLean.Proofs.WF.Cells

/-!
# The TonEnv family keeps states well-formed

`execInstrTonEnv_WF : FamilyWF execInstrTonEnv`, one theorem per handler of
`TvmLean/Semantics/Exec/TonEnv/` (35, the pattern of `Step.lean`). The instructions read the
parameters in `c7`, set globals (`tupleExtendSetIndex_WF`), commit (`VmState.WF.tryCommit`), parse
and store message addresses and grams, and look up the configuration dictionary and the extra
currencies (`dictLookupWithCells_WF` of `Cells.lean`). Three things `mvcgen` must not see:

* the integers they push: `VM.pushIntQuiet (.num (Int.ofNat n))` makes `mvcgen` (when it compares
  the postcondition of the step before with the code after) and the kernel compare `n` with
  `2 ^ 256` by unfolding `Nat.ble` (`maximum recursion depth`, `(kernel) deep recursion detected`):
  `IntVal.num` is generalized first (`generalize_opaque`, `Cells.lean`);
* the dictionary lookups (`dictLookupWithCells`, `dictLookupVisitedCells`, `whnf` timeouts) and
  the hashes (`sha256Digest` of `SETRAND`, `Cell.hashBytes` of `VM.registerCellLoadCheap`): they
  are generalized, the lookup with its specification (`dictLookupWithCells_WF'`);
* a `match` on a value bound by `let x ← pure e` (the join points of `let x ← match ... with ... =>
  pure ...`): `mvcgen` simplifies the discriminant and then splits on a proof in place of the program
  (an unsolved `wp⟦Eq.mpr ...⟧`, `(kernel) application type mismatch`): `simp only [pure_bind]`
  first (`SETRAND`, `GETEXTRABALANCE`, `REWRITESTDADDR`); the parses of `PARSEMSGADDR` and
  `REWRITEVARADDR` (`Except` values) get a specification of their own.
-/

open Std.Do

set_option mvcgen.warning false
set_option maxHeartbeats 4000000

namespace TvmLean

/-- Assigns the invariant `VmState.WF` to every loop `mvcgen` left (the twelve copies of the
loops over the cells a lookup loaded in `GETEXTRABALANCE`), after `mvcgen` and before the
conditions are closed. -/
macro "wf_invariants" : tactic =>
  `(tactic| all_goals try exact post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩)

/-- `dictLookupWithCells_WF` in the form `generalize_opaque` takes. -/
theorem dictLookupWithCells_WF' : ∀ root key r s cells, ResolverWF r →
    (∀ c, root = some c → c.WF) → dictLookupWithCells root key r = .ok (some s, cells) → s.WF :=
  fun _ _ _ _ _ hr hroot h => dictLookupWithCells_WF hr hroot h

theorem VM.get_spec' (P : VmState → Prop) :
    ⦃fun st => ⌜P st⌝⦄ (get : VM VmState)
      ⦃post⟨fun r st => ⌜P st ∧ r = st⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen

/-- C++ `LocalVmState` of `GETEXTRABALANCE`: a cheap cell load keeps the state well-formed. -/
theorem VM.registerCellLoadCheap_spec (c : Cell) (remaining : Int) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.registerCellLoadCheap c remaining
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  unfold VM.registerCellLoadCheap
  generalize_opaque hb := Cell.hashBytes
  mvcgen invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_cells

/-- C++ `skip_std_message_addr` (version 12): the rest of a well-formed slice is well-formed. -/
theorem Slice.skipStdMessageAddr_WF {s s' : Slice} (hs : s.WF)
    (h : s.skipStdMessageAddr = .ok s') : s'.WF := by
  refine Except.of_triple (P := Slice.WF) ?_ h
  mvcgen [Slice.skipStdMessageAddr, Slice.takeBitsAsNatCellUnd_wfspec]
  all_goals wf_cells

theorem Slice.parseMessageAddr_spec (s : Slice) (gv : Nat) (hs : s.WF) :
    ⦃⌜True⌝⦄ s.parseMessageAddr gv
      ⦃post⟨fun r => ⌜(∀ v ∈ r.1, v.WF) ∧ r.2.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
  Except.triple_of fun r h => Slice.parseMessageAddr_WF hs (t := r.1) (s' := r.2) h

/-- C++ `do_rewrite_addr`: the address with the anycast prefix in place of its first bits is a
well-formed slice (a new cell of at most the bits of the address). -/
theorem rewriteMessageAddr_WF {addr : Slice} (ha : addr.WF) {pfx : Value} (hp : pfx.WF)
    {r : Slice × Bool} (h : rewriteMessageAddr addr pfx = .ok r) : r.1.WF := by
  unfold rewriteMessageAddr at h
  split at h
  · cases h; exact ha
  · simp only [Value.wf_slice] at hp
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h; exact ha
    · split at h
      · cases h
      · split at h
        · cases h; exact hp
        · cases h
          refine Slice.ofCell_WF (Cell.mkOrdinary_WF ?_ (by simp) (by simp))
          have := ha.1.bits_le
          have := ha.2.1
          have := hp.2.1
          simp only [Slice.bitsRemaining] at *
          simp only [Slice.readBits, Array.size_append, Array.size_extract]
          omega
  · cases h

theorem rewriteMessageAddr_spec (addr : Slice) (pfx : Value) (ha : addr.WF) (hp : pfx.WF) :
    ⦃⌜True⌝⦄ rewriteMessageAddr addr pfx ⦃post⟨fun r => ⌜r.1.WF⌝, fun _ => ⌜True⌝⟩⦄ :=
  Except.triple_of fun _ h => rewriteMessageAddr_WF ha hp h

/-! ## The handlers -/

theorem execInstrTonEnvBalance_WF : FamilyWF execInstrTonEnvBalance := by
  intro i next hi hnext
  unfold execInstrTonEnvBalance
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvNow_WF : FamilyWF execInstrTonEnvNow := by
  intro i next hi hnext
  unfold execInstrTonEnvNow
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGetParamAliases_WF : FamilyWF execInstrTonEnvGetParamAliases := by
  intro i next hi hnext
  unfold execInstrTonEnvGetParamAliases
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGetParam_WF : FamilyWF execInstrTonEnvGetParam := by
  intro i next hi hnext
  unfold execInstrTonEnvGetParam
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvConfigDict_WF : FamilyWF execInstrTonEnvConfigDict := by
  intro i next hi hnext
  unfold execInstrTonEnvConfigDict
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvConfigParam_WF : FamilyWF execInstrTonEnvConfigParam := by
  intro i next hi hnext
  unfold execInstrTonEnvConfigParam
  have hlk := dictLookupWithCells_WF'
  generalize_opaque lk := @dictLookupWithCells at hlk
  generalize_opaque lkv := @dictLookupVisitedCells
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_cells

theorem execInstrTonEnvPrevBlocksInfo_WF : FamilyWF execInstrTonEnvPrevBlocksInfo := by
  intro i next hi hnext
  unfold execInstrTonEnvPrevBlocksInfo
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGetPrecompiledGas_WF : FamilyWF execInstrTonEnvGetPrecompiledGas := by
  intro i next hi hnext
  unfold execInstrTonEnvGetPrecompiledGas
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvRandu256_WF : FamilyWF execInstrTonEnvRandu256 := by
  intro i next hi hnext
  unfold execInstrTonEnvRandu256
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvRand_WF : FamilyWF execInstrTonEnvRand := by
  intro i next hi hnext
  unfold execInstrTonEnvRand
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvSetRand_WF : FamilyWF execInstrTonEnvSetRand := by
  intro i next hi hnext
  unfold execInstrTonEnvSetRand
  generalize_opaque sha := sha256Digest
  generalize_opaque num := IntVal.num
  simp only [pure_bind]
  mvcgen [hnext]
  all_goals wf_cells [tupleExtendSetIndex_WF]

theorem execInstrTonEnvGetExtraBalance_WF : FamilyWF execInstrTonEnvGetExtraBalance := by
  intro i next hi hnext
  unfold execInstrTonEnvGetExtraBalance
  have hlk := dictLookupWithCells_WF'
  generalize_opaque lk := @dictLookupWithCells at hlk
  generalize_opaque lkv := @dictLookupVisitedCells
  generalize_opaque num := IntVal.num
  simp only [pure_bind]
  mvcgen [hnext, VM.pushC7Param, VM.registerCellLoadCheap_spec]
  wf_invariants
  all_goals try exact ExceptConds.entails.refl _
  all_goals wf_cells

theorem execInstrTonEnvGetGlobVar_WF : FamilyWF execInstrTonEnvGetGlobVar := by
  intro i next hi hnext
  unfold execInstrTonEnvGetGlobVar
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGetGlob_WF : FamilyWF execInstrTonEnvGetGlob := by
  intro i next hi hnext
  unfold execInstrTonEnvGetGlob
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvSetGlobVar_WF : FamilyWF execInstrTonEnvSetGlobVar := by
  intro i next hi hnext
  mvcgen [execInstrTonEnvSetGlobVar, hnext]
  all_goals wf_cells [tupleExtendSetIndex_WF]

theorem execInstrTonEnvSetGlob_WF : FamilyWF execInstrTonEnvSetGlob := by
  intro i next hi hnext
  mvcgen [execInstrTonEnvSetGlob, hnext]
  all_goals wf_cells [tupleExtendSetIndex_WF]

theorem execInstrTonEnvAccept_WF : FamilyWF execInstrTonEnvAccept := by
  intro i next hi hnext
  unfold execInstrTonEnvAccept
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvSetGasLimit_WF : FamilyWF execInstrTonEnvSetGasLimit := by
  intro i next hi hnext
  unfold execInstrTonEnvSetGasLimit
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGasConsumed_WF : FamilyWF execInstrTonEnvGasConsumed := by
  intro i next hi hnext
  unfold execInstrTonEnvGasConsumed
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvCommit_WF : FamilyWF execInstrTonEnvCommit := by
  intro i next hi hnext
  mvcgen [execInstrTonEnvCommit, hnext]
  all_goals first | (apply VmState.WF.tryCommit; assumption) | wf_cells

theorem execInstrTonEnvLdGrams_WF : FamilyWF execInstrTonEnvLdGrams := by
  intro i next hi hnext
  unfold execInstrTonEnvLdGrams
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvStGrams_WF : FamilyWF execInstrTonEnvStGrams := by
  intro i next hi hnext
  unfold execInstrTonEnvStGrams
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvLdMsgAddr_WF : FamilyWF execInstrTonEnvLdMsgAddr := by
  intro i next hi hnext
  mvcgen [execInstrTonEnvLdMsgAddr, hnext]
  all_goals wf_cells [→ Slice.skipMessageAddr_WF]

theorem execInstrTonEnvParseMsgAddr_WF : FamilyWF execInstrTonEnvParseMsgAddr := by
  intro i next hi hnext
  unfold execInstrTonEnvParseMsgAddr
  split
  · -- the parse (an `Except` value) gets a specification of its own
    refine Triple.bind _ _ VM.popSlice_spec fun csr0 => ?_
    refine Triple.bind _ _ (VM.get_spec' fun st => st.WF ∧ csr0.WF) fun st0 => ?_
    extract_lets gv parsed
    have hp : csr0.WF → ∀ t, parsed = .ok t → ∀ v ∈ t, v.WF := by
      intro hc t h
      refine Except.of_triple (P := fun t : Array Value => ∀ v ∈ t, v.WF) ?_ h
      simp only [parsed]
      mvcgen [Slice.parseMessageAddr_spec]
      all_goals wf_cells
    clear_value parsed
    mvcgen [hnext]
    all_goals wf_cells
  · exact hnext

theorem execInstrTonEnvRewriteStdAddr_WF : FamilyWF execInstrTonEnvRewriteStdAddr := by
  intro i next hi hnext
  unfold execInstrTonEnvRewriteStdAddr
  generalize_opaque num := IntVal.num
  simp only [pure_bind]
  mvcgen [hnext]
  all_goals wf_cells

theorem execInstrTonEnvRewriteVarAddr_WF : FamilyWF execInstrTonEnvRewriteVarAddr := by
  intro i next hi hnext
  unfold execInstrTonEnvRewriteVarAddr
  split
  · -- as for `PARSEMSGADDR`
    refine Triple.bind _ _ VM.popSlice_spec fun csr0 => ?_
    refine Triple.bind _ _ (VM.get_spec' fun st => st.WF ∧ csr0.WF) fun st0 => ?_
    extract_lets gv parsed
    have hp : csr0.WF → ∀ r, parsed = .ok r → r.2.1.WF := by
      intro hc r h
      refine Except.of_triple (P := fun r : Int × Slice × Bool => r.2.1.WF) ?_ h
      simp only [parsed]
      mvcgen [Slice.parseMessageAddr_spec, rewriteMessageAddr_spec]
      all_goals wf_cells
    clear_value parsed
    mvcgen [hnext]
    all_goals wf_cells
  · exact hnext

theorem execInstrTonEnvStdAddr_WF : FamilyWF execInstrTonEnvStdAddr := by
  intro i next hi hnext
  mvcgen [execInstrTonEnvStdAddr, hnext]
  all_goals wf_cells [→ Slice.skipStdMessageAddr_WF]

theorem execInstrTonEnvGlobalId_WF : FamilyWF execInstrTonEnvGlobalId := by
  intro i next hi hnext
  unfold execInstrTonEnvGlobalId
  have hlk := dictLookupWithCells_WF'
  generalize_opaque lk := @dictLookupWithCells at hlk
  generalize_opaque lkv := @dictLookupVisitedCells
  mvcgen [hnext, VM.pushC7Param] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_cells

theorem execInstrTonEnvGetGasFee_WF : FamilyWF execInstrTonEnvGetGasFee := by
  intro i next hi hnext
  unfold execInstrTonEnvGetGasFee
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGetStorageFee_WF : FamilyWF execInstrTonEnvGetStorageFee := by
  intro i next hi hnext
  unfold execInstrTonEnvGetStorageFee
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGetForwardFee_WF : FamilyWF execInstrTonEnvGetForwardFee := by
  intro i next hi hnext
  unfold execInstrTonEnvGetForwardFee
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGetOriginalFwdFee_WF : FamilyWF execInstrTonEnvGetOriginalFwdFee := by
  intro i next hi hnext
  unfold execInstrTonEnvGetOriginalFwdFee
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGetGasFeeSimple_WF : FamilyWF execInstrTonEnvGetGasFeeSimple := by
  intro i next hi hnext
  unfold execInstrTonEnvGetGasFeeSimple
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvGetForwardFeeSimple_WF : FamilyWF execInstrTonEnvGetForwardFeeSimple := by
  intro i next hi hnext
  unfold execInstrTonEnvGetForwardFeeSimple
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnvInMsgParam_WF : FamilyWF execInstrTonEnvInMsgParam := by
  intro i next hi hnext
  unfold execInstrTonEnvInMsgParam
  generalize_opaque num := IntVal.num
  mvcgen [hnext, VM.pushC7Param, VM.pushPrevBlocksInfo]
  all_goals wf_cells

theorem execInstrTonEnv_WF : FamilyWF execInstrTonEnv := by
  intro i next hi hnext
  unfold execInstrTonEnv
  exact execInstrTonEnvBalance_WF i _ hi <|
    execInstrTonEnvNow_WF i _ hi <|
    execInstrTonEnvGetParamAliases_WF i _ hi <|
    execInstrTonEnvGetParam_WF i _ hi <|
    execInstrTonEnvConfigDict_WF i _ hi <|
    execInstrTonEnvConfigParam_WF i _ hi <|
    execInstrTonEnvPrevBlocksInfo_WF i _ hi <|
    execInstrTonEnvGetPrecompiledGas_WF i _ hi <|
    execInstrTonEnvRandu256_WF i _ hi <|
    execInstrTonEnvRand_WF i _ hi <|
    execInstrTonEnvSetRand_WF i _ hi <|
    execInstrTonEnvGetExtraBalance_WF i _ hi <|
    execInstrTonEnvGetGlobVar_WF i _ hi <|
    execInstrTonEnvGetGlob_WF i _ hi <|
    execInstrTonEnvSetGlobVar_WF i _ hi <|
    execInstrTonEnvSetGlob_WF i _ hi <|
    execInstrTonEnvAccept_WF i _ hi <|
    execInstrTonEnvSetGasLimit_WF i _ hi <|
    execInstrTonEnvGasConsumed_WF i _ hi <|
    execInstrTonEnvCommit_WF i _ hi <|
    execInstrTonEnvLdGrams_WF i _ hi <|
    execInstrTonEnvStGrams_WF i _ hi <|
    execInstrTonEnvLdMsgAddr_WF i _ hi <|
    execInstrTonEnvParseMsgAddr_WF i _ hi <|
    execInstrTonEnvRewriteStdAddr_WF i _ hi <|
    execInstrTonEnvRewriteVarAddr_WF i _ hi <|
    execInstrTonEnvStdAddr_WF i _ hi <|
    execInstrTonEnvGlobalId_WF i _ hi <|
    execInstrTonEnvGetGasFee_WF i _ hi <|
    execInstrTonEnvGetStorageFee_WF i _ hi <|
    execInstrTonEnvGetForwardFee_WF i _ hi <|
    execInstrTonEnvGetOriginalFwdFee_WF i _ hi <|
    execInstrTonEnvGetGasFeeSimple_WF i _ hi <|
    execInstrTonEnvGetForwardFeeSimple_WF i _ hi <|
    execInstrTonEnvInMsgParam_WF i _ hi <|
    hnext

end TvmLean

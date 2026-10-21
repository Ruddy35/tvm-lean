import TvmLean.Proofs.WF.Cells

/-!
# The Crypto family keeps states well-formed

`execInstrCrypto_WF : FamilyWF execInstrCrypto`, one theorem per handler of
`TvmLean/Semantics/Exec/Crypto/` (7: the hashes `HASHCU`, `HASHSU`, `SHA256U`, `HASHEXT`, the
signatures `CHKSIGNU`, `CHKSIGNS`, and `execInstrCryptoExt`: secp256k1, P-256, Ristretto255,
BLS12-381). The instructions push integers, booleans, tuples of integers and slices of new cells
built from bytes; none of their results needs the hash or the curve operation computed:

* every hash, signature check and curve operation is generalized before `mvcgen` sees it
  (`generalize_opaque`, `Cells.lean`), with `IntVal.num` (an integer pushed by
  `VM.pushIntQuiet`, see `Exec/TonEnv.lean`);
* the BLS12-381 operations that return points keep, as a hypothesis, that a point is a 48-byte
  (G1) or a 96-byte (G2) encoding (`Bls12381.g1Add_size`, ..., `Bls12381.aggregate_size`, from
  `compressG1_size`, `compressG2_size`), so that its slice (`sliceOfByteArray`) is a well-formed
  cell of at most 768 bits (`sliceOfByteArray_WF`);
* `HASHEXTA` stores the digest bits in a builder after checking `canExtendBy (digest.size * 8)`:
  the invariant of the loop building them says they are 8 bits a byte; `HASHEXT` of a digest
  longer than 32 bytes pushes a tuple of integers (`hashExtChunks_WF`).
-/

open Std.Do

set_option mvcgen.warning false
set_option maxHeartbeats 4000000

namespace TvmLean

namespace Bls12381

theorem infEncoding_size {n : Nat} (h : 0 < n) : (infEncoding n).size = n := by
  simp [infEncoding]; omega

theorem compressG1_size (q : Jac Nat) : (compressG1 q).size = 48 := by
  unfold compressG1
  split
  · exact infEncoding_size (by decide)
  · simp [natToBE]

theorem compressG2_size (q : Jac Fp2) : (compressG2 q).size = 96 := by
  unfold compressG2
  split
  · exact infEncoding_size (by decide)
  · simp [natToBE]

theorem g1ZeroBytes_size : g1ZeroBytes.size = 48 := infEncoding_size (by decide)
theorem g2ZeroBytes_size : g2ZeroBytes.size = 96 := infEncoding_size (by decide)

/-- The points the G1 operations return are 48-byte encodings. -/
def G1Out (f : Option (Array UInt8)) : Prop := ∀ out, f = some out → out.size = 48
/-- The points the G2 operations return are 96-byte encodings. -/
def G2Out (f : Option (Array UInt8)) : Prop := ∀ out, f = some out → out.size = 96

theorem g1Add_size (a b : Array UInt8) : G1Out (g1Add a b) := by
  intro out h
  unfold g1Add at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, h⟩ := h
  split at h
  · rw [← Option.some.inj h]; exact compressG1_size _
  · cases h

theorem g1Sub_size (a b : Array UInt8) : G1Out (g1Sub a b) := by
  intro out h
  unfold g1Sub at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, h⟩ := h
  split at h
  · rw [← Option.some.inj h]; exact compressG1_size _
  · cases h

theorem g1Neg_size (a : Array UInt8) : G1Out (g1Neg a) := by
  intro out h
  unfold g1Neg at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, h⟩ := h
  rw [← Option.some.inj h]; exact compressG1_size _

theorem g1MulInt_size (a : Array UInt8) (x : Int) : G1Out (g1MulInt a x) := by
  intro out h
  unfold g1MulInt at h
  split at h
  · rw [← Option.some.inj h]; exact g1ZeroBytes_size
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    exact compressG1_size _

theorem g1MultiExp_size (ps : Array (Array UInt8)) (xs : Array Int) : G1Out (g1MultiExp ps xs) := by
  intro out h
  unfold g1MultiExp at h
  split at h
  · rw [← Option.some.inj h]; exact g1ZeroBytes_size
  · split at h
    · exact g1MulInt_size _ _ out h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      rw [← Option.some.inj h]; exact compressG1_size _

theorem mapToG1Bytes_size (a : Array UInt8) : (mapToG1Bytes a).size = 48 := compressG1_size _

theorem g2Add_size (a b : Array UInt8) : G2Out (g2Add a b) := by
  intro out h
  unfold g2Add at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, h⟩ := h
  split at h
  · rw [← Option.some.inj h]; exact compressG2_size _
  · cases h

theorem g2Sub_size (a b : Array UInt8) : G2Out (g2Sub a b) := by
  intro out h
  unfold g2Sub at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, h⟩ := h
  split at h
  · rw [← Option.some.inj h]; exact compressG2_size _
  · cases h

theorem g2Neg_size (a : Array UInt8) : G2Out (g2Neg a) := by
  intro out h
  unfold g2Neg at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, h⟩ := h
  rw [← Option.some.inj h]; exact compressG2_size _

theorem g2MulInt_size (a : Array UInt8) (x : Int) : G2Out (g2MulInt a x) := by
  intro out h
  unfold g2MulInt at h
  split at h
  · rw [← Option.some.inj h]; exact g2ZeroBytes_size
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    exact compressG2_size _

theorem g2MultiExp_size (ps : Array (Array UInt8)) (xs : Array Int) : G2Out (g2MultiExp ps xs) := by
  intro out h
  unfold g2MultiExp at h
  split at h
  · rw [← Option.some.inj h]; exact g2ZeroBytes_size
  · split at h
    · exact g2MulInt_size _ _ out h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      rw [← Option.some.inj h]; exact compressG2_size _

theorem mapToG2Bytes_size (a : Array UInt8) : (mapToG2Bytes a).size = 96 := compressG2_size _

/-- A loop over a range in `Id` followed by `g`: an invariant of the loop that `g` turns into
`Q`. -/
theorem id_run_forIn_bind_inv {β γ : Type} (Q : γ → Prop) (inv : β → Prop) {xs : Std.Range}
    {init : β} {f : Nat → β → Id (ForInStep β)} {g : β → Id γ} (h0 : inv init)
    (hf : ∀ i b, inv b → inv (f i b).run.value) (hg : ∀ b, inv b → Q (g b).run) :
    Q ((forIn xs init f >>= g).run) :=
  hg _ (WF.id_forIn_range inv h0 hf)

theorem aggregate_size (sigs : Array (Array UInt8)) : G2Out (aggregate sigs) := by
  unfold G2Out aggregate
  simp only [pure_bind]
  split
  · intro out h; cases h
  · refine id_run_forIn_bind_inv
      (Q := fun o : Option (Array UInt8) => ∀ out : Array UInt8, o = some out → out.size = 96)
      (inv := fun r : MProd (Option (Option (Array UInt8))) (Jac Fp2) =>
        r.fst = none ∨ r.fst = some none) ?_ ?_ ?_
    · exact Or.inl rfl
    · intro i b _
      split
      · exact Or.inr rfl
      · split
        · exact Or.inr rfl
        · exact Or.inl rfl
    · intro b hb out h
      rcases hb with hb | hb <;> rw [hb] at h
      · rw [← Option.some.inj h]; exact compressG2_size _
      · exact absurd h (by simp)

end Bls12381

theorem foldl_append_natToBits_size {α : Type} (f : α → Nat) :
    ∀ (l : List α) (init : BitString),
      (l.foldl (fun b a => b ++ natToBits (f a) 8) init).size = init.size + 8 * l.length := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons a l ih =>
    intro init
    simp only [List.foldl_cons, List.length_cons, ih, Array.size_append, natToBits_size]
    omega

/-- The slice of the bits of at most 127 bytes is well-formed. -/
theorem sliceOfByteArray_WF {ba : ByteArray} (h : ba.size ≤ 127) : (sliceOfByteArray ba).WF := by
  unfold sliceOfByteArray
  simp only [pure_bind, Std.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  refine Slice.ofCell_WF (Cell.mkOrdinary_WF ?_ (by simp) (by simp))
  rw [foldl_append_natToBits_size]
  simp
  omega


theorem hashExtChunks_WF (digest : ByteArray) :
    ∀ (k off : Nat) (res : Array Value), (∀ v ∈ res, v.WF) →
      ∀ v ∈ hashExtChunks digest k off res, v.WF
  | 0, _, _, h => h
  | k + 1, _, _, h => hashExtChunks_WF digest k _ _ (by
      simp only [Array.forall_mem_push]; exact ⟨Value.WF.int _, h⟩)

theorem hashExtChunks_nil_WF (digest : ByteArray) (k off : Nat) :
    ∀ v ∈ hashExtChunks digest k off #[], v.WF :=
  hashExtChunks_WF digest k off #[] (by simp)

/-! ## The handlers -/

theorem execInstrCryptoHashExt_WF : FamilyWF execInstrCryptoHashExt := by
  intro i next hi hnext
  unfold execInstrCryptoHashExt
  generalize_opaque sha := sha256Digest
  generalize_opaque sha5 := sha512Digest
  generalize_opaque blake := Blake2b.blake2b512
  generalize_opaque k256 := Keccak.keccak256
  generalize_opaque k512 := Keccak.keccak512
  generalize_opaque num := IntVal.num
  simp only [pure_bind]
  -- the loop over the entries and the loop over the digest bytes, in each of the 15 branches
  -- on the hash and the version
  mvcgen [hnext] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun p st => ⌜st.WF ∧ p.2.size = 8 * p.1.prefix.length⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_cells [hashExtChunks_nil_WF, List.length_range']

theorem execInstrCryptoHashCU_WF : FamilyWF execInstrCryptoHashCU := by
  intro i next hi hnext
  unfold execInstrCryptoHashCU
  generalize_opaque hb := Cell.hashBytes
  generalize_opaque num := IntVal.num
  mvcgen [hnext]
  all_goals wf_cells

theorem execInstrCryptoHashSU_WF : FamilyWF execInstrCryptoHashSU := by
  intro i next hi hnext
  unfold execInstrCryptoHashSU
  generalize_opaque hb := Cell.hashBytes
  generalize_opaque num := IntVal.num
  mvcgen [hnext]
  all_goals wf_cells

theorem execInstrCryptoSha256U_WF : FamilyWF execInstrCryptoSha256U := by
  intro i next hi hnext
  unfold execInstrCryptoSha256U
  generalize_opaque sha := sha256Digest
  generalize_opaque num := IntVal.num
  mvcgen [hnext]
  all_goals wf_cells

theorem execInstrCryptoChkSignU_WF : FamilyWF execInstrCryptoChkSignU := by
  intro i next hi hnext
  unfold execInstrCryptoChkSignU
  generalize_opaque ver := Ed25519.verify
  simp only [pure_bind]
  mvcgen [hnext]
  all_goals wf_cells

theorem execInstrCryptoChkSignS_WF : FamilyWF execInstrCryptoChkSignS := by
  intro i next hi hnext
  unfold execInstrCryptoChkSignS
  generalize_opaque ver := Ed25519.verify
  simp only [pure_bind]
  mvcgen [hnext]
  all_goals wf_cells

theorem execInstrCryptoExt_WF : FamilyWF execInstrCryptoExt := by
  intro i next hi hnext
  unfold execInstrCryptoExt
  -- the points the BLS12-381 operations return: their sizes, then the operations generalized
  have hsl : ∀ a : Array UInt8, a.size ≤ 127 → (sliceOfByteArray (ByteArray.mk a)).WF :=
    fun _ h => sliceOfByteArray_WF h
  have hz1 := Bls12381.g1ZeroBytes_size
  have hz2 := Bls12381.g2ZeroBytes_size
  have ha : ∀ a out, Bls12381.aggregate a = some out → out.size = 96 := Bls12381.aggregate_size
  have h1a : ∀ a b out, Bls12381.g1Add a b = some out → out.size = 48 := Bls12381.g1Add_size
  have h1s : ∀ a b out, Bls12381.g1Sub a b = some out → out.size = 48 := Bls12381.g1Sub_size
  have h2a : ∀ a b out, Bls12381.g2Add a b = some out → out.size = 96 := Bls12381.g2Add_size
  have h2s : ∀ a b out, Bls12381.g2Sub a b = some out → out.size = 96 := Bls12381.g2Sub_size
  have h1n : ∀ a out, Bls12381.g1Neg a = some out → out.size = 48 := Bls12381.g1Neg_size
  have h2n : ∀ a out, Bls12381.g2Neg a = some out → out.size = 96 := Bls12381.g2Neg_size
  have h1m : ∀ a x out, Bls12381.g1MulInt a x = some out → out.size = 48 :=
    Bls12381.g1MulInt_size
  have h2m : ∀ a x out, Bls12381.g2MulInt a x = some out → out.size = 96 :=
    Bls12381.g2MulInt_size
  have h1e : ∀ a x out, Bls12381.g1MultiExp a x = some out → out.size = 48 :=
    Bls12381.g1MultiExp_size
  have h2e : ∀ a x out, Bls12381.g2MultiExp a x = some out → out.size = 96 :=
    Bls12381.g2MultiExp_size
  have h1p := Bls12381.mapToG1Bytes_size
  have h2p := Bls12381.mapToG2Bytes_size
  generalize_opaque sob := sliceOfByteArray at hsl
  generalize_opaque z1 := Bls12381.g1ZeroBytes at hz1
  generalize_opaque z2 := Bls12381.g2ZeroBytes at hz2
  generalize_opaque agg := Bls12381.aggregate at ha
  generalize_opaque g1a := Bls12381.g1Add at h1a
  generalize_opaque g1s := Bls12381.g1Sub at h1s
  generalize_opaque g2a := Bls12381.g2Add at h2a
  generalize_opaque g2s := Bls12381.g2Sub at h2s
  generalize_opaque g1n := Bls12381.g1Neg at h1n
  generalize_opaque g2n := Bls12381.g2Neg at h2n
  generalize_opaque g1m := Bls12381.g1MulInt at h1m
  generalize_opaque g2m := Bls12381.g2MulInt at h2m
  generalize_opaque g1e := Bls12381.g1MultiExp at h1e
  generalize_opaque g2e := Bls12381.g2MultiExp at h2e
  generalize_opaque g1p := Bls12381.mapToG1Bytes at h1p
  generalize_opaque g2p := Bls12381.mapToG2Bytes at h2p
  -- the checks and the other curves: booleans and integers
  generalize_opaque bv := Bls12381.verify
  generalize_opaque bfv := Bls12381.fastAggregateVerify
  generalize_opaque bav := Bls12381.aggregateVerify
  generalize_opaque g1g := Bls12381.g1InGroup
  generalize_opaque g2g := Bls12381.g2InGroup
  generalize_opaque g1z := Bls12381.g1IsZero
  generalize_opaque g2z := Bls12381.g2IsZero
  generalize_opaque bp := Bls12381.pairing
  generalize_opaque ecr := Secp256k1.ecrecover
  generalize_opaque xpt := Secp256k1.xonlyPubkeyTweakAdd
  generalize_opaque p256 := P256.verify
  generalize_opaque rfh := Ristretto255.fromHash
  generalize_opaque rv := Ristretto255.isValid
  generalize_opaque radd := Ristretto255.add
  generalize_opaque rsub := Ristretto255.sub
  generalize_opaque rmul := Ristretto255.mul
  generalize_opaque rmb := Ristretto255.mulBase
  generalize_opaque num := IntVal.num
  simp only [pure_bind]
  -- the loops of BLS_AGGREGATE, BLS_FASTAGGREGATEVERIFY, BLS_AGGREGATEVERIFY, BLS_G1_MULTIEXP,
  -- BLS_G2_MULTIEXP, BLS_PAIRING
  mvcgen [hnext, pushUInt256BE, popNatInRange] invariants
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  · post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩
  all_goals wf_cells

theorem execInstrCrypto_WF : FamilyWF execInstrCrypto := by
  intro i next hi hnext
  unfold execInstrCrypto
  exact execInstrCryptoHashExt_WF i _ hi <| execInstrCryptoHashCU_WF i _ hi <|
    execInstrCryptoHashSU_WF i _ hi <| execInstrCryptoSha256U_WF i _ hi <|
    execInstrCryptoChkSignU_WF i _ hi <| execInstrCryptoChkSignS_WF i _ hi <|
    execInstrCryptoExt_WF i _ hi <| hnext

end TvmLean

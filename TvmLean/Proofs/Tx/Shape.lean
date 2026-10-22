import TvmLean.Proofs.Tx.Effect
import TvmLean.Proofs.Tx.ReadBack
import TvmLean.Proofs.Fast.Sha256

/-!
# The shape of the account a transaction writes

`computeState_readBack` reads back the account `Tx.computeState` writes if its address, its dict
hash and its fixed prefix length have the shape the reader needs (`Tx.Fits`). They do for the state
every transaction the model runs ends in (`EmulateFinal.fits`, `TickTockFinal.fits`):
* `Account.unpack` reads an account of `Account.Shape` (`unpack_shape`): addresses of
  `Account.mkAddr` with 256 bits and an anycast prefix below 32 bits (`AddrOK`), a rewrite length and
  a fixed prefix length below 32, a 256-bit dict hash (what a read returns: `RP`); the address of
  the account has 256 bits (`stdAddressOf_size`);
* the phases keep `Tx.Shape`: the compute phase (`computePhaseRun_shape`) sets the address to the
  exact one, or (before version 10) to the address with the anycast prefix of the message's
  `StateInit` (`addrOK_rewritten`), and the fixed prefix length to that of the `StateInit`; no other
  phase changes them (`Tx.Keep`, the action phase's `Tx.AddrKeep`);
* the dict hash computed from the storage is a cell hash, of 32 bytes (`Cell.hashBytes_size`: the
  level information of a cell has four hashes of 32 bytes, `levelInfoFromChildren_hashes`; SHA-256
  returns 32 bytes, `sha256Digest_size`).
-/

namespace TvmLean

open TvmLean.Proofs.TxTac

/-! ## A cell hash has 32 bytes -/

theorem Sha256F.compress_length (h ws : List Nat) : (Sha256F.compress h ws).length = h.length := by
  unfold Sha256F.compress
  split <;> simp

theorem Sha256F.hashBlocks_length : ∀ (n : Nat) (h l : List Nat), (Sha256F.hashBlocks n h l).length = h.length
  | 0, h, l => by simp [Sha256F.hashBlocks]
  | n + 1, h, l => by
    rw [Sha256F.hashBlocks, Sha256F.hashBlocks_length n, Sha256F.compress_length]

theorem sum_map_four (l : List Nat) : (l.map fun _ => 4).sum = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

theorem sha256Digest_size (msg : Array UInt8) : (sha256Digest msg).size = 32 := by
  rw [sha256Digest_eq_fast]
  unfold sha256DigestFast
  simp only [List.size_toArray]
  unfold Sha256F.outBytes
  rw [List.length_flatMap]
  have := Sha256F.hashBlocks_length ((Sha256F.padN (msg.toList.map UInt8.toNat)).length / 64) Sha256F.H0
    (Sha256F.padN (msg.toList.map UInt8.toNat))
  generalize Sha256F.hashBlocks _ _ _ = l at this
  simp only [Sha256F.H0, List.length_cons, List.length_nil] at this
  simp only [List.length_cons, List.length_nil]
  rw [sum_map_four, this]

/-- Four hashes of 32 bytes. -/
def HOK (hs : Array (Array UInt8)) : Prop := hs.size = 4 ∧ ∀ i < 4, (hs[i]!).size = 32

theorem OKe_bind_any {ε α β : Type} {R : β → Prop} (e : Except ε α) (k : α → Except ε β)
    (h : ∀ a, OKe R (k a)) : OKe R (e >>= k) :=
  OKe_bind e k fun a _ => h a

theorem OKe_forIn_inv {ε α β : Type} (l : List α) (init : β) (f : α → β → Except ε (ForInStep β))
    (I : β → Prop) (h0 : I init)
    (hs : ∀ a b, I b → OKe (fun s => match s with | .yield b' => I b' | .done b' => I b') (f a b)) :
    OKe I (forIn l init f) := by
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih =>
    simp only [List.forIn_cons]
    have := hs a init h0
    revert this
    cases f a init with
    | error e => intro _; trivial
    | ok s =>
      intro hs'
      cases s with
      | yield b => exact ih b hs'
      | done b => exact hs'

theorem OKe_forIn_bind_inv {ε α β γ : Type} (l : List α) (init : β) (f : α → β → Except ε (ForInStep β))
    (k : β → Except ε γ) {R : γ → Prop} (I : β → Prop) (h0 : I init)
    (hs : ∀ a b, I b → OKe (fun s => match s with | .yield b' => I b' | .done b' => I b') (f a b))
    (hk : ∀ b, I b → OKe R (k b)) : OKe R (forIn l init f >>= k) :=
  OKe_bind _ _ fun b hb => hk b (OKe_of (OKe_forIn_inv l init f I h0 hs) hb)

theorem HOK_init : HOK (Array.replicate (Cell.maxLevel + 1) (Array.replicate 32 0)) := by
  unfold HOK; decide

theorem HOK_set {hs : Array (Array UInt8)} (h : HOK hs) (j : Nat) {v : Array UInt8} (hv : v.size = 32) :
    HOK (hs.set! j v) := by
  obtain ⟨h1, h2⟩ := h
  have hsz : (hs.set! j v).size = 4 := by simp [h1]
  refine ⟨hsz, fun i hi => ?_⟩
  rw [getElem!_pos (hs.set! j v) i (by omega)]
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds (by omega)]
  split
  · exact hv
  · have := h2 i hi
    rwa [getElem!_pos hs i (by omega)] at this

set_option maxHeartbeats 4000000 in
/-- The hashes of the level information of a cell (`Cell.levelInfoFromChildren`): four of 32 bytes. -/
theorem levelInfoFromChildren_hashes (c : Cell) (ci : Array CellLevelInfo) :
    OKe (fun info : CellLevelInfo => HOK info.hashes) (Cell.levelInfoFromChildren c ci) := by
  unfold Cell.levelInfoFromChildren
  tx_vcg
  all_goals (repeat (first
    | refine OKe_forIn_bind_inv (I := fun r : MProd (Array (Array UInt8)) (Option Nat) => HOK r.1) _ _ _ _ ?_ ?_ ?_
    | (refine OKe_bind_any _ _ fun _ => ?_; tx_vcg)))
  all_goals try refine OKe_forIn_bind_inv (I := fun r : MProd (Array (Array UInt8)) (Option Nat) => HOK r.1) _ _ _ _ ?_ ?_ ?_
  all_goals first
    | exact HOK_init
    | (intro b hb; tx_vcg; exact hb)
    | skip
  all_goals
    intro lvl b hb
    tx_vcg
  all_goals try exact hb
  all_goals
    have hh : h.size = 32 := by
      first
        | (simp only [h, Array.size_extract]; (try subst_vars); omega)
        | (dsimp (config := { zetaDelta := true }) only
           repeat' split
           all_goals first | (with_reducible exact sha256Digest_size _) | simp_all)
    refine OKe_forIn_bind_inv (I := HOK) _ _ _ _ hb (fun j r hr => HOK_set hr j hh) (fun r hr => HOK_set hr _ hh)

theorem computeLevelInfo_hashes (c : Cell) : OKe (fun info => HOK info.hashes) c.computeLevelInfo? := by
  rcases c with ⟨bits, ⟨refs⟩, special, lm⟩
  unfold Cell.computeLevelInfo?
  tx_vcg
  exact levelInfoFromChildren_hashes _ _

/-- A cell hash has 32 bytes. -/
theorem Cell.hashBytes_size (c : Cell) : c.hashBytes.size = 32 := by
  unfold Cell.hashBytes
  cases h : c.computeLevelInfo? with
  | error e => simp
  | ok info =>
    have := OKe_of (computeLevelInfo_hashes c) h
    unfold CellLevelInfo.getHash CellLevelInfo.clampLevel
    exact this.2 _ (by simp only [Cell.maxLevel, Nat.min_def]; split <;> split <;> omega)

end TvmLean

namespace TvmLean.Tx

open TvmLean.Proofs.TxTac

/-! ## What a read returns -/

/-- Every value the read `r` returns satisfies `P`. -/
def RP {α : Type} (r : Reader α) (P : α → Prop) : Prop := ∀ s v s', r s = some (v, s') → P v

theorem RP.bind {α β : Type} {r : Reader α} {k : α → Reader β} {P : α → Prop} {Q : β → Prop}
    (h1 : RP r P) (h2 : ∀ x, P x → RP (k x) Q) : RP (r >>= k) Q := by
  intro s v s' h
  have e : (r >>= k) s = (r s).bind (fun p => k p.1 p.2) := rfl
  rw [e] at h
  cases hr : r s with
  | none => rw [hr] at h; cases h
  | some p =>
    rw [hr] at h
    exact h2 p.1 (h1 s p.1 p.2 hr) p.2 v s' h

theorem RP.ret {α : Type} (a : α) : RP (pure a : Reader α) (· = a) := by
  intro s v s' h
  have e : (pure a : Reader α) s = some (a, s) := rfl
  rw [e] at h
  cases h
  rfl

theorem RP.mono {α : Type} {r : Reader α} {P Q : α → Prop} (h : RP r P) (hPQ : ∀ x, P x → Q x) : RP r Q :=
  fun s v s' hr => hPQ v (h s v s' hr)

theorem RP.any {α : Type} (r : Reader α) : RP r (fun _ => True) := fun _ _ _ _ => trivial

theorem RP.fail {α : Type} (P : α → Prop) : RP (Reader.fail : Reader α) P := by
  intro s v s' h; cases h

theorem RP.bits (n : Nat) : RP (Reader.bits n) (fun v => v.size = n) := by
  intro s v s' h
  unfold Reader.bits at h
  split at h
  · rename_i hb
    cases h
    simp only [Slice.haveBits, decide_eq_true_eq] at hb
    simp only [Slice.readBits, Array.size_extract]
    omega
  · cases h

theorem bitsToNat_lt_pow (bs : BitString) : bitsToNat bs < 2 ^ bs.size := by
  have key : ∀ (l : List Bool) (acc k : Nat), acc < 2 ^ k →
      l.foldl (fun acc b => (acc <<< 1) + (if b then 1 else 0)) acc < 2 ^ (k + l.length) := by
    intro l
    induction l with
    | nil => intro acc k h; simpa using h
    | cons b l ih =>
      intro acc k h
      simp only [List.foldl_cons, List.length_cons]
      have := ih ((acc <<< 1) + (if b then 1 else 0)) (k + 1) (by
        rw [Nat.shiftLeft_eq, Nat.pow_succ]; split <;> omega)
      rwa [show k + 1 + l.length = k + (l.length + 1) by omega] at this
  unfold bitsToNat
  rw [← Array.foldl_toList]
  have := key bs.toList 0 0 (by decide)
  simpa using this

theorem RP.uint (n : Nat) : RP (Reader.uint n) (· < 2 ^ n) := by
  unfold Reader.uint
  refine RP.bind (RP.bits n) fun v hv => ?_
  refine (RP.ret _).mono fun x hx => ?_
  subst hx; rw [← hv]; exact bitsToNat_lt_pow v

theorem RP.bool : RP Reader.bool (fun _ => True) := RP.any _

theorem RP.maybe {α : Type} {r : Reader α} {P : α → Prop} (h : RP r P) :
    RP (Reader.maybe r) (fun o => ∀ x, o = some x → P x) := by
  unfold Reader.maybe
  refine RP.bind (RP.any _) fun b _ => ?_
  split
  · refine RP.bind h fun x hx => (RP.ret _).mono fun o ho => ?_
    subst ho; intro y hy; cases hy; exact hx
  · exact (RP.ret _).mono fun o ho => by subst ho; intro y hy; cases hy

theorem RP.addrStd : RP Account.Reader.addrStd
    (fun r => (∀ p, r.1 = some p → p.size ≤ 30) ∧ r.2.2.size = 256) := by
  unfold Account.Reader.addrStd
  refine RP.bind (RP.any _) fun t _ => ?_
  split
  · exact RP.bind (RP.fail (fun _ : PUnit => False)) fun _ h => h.elim
  · refine RP.bind (RP.any _) fun _ _ => ?_
    refine RP.bind (RP.maybe (P := fun p => p.size ≤ 30) ?_) fun pfx hpfx => ?_
    · refine RP.bind (RP.any _) fun d _ => ?_
      split
      · exact RP.bind (RP.fail (fun _ : PUnit => False)) fun _ h => h.elim
      · rename_i hd
        refine RP.bind (RP.any _) fun _ _ => ?_
        exact (RP.bits d).mono fun v hv => by omega
    · refine RP.bind (RP.any _) fun w _ => ?_
      refine RP.bind (RP.bits 256) fun a ha => ?_
      exact (RP.ret _).mono fun r hr => by subst hr; exact ⟨hpfx, ha⟩

theorem RP.storageInfo : RP Account.Reader.storageInfo (fun r => ∀ h, r.2.1 = some h → h.size = 256) := by
  unfold Account.Reader.storageInfo
  refine RP.bind (RP.any _) fun _ _ => ?_
  refine RP.bind (RP.any _) fun _ _ => ?_
  refine RP.bind (RP.any _) fun tag _ => ?_
  dsimp only
  split
  · refine RP.bind (P := fun d : Option BitString => ∀ h, d = some h → h.size = 256) ?_ fun d hd => ?_
    · rw [map_eq_pure_bind]
      refine RP.bind (RP.bits 256) fun x hx => (RP.ret _).mono fun d hd => ?_
      subst hd
      intro h hh
      cases hh
      exact hx
    · refine RP.bind (RP.any _) fun _ _ => ?_
      refine RP.bind (RP.any _) fun _ _ => ?_
      exact (RP.ret _).mono fun r hr => by subst hr; exact hd
  · split
    · refine RP.bind (RP.ret _) fun d hd => ?_
      subst hd
      refine RP.bind (RP.any _) fun _ _ => ?_
      refine RP.bind (RP.any _) fun _ _ => ?_
      exact (RP.ret _).mono fun r hr => by subst hr; intro h hh; cases hh
    · exact RP.bind (RP.fail (fun _ : Option BitString => False)) fun _ h => h.elim

theorem RP.stateInit : RP Account.Reader.stateInit (fun si => si.fixedPrefixLength.getD 0 < 32) := by
  unfold Account.Reader.stateInit
  refine RP.bind (RP.maybe (RP.uint 5)) fun fpl hfpl => ?_
  refine RP.bind (RP.any _) fun _ _ => ?_
  refine RP.bind (RP.any _) fun _ _ => ?_
  refine RP.bind (RP.any _) fun _ _ => ?_
  refine RP.bind (RP.any _) fun _ _ => ?_
  refine (RP.ret _).mono fun si hsi => ?_
  subst hsi
  cases fpl with
  | none => simp
  | some x => exact hfpl x rfl

theorem RP.runExact {α : Type} {r : Reader α} {P : α → Prop} (h : RP r P) {c : Cell} {v : α}
    (hv : Reader.runExact r c = some v) : P v := by
  unfold Reader.runExact at hv
  cases hrs : r (Slice.ofCell c) with
  | none => rw [hrs] at hv; cases hv
  | some p =>
    obtain ⟨v', s'⟩ := p
    rw [hrs] at hv
    dsimp only at hv
    split at hv
    · cases hv; exact h _ _ _ hrs
    · cases hv

/-- The read of `account$1 addr:MsgAddressInt storage_stat:StorageInfo` in `Account.unpack`. -/
theorem RP.accountPrefix : RP (do
      let _ ← Reader.bits 1
      let (pfx, awc, addrOrig) ← Account.Reader.addrStd
      return (pfx, awc, addrOrig, ← Account.Reader.storageInfo))
    (fun r => (∀ p, r.1 = some p → p.size ≤ 30) ∧ r.2.2.1.size = 256 ∧
      ∀ h, r.2.2.2.2.1 = some h → h.size = 256) := by
  refine RP.bind (RP.any _) fun _ _ => ?_
  refine RP.bind RP.addrStd fun x hx => ?_
  obtain ⟨pfx, awc, addrOrig⟩ := x
  dsimp only
  refine RP.bind RP.storageInfo fun y hy => ?_
  exact (RP.ret _).mono fun r hr => by subst hr; exact ⟨hx.1, hx.2, hy⟩

/-! ## The shape of an account -/

/-- An address as `Account.mkAddr` writes it: 256 bits and an anycast prefix below 32 bits (what
`ReadsAs.addrStd_mkAddr` reads back). -/
def AddrOK (c : Cell) : Prop :=
  ∃ wc any a lim, c = Account.mkAddr wc any a lim ∧ a.size = 256 ∧ ∀ q, any = some q → q.size < 32

theorem AddrOK.mk (wc : Int) (any : Option BitString) (a : BitString) (lim : Int) (ha : a.size = 256)
    (hq : ∀ q, any = some q → q.size < 32) : AddrOK (Account.mkAddr wc any a lim) :=
  ⟨wc, any, a, lim, rfl, ha, hq⟩

/-- What the account `Account.unpack` reads has of the shape the account `Tx.computeState` writes
needs: its addresses (`AddrOK`), a 256-bit address, a rewrite length and a fixed prefix length below
32, a 256-bit dict hash. -/
def Account.Shape (a : Account) : Prop :=
  AddrOK a.myAddr ∧ AddrOK a.myAddrExact ∧ a.addr.size = 256 ∧ a.addrRewriteLength < 32 ∧
    a.fixedPrefixLength < 32 ∧ ∀ h, a.storageDictHash = some h → h.size = 256

theorem unpackAddress_shape (a : Account) (pfx? : Option BitString) (wc : Int) (addrOrig : BitString)
    (ha : a.addr.size = 256) (hfpl : a.fixedPrefixLength < 32)
    (hd : ∀ h, a.storageDictHash = some h → h.size = 256)
    (hp : ∀ p, pfx? = some p → p.size ≤ 30) (ho : addrOrig.size = 256) :
    OKo Account.Shape (Account.unpackAddress a pfx? wc addrOrig) := by
  have hlen : (pfx?.map (·.size)).getD 0 ≤ 30 := by
    cases h : pfx? with
    | none => simp
    | some p => simpa using hp p h
  unfold Account.unpackAddress Account.withMyAddr
  tx_vcg
  all_goals simp (config := { zetaDelta := true }) only [Account.Shape]
  all_goals first
    | exact ⟨AddrOK.mk _ _ _ _ ho (fun q h => by cases h), AddrOK.mk _ _ _ _ ho (fun q h => by cases h), ha,
        by omega, hfpl, hd⟩
    | exact ⟨AddrOK.mk _ _ _ _ ho (fun q h => by split at h <;> (cases h <;> simp <;> omega)),
        AddrOK.mk _ _ _ _ ha (fun q h => by cases h), ha, by omega, hfpl, hd⟩

theorem initNew_shape (wc : Int) (addr : BitString) (haddr : addr.size = 256) :
    AddrOK (Account.initNew wc addr).myAddr ∧ AddrOK (Account.initNew wc addr).myAddrExact ∧
      (Account.initNew wc addr).addr.size = 256 ∧ (Account.initNew wc addr).addrRewriteLength < 32 ∧
      (Account.initNew wc addr).fixedPrefixLength < 32 ∧
      ∀ h, (Account.initNew wc addr).storageDictHash = some h → h.size = 256 :=
  ⟨AddrOK.mk wc none addr 128 haddr (fun _ h => by cases h), AddrOK.mk wc none addr 128 haddr (fun _ h => by cases h),
    haddr, Nat.zero_lt_succ 31, Nat.zero_lt_succ 31, fun _ h => by cases h⟩

set_option maxHeartbeats 2000000 in
/-- The account `Account.unpack` reads at a 256-bit address has the shape of `Account.Shape`. -/
theorem unpack_shape (sa : Cell) (wc : Int) (addr : BitString) (sp : Bool) (haddr : addr.size = 256) :
    OKo Account.Shape (Account.unpack sa wc addr sp) := by
  have hb := initNew_shape wc addr haddr
  unfold Account.unpack
  tx_vcg
  · exact hb
  all_goals
    obtain ⟨hp1, hp2, hp3⟩ := RP.accountPrefix _ _ _ ‹_›
    dsimp only at hp1 hp2 hp3
    have hA := OKo_of (unpackAddress_shape base _ _ _ hb.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2 hp1 hp2) ‹_›
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hA
    simp (config := { zetaDelta := true }) only [Account.Shape]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | assumption
    | (simp; done)
    | exact RP.runExact RP.stateInit ‹_›

/-! ## The shape through the compute phase -/

/-- What the transaction has of the shape the account `Tx.computeState` writes needs: its addresses
(`AddrOK`), a fixed prefix length below 32, the account it started from (`Account.Shape`). -/
def Tx.Shape (t : Tx) : Prop :=
  AddrOK t.myAddr ∧ AddrOK t.myAddrExact ∧ t.newFixedPrefixLength < 32 ∧ t.account.Shape

theorem msgStateInit_fpl {o : Option Cell} {si : Account.StateInit}
    (h : o.bind (Reader.runExact Account.Reader.stateInit) = some si) : si.fixedPrefixLength.getD 0 < 32 := by
  cases o with
  | none => cases h
  | some c => exact RP.runExact RP.stateInit h

/-- The address with an anycast prefix that `Tx.checkInMsgStateHash` makes (before version 10): the
address checked against the hash below the prefix has 256 bits. -/
theorem addrOK_rewritten {h addr : BitString} {d : Nat} (wc : Int) (ha : addr.size = 256) (hd : d < 32)
    (he : h.extract d 256 = addr.extract d 256) :
    AddrOK (Account.mkAddr wc (some (addr.extract 0 d)) (h.extract 0 d ++ addr.extract d 256)) := by
  have hs := congrArg Array.size he
  simp only [Array.size_extract, ha] at hs
  refine AddrOK.mk _ _ _ _ ?_ ?_
  · simp only [Array.size_append, Array.size_extract, ha]
    omega
  · intro q hq
    cases hq
    simp only [Array.size_extract, ha]
    omega

theorem payGas_shape (t : Tx) (gas : GasPrices) (cp : ComputePhase) :
    OKe (fun r : Tx × ComputePhase => r.1.myAddr = t.myAddr ∧ r.1.myAddrExact = t.myAddrExact ∧
      r.1.newFixedPrefixLength = t.newFixedPrefixLength ∧ r.1.account = t.account) (t.payGas gas cp) := by
  unfold Tx.payGas
  tx_vcg
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem unpackMsgState_shape (t : Tx) (sl : SizeLimits) (libOnly : Bool) :
    OKp (fun r : Tx × Bool => r.1.myAddr = t.myAddr ∧ r.1.myAddrExact = t.myAddrExact ∧
      r.1.account = t.account ∧ (r.1.newFixedPrefixLength = t.newFixedPrefixLength ∨ r.1.newFixedPrefixLength < 32))
      (t.unpackMsgState sl libOnly) := by
  unfold Tx.unpackMsgState
  tx_vcg
  all_goals first
    | exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
    | exact ⟨rfl, rfl, rfl, Or.inr (msgStateInit_fpl ‹_›)⟩

theorem checkInMsgStateHash_shape (t : Tx) :
    OKo (fun u => u.myAddrExact = t.myAddrExact ∧ u.account = t.account ∧
      u.newFixedPrefixLength = t.newFixedPrefixLength ∧
      (t.account.addr.size = 256 → t.newFixedPrefixLength < 32 → AddrOK t.myAddrExact → AddrOK u.myAddr))
      t.checkInMsgStateHash := by
  unfold Tx.checkInMsgStateHash
  tx_vcg
  all_goals refine ⟨rfl, rfl, rfl, fun ha hd hx => ?_⟩
  all_goals first
    | exact hx
    | exact addrOK_rewritten _ ha hd (eq_of_not_bne ‹_›)

set_option maxHeartbeats 4000000 in
/-- The compute phase keeps `Tx.Shape`. -/
theorem computePhaseRun_shape (t₀ : Tx) (gas : GasPrices) (sl : SizeLimits) (seed : BitString) (h : t₀.Shape) :
    OKe (OKo Tx.Shape) (t₀.computePhaseRun gas sl seed) := by
  unfold Tx.computePhaseRun
  tx_vcg keep_jps
  tx_jp_spec [Tx.Shape]
  all_goals tx_vcg_inv [Tx.Shape]
  all_goals try trivial
  all_goals tx_specs [payGas_shape, checkInMsgStateHash_shape, unpackMsgState_shape]
  all_goals tx_close [Tx.myAddr, Tx.myAddrExact, Tx.newFixedPrefixLength, Tx.account] [Tx.Shape, Account.Shape]


theorem bytesToBits_size (bs : Array UInt8) : (bytesToBits bs).size = 8 * bs.size := by
  unfold bytesToBits
  rw [← Array.foldl_toList]
  have key : ∀ (l : List UInt8) (acc : BitString),
      (l.foldl (fun acc b => acc ++ natToBits b.toNat 8) acc).size = acc.size + 8 * l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b l ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Array.size_append, natToBits_size, List.length_cons]
      omega
  rw [key]
  simp

/-- The storage dict hash has 256 bits. -/
theorem storageDictHash_size {m : Std.HashMap (Array UInt8) CellEntry} {h : BitString}
    (hh : storageDictHash m = some h) : h.size = 256 := by
  unfold storageDictHash at hh
  simp only [bind, Option.bind] at hh
  split at hh
  · cases hh
  · cases hh
    split
    · exact natToBits_size 0 256
    · rw [bytesToBits_size, Cell.hashBytes_size]

theorem storageStat_dictHash' (t : Tx) (sl : SizeLimits) (c : Cell)
    (hd : ∀ h, t.account.storageDictHash = some h → h.size = 256) :
    OKo (fun r : StorageUsed × Option BitString => ∀ h, r.2 = some h → h.size = 256) (t.storageStat sl c) := by
  unfold Tx.storageStat
  tx_vcg
  all_goals
    intro h hh
    try simp (config := { zetaDelta := true }) only at hh
    split at hh <;> first | exact storageDictHash_size hh | exact hd h hh | cases hh

/-- The storage statistics `Tx.computeState` writes have a 256-bit dict hash, if the account's has. -/
theorem storageStat_dictHash {t : Tx} {sl : SizeLimits} {c : Cell} {used : StorageUsed} {dh : Option BitString}
    (hd : ∀ h, t.account.storageDictHash = some h → h.size = 256)
    (hs : t.storageStat sl c = some (used, dh)) : ∀ h, dh = some h → h.size = 256 :=
  OKo_of (storageStat_dictHash' t sl c hd) hs

theorem csAdjust_keeps (t : Tx) :
    (csAdjust t).myAddr = t.myAddr ∧ (csAdjust t).account = t.account ∧
      (csAdjust t).newFixedPrefixLength = t.newFixedPrefixLength ∧ (csAdjust t).gv = t.gv := by
  unfold csAdjust
  dsimp only
  split <;> split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem csState_keeps (t : Tx) :
    (csState t).1.myAddr = t.myAddr ∧ (csState t).1.account = t.account := by
  unfold csState
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

/-- A transaction of `Tx.Shape` writes an account of the shape its reader needs (`Tx.Fits`). -/
theorem Tx.Shape.fits {tf : Tx} (h : tf.Shape) (sl : SizeLimits) : tf.Fits sl := by
  obtain ⟨hm, _, hf, ham, _, _, hrw, _, hdh⟩ := h
  obtain ⟨k1, k2, k3, k4⟩ := csAdjust_keeps tf
  intro p hp
  revert hp
  unfold Tx.computeStateParts
  dsimp only
  split
  · intro hp; cases hp
  · generalize hq : csState (csAdjust tf) = q
    obtain ⟨t', w⟩ := q
    dsimp only
    intro hp
    split at hp
    · cases hp
    · rename_i used dh hs
      cases hp
      obtain ⟨s1, s2⟩ := csState_keeps (csAdjust tf)
      rw [hq] at s1 s2
      dsimp only at s1 s2
      refine ⟨?_, ?_, ?_⟩
      · dsimp only
        unfold csAddr
        split
        · rw [s1, k1]; exact hm
        · rw [s2, k2]; exact ham
      · exact storageStat_dictHash (by rw [s2, k2]; exact hdh) hs
      · dsimp only
        unfold csFpl
        rw [k2, k3, k4]
        split
        · exact hf
        · exact hrw


/-! ## The shape through a transaction -/

theorem Tx.Shape.congr {t u : Tx} (h : t.Shape) (e1 : u.myAddr = t.myAddr) (e2 : u.myAddrExact = t.myAddrExact)
    (e3 : u.newFixedPrefixLength = t.newFixedPrefixLength) (e4 : u.account = t.account) : u.Shape := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨e1 ▸ h1, e2 ▸ h2, e3 ▸ h3, e4 ▸ h4⟩

/-- The address `stdAddressOf` reads has 256 bits. -/
theorem stdAddressOf_size {addrBits : BitString} {wc : Int} {addr : BitString}
    (h : stdAddressOf addrBits = some (wc, addr)) : addr.size = 256 := by
  have hr : RP (do
      let tag ← Reader.uint 2
      let pfx ← Reader.maybe (do let d ← Reader.uint 5; Reader.bits d)
      if tag == 2 then return (pfx, ← Reader.int 8, ← Reader.bits 256)
      else if tag == 3 then
        let len ← Reader.uint 9
        if len != 256 then Reader.fail
        return (pfx, ← Reader.int 32, ← Reader.bits 256)
      else Reader.fail)
      (fun r => (∀ p, r.1 = some p → p.size < 32) ∧ r.2.2.size = 256) := by
    refine RP.bind (RP.any _) fun tag _ => ?_
    refine RP.bind (RP.maybe (P := fun p => p.size < 32) ?_) fun pfx hpfx => ?_
    · exact RP.bind (RP.uint 5) fun d hd => (RP.bits d).mono fun v hv => by omega
    · split
      · refine RP.bind (RP.any _) fun _ _ => RP.bind (RP.bits 256) fun a ha => ?_
        exact (RP.ret _).mono fun r hr => by subst hr; exact ⟨hpfx, ha⟩
      · split
        · refine RP.bind (RP.any _) fun len _ => ?_
          dsimp only
          split
          · exact RP.bind (RP.fail (fun _ : PUnit => False)) fun _ h => h.elim
          · refine RP.bind (RP.any _) fun _ _ => RP.bind (RP.any _) fun _ _ => RP.bind (RP.bits 256) fun a ha => ?_
            exact (RP.ret _).mono fun r hr => by subst hr; exact ⟨hpfx, ha⟩
        · exact RP.fail _
  unfold stdAddressOf at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  · rename_i r heq
    obtain ⟨⟨pfx, w, a⟩, s'⟩ := r
    obtain ⟨hp, ha⟩ := hr _ _ _ heq
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    dsimp only at hp ha
    have hps : (pfx.getD #[]).size < 32 := by
      cases pfx with
      | none => simp
      | some p => exact hp p rfl
    simp only [Array.size_append, Array.size_extract, ha]
    omega

set_option maxHeartbeats 2000000 in
/-- The state a transaction starts from has `Tx.Shape`. -/
theorem newTx_shape (cfg : Config) (sa inMsg : Cell) (kind : TxKind) (wc : Int) (addr addrBits : BitString)
    (lt now : Nat) (libs : Option Cell) (haddr : addr.size = 256) :
    OKe (fun r : Tx × Array StoragePrices × SizeLimits × GasPrices × MsgPrices => r.1.Shape)
      (newTx cfg sa inMsg kind wc addr addrBits lt now libs) := by
  unfold newTx
  tx_vcg
  all_goals
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := OKo_of (unpack_shape _ _ _ _ haddr) ‹_›
    exact ⟨m1, m2, m5, m1, m2, m3, m4, m5, m6⟩

/-- The state an ordinary transaction ends in has `Tx.Shape`. -/
theorem EmulateFinal.shape {configRoot sa inMsg : Cell} {now lt : Nat} {seed : BitString} {libs : Option Cell}
    {tf : Tx} {sl : SizeLimits} (h : EmulateFinal configRoot sa inMsg now lt seed libs tf sl) : tf.Shape := by
  obtain ⟨cfg, wc, addr, addrBits, t0, pricing, gas, fwd, t1, t2, t3, t4, _, hstd, hnew, hin, ⟨nc, hsc⟩, hc, ha,
    hb⟩ := h
  have h0 := OKe_of (newTx_shape cfg sa inMsg .ord wc addr addrBits lt now libs (stdAddressOf_size hstd)) hnew
  have ⟨⟨a1, _⟩, _, _, m1, m2, f1⟩ := OKe_of (OKo_of (unpackInputMsg_spec t0 sl fwd) hin) rfl
  have h1 : t1.Shape := h0.congr m1 m2 f1 a1
  have ⟨⟨⟨a2, _⟩, _, _, m3, m4, f2⟩, _⟩ := StorageCredit.spec hsc
  have h2 : t2.Shape := h1.congr m3 m4 f2 a2
  have h3 : t3.Shape := OKo_of (OKe_of (computePhaseRun_shape t2 gas sl seed h2) hc) rfl
  have h4 : t4.Shape := by
    rcases ha with ⟨_, hap⟩ | ⟨_, rfl⟩
    · have ⟨⟨a3, _⟩, ⟨m5, m6, f3⟩, _⟩ := OKo_of (OKe_of (actionPhaseRun_spec t3 sl) hap) rfl
      exact h3.congr m5 m6 f3 a3
    · exact h3
  rcases hb with rfl | hb
  · exact h4
  · have ⟨⟨⟨a4, _⟩, _, _, m7, m8, f4⟩, _⟩ := OKo_of (OKe_of (bouncePhaseRun_spec t4) hb) rfl
    exact h4.congr m7 m8 f4 a4

/-- The state a tick-tock transaction ends in has `Tx.Shape`. -/
theorem TickTockFinal.shape {configRoot sa : Cell} {isTock : Bool} {now lt : Nat} {seed : BitString}
    {libs : Option Cell} {tf : Tx} {sl : SizeLimits}
    (h : TickTockFinal configRoot sa isTock now lt seed libs tf sl) : tf.Shape := by
  obtain ⟨cfg, kind, wc, addr, addrBits, t0, pricing, gas, fwd, t2, t3, _, hstd, hnew, _, hs, hc, ha⟩ := h
  have h0 := OKe_of (newTx_shape cfg sa Cell.empty kind wc addr addrBits lt now libs (stdAddressOf_size hstd)) hnew
  have ⟨⟨⟨a2, _⟩, _, _, m3, m4, f2⟩, _⟩ := OKo_of (storagePhaseRun_spec t0 pricing gas false) hs
  have h2 : t2.Shape := h0.congr m3 m4 f2 a2
  have h3 : t3.Shape := OKo_of (OKe_of (computePhaseRun_shape t2 gas sl seed h2) hc) rfl
  rcases ha with ⟨_, hap⟩ | ⟨_, rfl⟩
  · have ⟨⟨a3, _⟩, ⟨m5, m6, f3⟩, _⟩ := OKo_of (OKe_of (actionPhaseRun_spec t3 sl) hap) rfl
    exact h3.congr m5 m6 f3 a3
  · exact h3

/-- The account an ordinary transaction writes has the shape its reader needs. -/
theorem EmulateFinal.fits {configRoot sa inMsg : Cell} {now lt : Nat} {seed : BitString} {libs : Option Cell}
    {tf : Tx} {sl : SizeLimits} (h : EmulateFinal configRoot sa inMsg now lt seed libs tf sl) : tf.Fits sl :=
  h.shape.fits sl

/-- The account a tick-tock transaction writes has the shape its reader needs. -/
theorem TickTockFinal.fits {configRoot sa : Cell} {isTock : Bool} {now lt : Nat} {seed : BitString}
    {libs : Option Cell} {tf : Tx} {sl : SizeLimits}
    (h : TickTockFinal configRoot sa isTock now lt seed libs tf sl) : tf.Fits sl :=
  h.shape.fits sl

end TvmLean.Tx

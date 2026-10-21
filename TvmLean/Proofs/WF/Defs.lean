import TvmLean.Proofs.CellWF

/-!
# Well-formed values and VM states

`Cell.WF` (`Proofs/CellWF.lean`) bounds a cell and every cell below it by 1023 bits and 4
references. This module extends it to everything a VM state holds:

* `Slice.WF`: the slice's cell is well-formed and its positions are within it;
* `Value.WF`: cells, slices and builders well-formed, tuples and continuations recursively;
* `Continuation.WF`: the code slice of an ordinary continuation, the continuations it nests, the
  control registers it saves (`OrdCregs.WF`) and its captured stack (`OrdCdata.WF`);
* `Regs.WF`: the registers c0..c5 and c7;
* `VmState.WF`: the stack, the registers, `cc`, the committed c4 and c5, and the library
  collections (cells);
* `Instr.WF`: the cells and slices an instruction carries (`PUSHREF`, `PUSHSLICE`, `PUSHCONT`, ...):
  the decoder takes them from the code, so they are well-formed when the code is.

Nothing else is constrained: integers, gas, counters and the hashes of loaded cells are free. The
invariant only says what C++ guarantees by construction of its cells (`CellBuilder`,
`DataCell::create`, `CellSlice`), and the model's instructions keep it with the checks they make.
-/

namespace TvmLean

/-- A slice of a well-formed cell, its positions within the cell. -/
def Slice.WF (s : Slice) : Prop :=
  s.cell.WF ∧ s.bitPos ≤ s.cell.bits.size ∧ s.refPos ≤ s.cell.refs.size

mutual
  /-- Cells, slices and builders well-formed, in tuples and continuations too. -/
  inductive Value.WF : Value → Prop
    | int (i : IntVal) : Value.WF (.int i)
    | cell {c : Cell} : c.WF → Value.WF (.cell c)
    | slice {s : Slice} : s.WF → Value.WF (.slice s)
    | builder {b : Builder} : b.WF → Value.WF (.builder b)
    | tuple {t : Array Value} : (∀ v ∈ t, Value.WF v) → Value.WF (.tuple t)
    | cont {k : Continuation} : Continuation.WF k → Value.WF (.cont k)
    | null : Value.WF .null
    | nullCell : Value.WF .nullCell

  /-- The code of an ordinary continuation well-formed, and everything a continuation holds:
  the continuations it nests, its saved control registers and captured stack. -/
  inductive Continuation.WF : Continuation → Prop
    | ordinary {code : Slice} {saved : Continuation} {cregs : OrdCregs} {cdata : OrdCdata} :
        code.WF → Continuation.WF saved → OrdCregs.WF cregs → OrdCdata.WF cdata →
        Continuation.WF (.ordinary code saved cregs cdata)
    | envelope {ext : Continuation} {cregs : OrdCregs} {cdata : OrdCdata} :
        Continuation.WF ext → OrdCregs.WF cregs → OrdCdata.WF cdata →
        Continuation.WF (.envelope ext cregs cdata)
    | quit (n : Int) : Continuation.WF (.quit n)
    | excQuit : Continuation.WF .excQuit
    | whileCond {c b a : Continuation} :
        Continuation.WF c → Continuation.WF b → Continuation.WF a → Continuation.WF (.whileCond c b a)
    | whileBody {c b a : Continuation} :
        Continuation.WF c → Continuation.WF b → Continuation.WF a → Continuation.WF (.whileBody c b a)
    | untilBody {b a : Continuation} :
        Continuation.WF b → Continuation.WF a → Continuation.WF (.untilBody b a)
    | repeatBody {b a : Continuation} (n : Nat) :
        Continuation.WF b → Continuation.WF a → Continuation.WF (.repeatBody b a n)
    | againBody {b : Continuation} : Continuation.WF b → Continuation.WF (.againBody b)
    | pushInt (n : Int) {k : Continuation} : Continuation.WF k → Continuation.WF (.pushInt n k)

  /-- The control registers a continuation saves are well-formed. -/
  inductive OrdCregs.WF : OrdCregs → Prop
    | intro {cr : OrdCregs} :
        (∀ k, cr.c0 = some k → Continuation.WF k) →
        (∀ k, cr.c1 = some k → Continuation.WF k) →
        (∀ k, cr.c2 = some k → Continuation.WF k) →
        (∀ k, cr.c3 = some k → Continuation.WF k) →
        (∀ c, cr.c4 = some c → c.WF) →
        (∀ c, cr.c5 = some c → c.WF) →
        (∀ t, cr.c7 = some t → ∀ v ∈ t, Value.WF v) →
        OrdCregs.WF cr

  /-- The stack a continuation captured is well-formed. -/
  inductive OrdCdata.WF : OrdCdata → Prop
    | intro {cd : OrdCdata} : (∀ v ∈ cd.stack, Value.WF v) → OrdCdata.WF cd
end

/-- The registers c0..c5 and c7 well-formed. -/
structure Regs.WF (r : Regs) : Prop where
  c0 : r.c0.WF
  c1 : r.c1.WF
  c2 : r.c2.WF
  c3 : r.c3.WF
  c4 : r.c4.WF
  c5 : r.c5.WF
  c7 : ∀ v ∈ r.c7, v.WF

/-- A well-formed VM state: its stack, registers, current continuation, committed c4 and c5,
and library collections. -/
structure VmState.WF (st : VmState) : Prop where
  stack : ∀ v ∈ st.stack, v.WF
  regs : st.regs.WF
  cc : st.cc.WF
  committedC4 : st.cstate.c4.WF
  committedC5 : st.cstate.c5.WF
  libraries : ∀ c ∈ st.libraries, c.WF

/-- The cells and slices an instruction carries are well-formed. -/
def Instr.WF : Instr → Prop
  | .stSliceConst s => s.WF
  | .dictPushConst c _ => c.WF
  | .sdBeginsConst _ s => s.WF
  | .pushSliceConst s => s.WF
  | .pushCont s => s.WF
  | .pushRef c => c.WF
  | .pushRefSlice c => c.WF
  | .pushRefCont c => c.WF
  | .ifref s => s.WF
  | .ifnotref s => s.WF
  | .ifjmpref s => s.WF
  | .ifnotjmpref s => s.WF
  | .ifrefElse s => s.WF
  | .ifelseRef s => s.WF
  | .ifrefElseRef s t => s.WF ∧ t.WF
  | .callRef s => s.WF
  | .jmpRef s => s.WF
  | .jmpRefData s => s.WF
  | .dictExt (.pfxSwitch c _) => c.WF
  | .debugOp (.debugStr s) => s.WF
  | .contExt (.ifbitjmpref _ s) => s.WF
  | .contExt (.ifnbitjmpref _ s) => s.WF
  | .cellExt (.stRefConst c) => c.WF
  | .cellExt (.stRef2Const c d) => c.WF ∧ d.WF
  | _ => True

/-! ## Arrays all of whose elements satisfy a predicate -/

namespace WF

theorem forall_mem_pop {α} {P : α → Prop} {a : Array α} (h : ∀ v ∈ a, P v) : ∀ v ∈ a.pop, P v := by
  intro v hv
  apply h
  rw [Array.mem_def, Array.toList_pop] at hv
  rw [Array.mem_def]
  exact List.dropLast_subset _ hv

theorem forall_mem_extract {α} {P : α → Prop} {a : Array α} (h : ∀ v ∈ a, P v) (i j : Nat) :
    ∀ v ∈ a.extract i j, P v := by
  intro v hv
  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.mp hv
  exact h _ (Array.getElem_mem _)

theorem forall_mem_take {α} {P : α → Prop} {a : Array α} (h : ∀ v ∈ a, P v) (i : Nat) :
    ∀ v ∈ a.take i, P v := by
  rw [Array.take_eq_extract]; exact forall_mem_extract h 0 i

theorem forall_mem_setIfInBounds {α} {P : α → Prop} {a : Array α} (h : ∀ v ∈ a, P v) {x : α}
    (hx : P x) (i : Nat) : ∀ v ∈ a.setIfInBounds i x, P v := by
  intro v hv
  rcases Array.mem_or_eq_of_mem_setIfInBounds hv with hv | rfl
  · exact h v hv
  · exact hx

theorem forall_mem_set! {α} {P : α → Prop} {a : Array α} (h : ∀ v ∈ a, P v) {x : α}
    (hx : P x) (i : Nat) : ∀ v ∈ a.set! i x, P v := by
  rw [Array.set!_eq_setIfInBounds]; exact forall_mem_setIfInBounds h hx i

theorem getElem!_of_forall {α} [Inhabited α] {P : α → Prop} {a : Array α} (h : ∀ v ∈ a, P v)
    (hd : P default) (i : Nat) : P a[i]! := by
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  split
  · exact h _ (Array.getElem_mem _)
  · exact hd

theorem getElem?_of_forall {α} {P : α → Prop} {a : Array α} (h : ∀ v ∈ a, P v) {i : Nat} {x : α}
    (hx : a[i]? = some x) : P x :=
  h x (Array.mem_of_getElem? hx)

theorem back_of_forall {α} {P : α → Prop} {a : Array α} (h : ∀ v ∈ a, P v) (hs : 0 < a.size) :
    P (a.back hs) :=
  h _ (Array.back_mem hs)

theorem mem_of_mem_pop {α} {a : Array α} {v : α} (h : v ∈ a.pop) : v ∈ a :=
  forall_mem_pop (P := (· ∈ a)) (fun _ h => h) v h

theorem mem_of_mem_extract {α} {a : Array α} {v : α} {i j : Nat} (h : v ∈ a.extract i j) : v ∈ a :=
  forall_mem_extract (P := (· ∈ a)) (fun _ h => h) i j v h

theorem mem_of_mem_take {α} {a : Array α} {v : α} {i : Nat} (h : v ∈ a.take i) : v ∈ a :=
  forall_mem_take (P := (· ∈ a)) (fun _ h => h) i v h

theorem mem_or_eq_of_mem_set! {α} {a : Array α} {v x : α} {i : Nat} (h : v ∈ a.set! i x) :
    v ∈ a ∨ v = x := by
  rw [Array.set!_eq_setIfInBounds] at h; exact Array.mem_or_eq_of_mem_setIfInBounds h

theorem getElem!_mem_or_default {α} [Inhabited α] (a : Array α) (i : Nat) :
    a[i]! ∈ a ∨ a[i]! = default := by
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  split
  · exact .inl (Array.getElem_mem _)
  · exact .inr rfl

end WF

/-! ## Cells -/

theorem Cell.WF.bits_le {c : Cell} (h : c.WF) : c.bits.size ≤ 1023 := by
  cases h; assumption

theorem Cell.WF.refs_le {c : Cell} (h : c.WF) : c.refs.size ≤ 4 := by
  cases h; assumption

theorem Cell.WF.refs_wf {c : Cell} (h : c.WF) : ∀ r ∈ c.refs, r.WF := by
  cases h; assumption

theorem Cell.wf_iff (c : Cell) :
    c.WF ↔ c.bits.size ≤ 1023 ∧ c.refs.size ≤ 4 ∧ ∀ r ∈ c.refs, r.WF :=
  ⟨fun h => ⟨h.bits_le, h.refs_le, h.refs_wf⟩, fun ⟨h1, h2, h3⟩ => .intro c h1 h2 h3⟩

theorem Cell.mkOrdinary_WF {bits : BitString} {refs : Array Cell} (hb : bits.size ≤ 1023)
    (hr : refs.size ≤ 4) (hc : ∀ r ∈ refs, r.WF) : (Cell.mkOrdinary bits refs).WF :=
  .intro _ hb hr hc

@[simp] theorem Cell.empty_WF : Cell.empty.WF :=
  Cell.mkOrdinary_WF (by decide) (by decide) (by simp)

theorem Cell.default_WF : (default : Cell).WF := Cell.empty_WF

/-- Any reference of a well-formed cell, `[i]!` included (out of range it is the empty cell). -/
theorem Cell.WF.ref! {c : Cell} (h : c.WF) (i : Nat) : (c.refs[i]!).WF :=
  WF.getElem!_of_forall h.refs_wf Cell.default_WF i

@[simp] theorem natToBits_size (n bits : Nat) : (natToBits n bits).size = bits := by
  simp [natToBits]

theorem Cell.ofUInt_WF {bits n : Nat} (h : bits ≤ 1023) : (Cell.ofUInt bits n).WF :=
  Cell.mkOrdinary_WF (by simp [natToBits]; exact h) (by simp) (by simp)

/-! ## Slices -/

@[simp] theorem Slice.ofCell_WF_iff {c : Cell} : (Slice.ofCell c).WF ↔ c.WF := by
  simp [Slice.WF, Slice.ofCell]

theorem Slice.ofCell_WF {c : Cell} (h : c.WF) : (Slice.ofCell c).WF := Slice.ofCell_WF_iff.mpr h

theorem Slice.WF.cell_wf {s : Slice} (h : s.WF) : s.cell.WF := h.1

theorem Slice.WF.bitPos_le {s : Slice} (h : s.WF) : s.bitPos ≤ s.cell.bits.size := h.2.1

theorem Slice.WF.refPos_le {s : Slice} (h : s.WF) : s.refPos ≤ s.cell.refs.size := h.2.2

theorem Slice.haveBits_iff (s : Slice) (n : Nat) :
    s.haveBits n = true ↔ s.bitPos + n ≤ s.cell.bits.size := by
  simp [Slice.haveBits]

theorem Slice.haveRefs_iff (s : Slice) (n : Nat) :
    s.haveRefs n = true ↔ s.refPos + n ≤ s.cell.refs.size := by
  simp [Slice.haveRefs]

/-- Advancing within the bits keeps a slice well-formed. -/
theorem Slice.advanceBits_WF {s : Slice} (h : s.WF) {n : Nat} (hn : s.bitPos + n ≤ s.cell.bits.size) :
    (s.advanceBits n).WF :=
  ⟨h.1, by simp [Slice.advanceBits]; omega, h.2.2⟩

theorem Slice.advanceBits_WF' {s : Slice} (h : s.WF) {n : Nat} (hn : s.haveBits n = true) :
    (s.advanceBits n).WF :=
  Slice.advanceBits_WF h ((Slice.haveBits_iff s n).mp hn)

/-- Moving the reference position within the references keeps a slice well-formed. -/
theorem Slice.withRefPos_WF {s : Slice} (h : s.WF) {n : Nat} (hn : n ≤ s.cell.refs.size) :
    ({ s with refPos := n } : Slice).WF :=
  ⟨h.1, h.2.1, hn⟩

theorem Slice.withBitPos_WF {s : Slice} (h : s.WF) {n : Nat} (hn : n ≤ s.cell.bits.size) :
    ({ s with bitPos := n } : Slice).WF :=
  ⟨h.1, hn, h.2.2⟩

theorem Slice.readBits_size_le {s : Slice} (h : s.WF) (n : Nat) : (s.readBits n).size ≤ 1023 := by
  have := h.1.bits_le
  simp [Slice.readBits]; omega

theorem Slice.WF.ref! {s : Slice} (h : s.WF) (i : Nat) : (s.cell.refs[i]!).WF := h.1.ref! i

/-- The rest of a well-formed slice is a well-formed cell. -/
theorem Slice.toCellRemaining_WF {s : Slice} (h : s.WF) : s.toCellRemaining.WF := by
  have hb := h.1.bits_le
  have hr := h.1.refs_le
  refine Cell.mkOrdinary_WF ?_ ?_ ?_
  · simp; omega
  · simp; omega
  · exact WF.forall_mem_extract h.1.refs_wf _ _

theorem Slice.takeRefCell_WF {s : Slice} (h : s.WF) {c : Cell} {s' : Slice}
    (ht : s.takeRefCell = .ok (c, s')) : c.WF ∧ s'.WF := by
  unfold Slice.takeRefCell at ht
  split at ht
  · rename_i hr
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨h.ref! _, Slice.withRefPos_WF h ((Slice.haveRefs_iff s 1).mp hr)⟩
  · cases ht

/-! ## Builders -/

theorem Builder.WF.bits_le {b : Builder} (h : b.WF) : b.bits.size ≤ 1023 := h.1
theorem Builder.WF.refs_le {b : Builder} (h : b.WF) : b.refs.size ≤ 4 := h.2.1
theorem Builder.WF.refs_wf {b : Builder} (h : b.WF) : ∀ r ∈ b.refs, r.WF := h.2.2

/-- Appending a builder that fits (`canExtendBy`) keeps a builder well-formed. -/
theorem Builder.append_WF {b c : Builder} (hb : b.WF) (hc : c.WF)
    (h : b.canExtendBy c.bits.size c.refs.size = true) :
    ({ bits := b.bits ++ c.bits, refs := b.refs ++ c.refs } : Builder).WF := by
  rw [Builder.canExtendBy_iff] at h
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  simp only [Array.forall_mem_append]
  exact ⟨hb.refs_wf, hc.refs_wf⟩

/-- Storing bits that fit keeps a builder well-formed. -/
theorem Builder.storeBits_WF' {b : Builder} {bs : BitString} (hb : b.WF)
    (h : b.bits.size + bs.size ≤ 1023) : (b.storeBits bs).WF :=
  ⟨by simp [Builder.storeBits]; omega, hb.2.1, hb.2.2⟩

/-- Storing a well-formed reference that fits keeps a builder well-formed. -/
theorem Builder.pushRef_WF' {b : Builder} {c : Cell} (hb : b.WF) (hc : c.WF)
    (h : b.refs.size + 1 ≤ 4) : ({ b with refs := b.refs.push c } : Builder).WF := by
  refine ⟨hb.1, by simp; omega, ?_⟩
  simp only [Array.forall_mem_push]
  exact ⟨hc, hb.refs_wf⟩

/-! ## Values and continuations -/

@[simp] theorem Value.wf_int (i : IntVal) : (Value.int i).WF ↔ True :=
  ⟨fun _ => trivial, fun _ => .int i⟩
@[simp] theorem Value.wf_cell (c : Cell) : (Value.cell c).WF ↔ c.WF :=
  ⟨fun h => by cases h; assumption, .cell⟩
@[simp] theorem Value.wf_slice (s : Slice) : (Value.slice s).WF ↔ s.WF :=
  ⟨fun h => by cases h; assumption, .slice⟩
@[simp] theorem Value.wf_builder (b : Builder) : (Value.builder b).WF ↔ b.WF :=
  ⟨fun h => by cases h; assumption, .builder⟩
@[simp] theorem Value.wf_tuple (t : Array Value) : (Value.tuple t).WF ↔ ∀ v ∈ t, v.WF :=
  ⟨fun h => by cases h; assumption, .tuple⟩
@[simp] theorem Value.wf_cont (k : Continuation) : (Value.cont k).WF ↔ k.WF :=
  ⟨fun h => by cases h; assumption, .cont⟩
@[simp] theorem Value.wf_null : Value.null.WF ↔ True := ⟨fun _ => trivial, fun _ => .null⟩
@[simp] theorem Value.wf_nullCell : Value.nullCell.WF ↔ True :=
  ⟨fun _ => trivial, fun _ => .nullCell⟩

theorem Value.default_WF : (default : Value).WF := Value.WF.null

@[simp] theorem Continuation.wf_ordinary (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (cdata : OrdCdata) :
    (Continuation.ordinary code saved cregs cdata).WF ↔ code.WF ∧ saved.WF ∧ cregs.WF ∧ cdata.WF :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩, fun ⟨h1, h2, h3, h4⟩ => .ordinary h1 h2 h3 h4⟩
@[simp] theorem Continuation.wf_envelope (ext : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) :
    (Continuation.envelope ext cregs cdata).WF ↔ ext.WF ∧ cregs.WF ∧ cdata.WF :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›, ‹_›⟩, fun ⟨h1, h2, h3⟩ => .envelope h1 h2 h3⟩
@[simp] theorem Continuation.wf_quit (n : Int) : (Continuation.quit n).WF ↔ True :=
  ⟨fun _ => trivial, fun _ => .quit n⟩
@[simp] theorem Continuation.wf_excQuit : Continuation.excQuit.WF ↔ True :=
  ⟨fun _ => trivial, fun _ => .excQuit⟩
@[simp] theorem Continuation.wf_whileCond (c b a : Continuation) :
    (Continuation.whileCond c b a).WF ↔ c.WF ∧ b.WF ∧ a.WF :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›, ‹_›⟩, fun ⟨h1, h2, h3⟩ => .whileCond h1 h2 h3⟩
@[simp] theorem Continuation.wf_whileBody (c b a : Continuation) :
    (Continuation.whileBody c b a).WF ↔ c.WF ∧ b.WF ∧ a.WF :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›, ‹_›⟩, fun ⟨h1, h2, h3⟩ => .whileBody h1 h2 h3⟩
@[simp] theorem Continuation.wf_untilBody (b a : Continuation) :
    (Continuation.untilBody b a).WF ↔ b.WF ∧ a.WF :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›⟩, fun ⟨h1, h2⟩ => .untilBody h1 h2⟩
@[simp] theorem Continuation.wf_repeatBody (b a : Continuation) (n : Nat) :
    (Continuation.repeatBody b a n).WF ↔ b.WF ∧ a.WF :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›⟩, fun ⟨h1, h2⟩ => .repeatBody n h1 h2⟩
@[simp] theorem Continuation.wf_againBody (b : Continuation) :
    (Continuation.againBody b).WF ↔ b.WF :=
  ⟨fun h => by cases h; assumption, .againBody⟩
@[simp] theorem Continuation.wf_pushInt (n : Int) (k : Continuation) :
    (Continuation.pushInt n k).WF ↔ k.WF :=
  ⟨fun h => by cases h; assumption, .pushInt n⟩

theorem OrdCregs.wf_iff (cr : OrdCregs) : cr.WF ↔
    (∀ k, cr.c0 = some k → k.WF) ∧ (∀ k, cr.c1 = some k → k.WF) ∧
    (∀ k, cr.c2 = some k → k.WF) ∧ (∀ k, cr.c3 = some k → k.WF) ∧
    (∀ c, cr.c4 = some c → c.WF) ∧ (∀ c, cr.c5 = some c → c.WF) ∧
    (∀ t, cr.c7 = some t → ∀ v ∈ t, v.WF) :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩,
   fun ⟨h0, h1, h2, h3, h4, h5, h7⟩ => .intro h0 h1 h2 h3 h4 h5 h7⟩

@[simp] theorem OrdCdata.wf_iff (cd : OrdCdata) : cd.WF ↔ ∀ v ∈ cd.stack, v.WF :=
  ⟨fun h => by cases h; assumption, .intro⟩

@[simp] theorem OrdCregs.empty_WF : OrdCregs.empty.WF := by
  rw [OrdCregs.wf_iff]; simp [OrdCregs.empty]

@[simp] theorem OrdCdata.empty_WF : OrdCdata.empty.WF := by
  simp [OrdCdata.empty]

/-! ## Registers and states -/

theorem Regs.wf_iff (r : Regs) : r.WF ↔
    r.c0.WF ∧ r.c1.WF ∧ r.c2.WF ∧ r.c3.WF ∧ r.c4.WF ∧ r.c5.WF ∧ ∀ v ∈ r.c7, v.WF :=
  ⟨fun h => ⟨h.c0, h.c1, h.c2, h.c3, h.c4, h.c5, h.c7⟩,
   fun ⟨h0, h1, h2, h3, h4, h5, h7⟩ => ⟨h0, h1, h2, h3, h4, h5, h7⟩⟩

theorem Regs.initial_WF : Regs.initial.WF := by
  simp [Regs.wf_iff, Regs.initial]

theorem VmState.wf_iff (st : VmState) : st.WF ↔
    (∀ v ∈ st.stack, v.WF) ∧ st.regs.WF ∧ st.cc.WF ∧ st.cstate.c4.WF ∧ st.cstate.c5.WF ∧
      ∀ c ∈ st.libraries, c.WF :=
  ⟨fun h => ⟨h.stack, h.regs, h.cc, h.committedC4, h.committedC5, h.libraries⟩,
   fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

/-- A state is well-formed if one is and the fields the invariant reads agree. -/
theorem VmState.WF.of_eq {st st' : VmState} (h : st.WF) (hs : st'.stack = st.stack)
    (hr : st'.regs = st.regs) (hc : st'.cc = st.cc) (hk : st'.cstate = st.cstate)
    (hl : st'.libraries = st.libraries) : st'.WF := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨hs ▸ h1, hr ▸ h2, hc ▸ h3, hk ▸ h4, hk ▸ h5, hl ▸ h6⟩

theorem VmState.WF.withStack {st : VmState} (h : st.WF) {s : Stack} (hs : ∀ v ∈ s, v.WF) :
    ({ st with stack := s } : VmState).WF :=
  ⟨hs, h.regs, h.cc, h.committedC4, h.committedC5, h.libraries⟩

theorem VmState.WF.withRegs {st : VmState} (h : st.WF) {r : Regs} (hr : r.WF) :
    ({ st with regs := r } : VmState).WF :=
  ⟨h.stack, hr, h.cc, h.committedC4, h.committedC5, h.libraries⟩

theorem VmState.WF.withCc {st : VmState} (h : st.WF) {k : Continuation} (hk : k.WF) :
    ({ st with cc := k } : VmState).WF :=
  ⟨h.stack, h.regs, hk, h.committedC4, h.committedC5, h.libraries⟩

theorem VmState.WF.withGas {st : VmState} (h : st.WF) (g : GasLimits) :
    ({ st with gas := g } : VmState).WF :=
  ⟨h.stack, h.regs, h.cc, h.committedC4, h.committedC5, h.libraries⟩

theorem VmState.WF.consumeGas {st : VmState} (h : st.WF) (n : Int) : (st.consumeGas n).WF :=
  h.withGas _

theorem VmState.initial_WF {code : Cell} (h : code.WF) (gasLimit gasMax gasCredit : Int) :
    (VmState.initial code gasLimit gasMax gasCredit).WF := by
  refine ⟨by simp [VmState.initial], Regs.initial_WF, ?_, ?_, ?_, by simp [VmState.initial]⟩
  · simp [VmState.initial, Slice.ofCell_WF h, OrdCdata.empty]
  · simp [VmState.initial, CommittedState.empty]
  · simp [VmState.initial, CommittedState.empty]

end TvmLean

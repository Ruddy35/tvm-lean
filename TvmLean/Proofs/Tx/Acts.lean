import TvmLean.Proofs.Tx.NoSetCode
import TvmLean.Proofs.Exec.Spec.Actions

/-!
# Action lists with code changes

`SafeActs` (TvmLean/Proofs/Tx/NoSetCode.lean) admits `SENDRAWMSG` and `RAWRESERVE` actions only, so
that a contract checked with it never changes its code. `Acts K c5`: the action list `c5` is made,
from the empty list, of the actions the instructions of the model install (as their specifications
write them: `SENDRAWMSG` and `SENDMSG`, `OutAction.sendMsg`; `RAWRESERVE` and `RAWRESERVEX`,
`OutAction.reserve` and `OutAction.reserveExtra`; `SETCODE`, `OutAction.setCode`; `SETLIBCODE` and
`CHANGELIB`, `OutAction.setLibCode` and `OutAction.changeLib`), each `SETCODE` with a code satisfying
`K`. What the action phase makes of such a list (`ActionIn`, as `parseOutAction` reads the nodes):
every `SETCODE` action in it installs a code satisfying `K` (`Acts.setCode_of_actionIn`); with `K`
false there is none (`Acts.noSetCode`). A list of `SafeActs` is one of `Acts K` (`SafeActs.acts`).
-/

namespace TvmLean.Tx

/-- The nodes of the list with an action added whose first reference is the list before: after the
first, the nodes of the list before. -/
theorem actionNode_succ_of_ref0 (x prev : Cell) (h : x.refs[0]! = prev) :
    ∀ i, actionNode x (i + 1) = actionNode prev i
  | 0 => h
  | i + 1 => by rw [actionNode_succ, actionNode_succ_of_ref0 x prev h i, ← actionNode_succ]

/-- The tag of an action read after its first reference. -/
theorem uint32_setCode (prev code : Cell) :
    Reader.uint 32 { cell := TvmLean.OutAction.setCode prev code, bitPos := 0, refPos := 1 } =
      some (0xad4de08e, { cell := TvmLean.OutAction.setCode prev code, bitPos := 32, refPos := 1 }) := by
  have h1 : (natToBits 0xad4de08e 32).extract 0 32 = natToBits 0xad4de08e 32 :=
    Array.extract_eq_self_of_le (by simp [natToBits_size])
  have h2 : bitsToNat (natToBits 0xad4de08e 32) = 0xad4de08e := by decide
  simp only [Reader.uint, bind, StateT.bind, pure, StateT.pure]
  simp only [Reader.bits, Slice.haveBits, Slice.readBits, Slice.advanceBits, TvmLean.OutAction.setCode,
    Cell.mkOrdinary, Nat.zero_add, h1]
  simp [h2, natToBits_size]

theorem uint32_reserveExtra (m x : Nat) (prev e : Cell) :
    Reader.uint 32 { cell := TvmLean.OutAction.reserveExtra m x prev e, bitPos := 0, refPos := 1 } =
      some (0x36e6b809, { cell := TvmLean.OutAction.reserveExtra m x prev e, bitPos := 32, refPos := 1 }) := by
  have h2 : bitsToNat (natToBits 0x36e6b809 32) = 0x36e6b809 := by decide
  simp only [Reader.uint, bind, StateT.bind, pure, StateT.pure]
  simp only [Reader.bits, Slice.haveBits, Slice.readBits, Slice.advanceBits, TvmLean.OutAction.reserveExtra,
    Cell.mkOrdinary, Array.append_assoc, Nat.zero_add]
  rw [extract_append_32 _ _ (natToBits_size _ _)]
  simp [h2]

theorem uint32_setLibCode (m : Nat) (prev code : Cell) :
    Reader.uint 32 { cell := TvmLean.OutAction.setLibCode m prev code, bitPos := 0, refPos := 1 } =
      some (0x26fa1dd4, { cell := TvmLean.OutAction.setLibCode m prev code, bitPos := 32, refPos := 1 }) := by
  have h1 : (natToBits 0x26fa1dd4 32 ++ natToBits (m * 2 + 1) 8).extract 0 (0 + 32) = natToBits 0x26fa1dd4 32 :=
    extract_append_32 _ _ (natToBits_size _ _)
  have h2 : bitsToNat (natToBits 0x26fa1dd4 32) = 0x26fa1dd4 := by decide
  simp only [Reader.uint, bind, StateT.bind, pure, StateT.pure]
  simp only [Reader.bits, Slice.haveBits, Slice.readBits, Slice.advanceBits, TvmLean.OutAction.setLibCode,
    Cell.mkOrdinary, h1]
  simp [h2]

theorem uint32_changeLib (m : Nat) (prev : Cell) (h : Nat) :
    Reader.uint 32 { cell := TvmLean.OutAction.changeLib m prev h, bitPos := 0, refPos := 1 } =
      some (0x26fa1dd4, { cell := TvmLean.OutAction.changeLib m prev h, bitPos := 32, refPos := 1 }) := by
  have h2 : bitsToNat (natToBits 0x26fa1dd4 32) = 0x26fa1dd4 := by decide
  simp only [Reader.uint, bind, StateT.bind, pure, StateT.pure]
  simp only [Reader.bits, Slice.haveBits, Slice.readBits, Slice.advanceBits, TvmLean.OutAction.changeLib,
    Cell.mkOrdinary, Array.append_assoc, Nat.zero_add]
  rw [extract_append_32 _ _ (natToBits_size _ _)]
  simp [h2]

/-- The node `SETCODE` adds parses as `SETCODE` of its code. -/
theorem parseOutAction_setCode (prev code : Cell) :
    parseOutAction (TvmLean.OutAction.setCode prev code) = some (.setCode code) := by
  unfold parseOutAction
  simp only [Slice.ofCell]
  simp only [uint32_setCode]
  simp [TvmLean.OutAction.setCode, Cell.mkOrdinary, Slice.haveRefs, Reader.ref, Slice.bitsRemaining,
    Slice.refsRemaining, natToBits_size]

/-- A node that `RAWRESERVEX` adds with extra currencies never parses as `SETCODE`. -/
theorem parseOutAction_reserveExtra (m x : Nat) (prev e c : Cell) :
    parseOutAction (TvmLean.OutAction.reserveExtra m x prev e) ≠ some (.setCode c) := by
  intro h
  unfold parseOutAction at h
  simp only [Slice.ofCell] at h
  simp only [uint32_reserveExtra] at h
  simp [TvmLean.OutAction.reserveExtra, Cell.mkOrdinary, Slice.haveRefs, Option.bind_eq_some_iff] at h

/-- A node that `SETLIBCODE` adds never parses as `SETCODE`. -/
theorem parseOutAction_setLibCode (m : Nat) (prev code c : Cell) :
    parseOutAction (TvmLean.OutAction.setLibCode m prev code) ≠ some (.setCode c) := by
  intro h
  unfold parseOutAction at h
  simp only [Slice.ofCell] at h
  simp only [uint32_setLibCode] at h
  simp [TvmLean.OutAction.setLibCode, Cell.mkOrdinary, Slice.haveRefs, Option.bind_eq_some_iff] at h

/-- A node that `CHANGELIB` adds never parses as `SETCODE`. -/
theorem parseOutAction_changeLib (m : Nat) (prev : Cell) (hh : Nat) (c : Cell) :
    parseOutAction (TvmLean.OutAction.changeLib m prev hh) ≠ some (.setCode c) := by
  intro h
  unfold parseOutAction at h
  simp only [Slice.ofCell] at h
  simp only [uint32_changeLib] at h
  simp [TvmLean.OutAction.changeLib, Cell.mkOrdinary, Slice.haveRefs, Option.bind_eq_some_iff] at h

end TvmLean.Tx

namespace TvmLean

/-- An action list made, from the empty list, of the actions the instructions of the model install,
every `SETCODE` with a code satisfying `K`. -/
inductive Acts (K : Cell → Prop) : Cell → Prop
  | empty : Acts K Cell.empty
  | send {prev : Cell} (mode : Nat) (msg : Cell) : Acts K prev → Acts K (OutAction.sendMsg mode prev msg)
  | reserve {prev : Cell} (mode x : Nat) : Acts K prev → Acts K (OutAction.reserve mode x prev)
  | reserveExtra {prev : Cell} (mode x : Nat) (extra : Cell) : Acts K prev →
      Acts K (OutAction.reserveExtra mode x prev extra)
  | setCode {prev : Cell} (code : Cell) : Acts K prev → K code → Acts K (OutAction.setCode prev code)
  | setLibCode {prev : Cell} (mode : Nat) (code : Cell) : Acts K prev →
      Acts K (OutAction.setLibCode mode prev code)
  | changeLib {prev : Cell} (mode hash : Nat) : Acts K prev → Acts K (OutAction.changeLib mode prev hash)

/-- An action list that is not `SETCODE` at its first node and whose first reference is `prev`: a
`SETCODE` in it is one of `prev`. -/
theorem Tx.actionIn_setCode_tail {x prev c : Cell} (h0 : Tx.parseOutAction x ≠ some (.setCode c))
    (href : x.refs[0]! = prev) (h : Tx.ActionIn x (.setCode c)) : Tx.ActionIn prev (.setCode c) := by
  obtain ⟨i, hi, hp⟩ := h
  cases i with
  | zero => exact absurd hp h0
  | succ k =>
    rw [Tx.actionNode_succ_of_ref0 x prev href] at hp
    refine ⟨k, fun j hj => ?_, hp⟩
    have := hi (j + 1) (by omega)
    rwa [Tx.actionNode_succ_of_ref0 x prev href] at this

/-- **A `SETCODE` of an action list of `Acts K` installs a code satisfying `K`.** -/
theorem Acts.setCode_of_actionIn {K : Cell → Prop} {c5 c : Cell} (h : Acts K c5)
    (hin : Tx.ActionIn c5 (.setCode c)) : K c := by
  induction h with
  | empty =>
    obtain ⟨i, hi, _⟩ := hin
    exact absurd ⟨rfl, rfl⟩ (hi 0 (Nat.zero_le _))
  | send m msg _ ih => exact ih (Tx.actionIn_setCode_tail (Tx.parseOutAction_sendMsg m _ msg c) rfl hin)
  | reserve m x _ ih => exact ih (Tx.actionIn_setCode_tail (Tx.parseOutAction_reserve m x _ c) rfl hin)
  | reserveExtra m x e _ ih =>
    exact ih (Tx.actionIn_setCode_tail (Tx.parseOutAction_reserveExtra m x _ e c) rfl hin)
  | @setCode prev code _ hk ih =>
    obtain ⟨i, hi, hp⟩ := hin
    cases i with
    | zero =>
      rw [Tx.actionNode_zero, Tx.parseOutAction_setCode] at hp
      cases hp
      exact hk
    | succ k =>
      rw [Tx.actionNode_succ_of_ref0 _ prev rfl] at hp
      refine ih ⟨k, fun j hj => ?_, hp⟩
      have := hi (j + 1) (by omega)
      rwa [Tx.actionNode_succ_of_ref0 _ prev rfl] at this
  | setLibCode m code _ ih =>
    exact ih (Tx.actionIn_setCode_tail (Tx.parseOutAction_setLibCode m _ code c) rfl hin)
  | changeLib m hash _ ih => exact ih (Tx.actionIn_setCode_tail (Tx.parseOutAction_changeLib m _ hash c) rfl hin)

/-- An action list of `Acts` whose `SETCODE`s are excluded has none. -/
theorem Acts.noSetCode {c5 : Cell} (h : Acts (fun _ => False) c5) : Tx.NoSetCode c5 :=
  fun _ hin => h.setCode_of_actionIn hin

/-- A list of `SENDRAWMSG` and `RAWRESERVE` actions is one of `Acts K`, whatever `K`. -/
theorem SafeActs.acts {K : Cell → Prop} {c5 : Cell} (h : SafeActs c5) : Acts K c5 := by
  induction h with
  | empty => exact Acts.empty
  | send m msg _ ih => exact Acts.send m msg ih
  | reserve m x _ ih => exact Acts.reserve m x ih

/-- `Acts` for a weaker condition on the codes. -/
theorem Acts.mono {K K' : Cell → Prop} (hk : ∀ c, K c → K' c) {c5 : Cell} (h : Acts K c5) : Acts K' c5 := by
  induction h with
  | empty => exact Acts.empty
  | send m msg _ ih => exact Acts.send m msg ih
  | reserve m x _ ih => exact Acts.reserve m x ih
  | reserveExtra m x e _ ih => exact Acts.reserveExtra m x e ih
  | setCode code _ hc ih => exact Acts.setCode code ih (hk code hc)
  | setLibCode m code _ ih => exact Acts.setLibCode m code ih
  | changeLib m hash _ ih => exact Acts.changeLib m hash ih

end TvmLean

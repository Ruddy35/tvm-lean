import TvmLean.Proofs.Tx.ActionPhase
import TvmLean.Proofs.Exec.Spec.Msg
import TvmLean.Proofs.Contracts.Wallet3Run.Tactic

/-!
# Action lists without `SETCODE`

`NoSetCode c5`: the action list `c5` has no `SETCODE` action (`ActionIn`, as the action phase reads
it). An action `SENDRAWMSG` or `RAWRESERVE` adds (`OutAction.sendMsg`, `OutAction.reserve`,
TvmLean/Proofs/Exec/Spec/Msg.lean) never reads as `SETCODE` (its tag is that of `action_send_msg` or
`action_reserve_currency`), so a list of such actions, from the empty list, has none:
`SendList.noSetCode`, `SafeActs.noSetCode`. The obligation of `Reachable.code_fixed` asks for it of
every committed action list.
-/

namespace TvmLean.Tx

/-! ## Action lists of `SENDRAWMSG` actions have no `SETCODE` -/

/-- The action list `c5` has no `SETCODE` action. -/
def NoSetCode (c5 : Cell) : Prop := ∀ c, ¬ActionIn c5 (.setCode c)

/-- The nodes of the list with a `SENDRAWMSG` action added (`TvmLean.OutAction.sendMsg`): after the
first, the nodes of the list before. -/
theorem actionNode_sendMsg_succ (m : Nat) (prev msg : Cell) :
    ∀ i, actionNode (TvmLean.OutAction.sendMsg m prev msg) (i + 1) = actionNode prev i
  | 0 => rfl
  | i + 1 => by rw [actionNode_succ, actionNode_sendMsg_succ m prev msg i, ← actionNode_succ]

theorem extract_append_32 (a b : BitString) (h : a.size = 32) : (a ++ b).extract 0 32 = a := by
  rw [Array.extract_append]
  simp [h]

/-- The tag of a `SENDRAWMSG` action (`action_send_msg#0ec3c86d`), read after its first reference. -/
theorem uint32_sendMsg (m : Nat) (prev msg : Cell) :
    Reader.uint 32 { cell := TvmLean.OutAction.sendMsg m prev msg, bitPos := 0, refPos := 1 } =
      some (0x0ec3c86d, { cell := TvmLean.OutAction.sendMsg m prev msg, bitPos := 32, refPos := 1 }) := by
  have h1 : (natToBits 0x0ec3c86d 32 ++ natToBits m 8).extract 0 (0 + 32) = natToBits 0x0ec3c86d 32 :=
    extract_append_32 _ _ (natToBits_size _ _)
  have h2 : bitsToNat (natToBits 0x0ec3c86d 32) = 0x0ec3c86d := by decide
  simp only [Reader.uint, bind, StateT.bind, pure, StateT.pure]
  simp only [Reader.bits, Slice.haveBits, Slice.readBits, Slice.advanceBits, TvmLean.OutAction.sendMsg,
    Cell.mkOrdinary, h1]
  simp [h2]

/-- A node that `SENDRAWMSG` adds never parses as `SETCODE` (`parseOutAction`: its tag is that of
`action_send_msg`). -/
theorem parseOutAction_sendMsg (m : Nat) (prev msg c : Cell) :
    parseOutAction (TvmLean.OutAction.sendMsg m prev msg) ≠ some (.setCode c) := by
  intro h
  unfold parseOutAction at h
  simp only [Slice.ofCell] at h
  simp only [uint32_sendMsg] at h
  simp [TvmLean.OutAction.sendMsg, Cell.mkOrdinary, Slice.haveRefs, Option.bind_eq_some_iff] at h

/-- The empty action list has no action. -/
theorem noSetCode_empty : NoSetCode Cell.empty := by
  rintro c ⟨i, hi, _⟩
  exact hi 0 (Nat.zero_le _) ⟨rfl, rfl⟩

/-- A `SENDRAWMSG` action added to a list without `SETCODE` leaves a list without `SETCODE`. -/
theorem noSetCode_sendMsg {prev : Cell} (h : NoSetCode prev) (m : Nat) (msg : Cell) :
    NoSetCode (TvmLean.OutAction.sendMsg m prev msg) := by
  rintro c ⟨i, hi, hp⟩
  cases i with
  | zero => exact parseOutAction_sendMsg m prev msg c hp
  | succ k =>
    rw [actionNode_sendMsg_succ] at hp
    refine h c ⟨k, fun j hj => ?_, hp⟩
    have := hi (j + 1) (by omega)
    rwa [actionNode_sendMsg_succ] at this

end TvmLean.Tx

namespace TvmLean

/-- **An action list of `SENDRAWMSG` actions has no `SETCODE`.** -/
theorem SendList.noSetCode {c5 : Cell} (h : SendList c5) : Tx.NoSetCode c5 := by
  induction h with
  | empty => exact Tx.noSetCode_empty
  | send m msg _ ih => exact Tx.noSetCode_sendMsg ih m msg

end TvmLean

namespace TvmLean.Tx

/-! ## Action lists of `SENDRAWMSG` and `RAWRESERVE` actions have no `SETCODE` -/

/-- The nodes of the list with a `RAWRESERVE` action added: after the first, those of the list. -/
theorem actionNode_reserve_succ (m x : Nat) (prev : Cell) :
    ∀ i, actionNode (TvmLean.OutAction.reserve m x prev) (i + 1) = actionNode prev i
  | 0 => rfl
  | i + 1 => by rw [actionNode_succ, actionNode_reserve_succ m x prev i, ← actionNode_succ]

/-- The tag of a `RAWRESERVE` action (`action_reserve_currency#36e6b809`), read after its first
reference. -/
theorem uint32_reserve (m x : Nat) (prev : Cell) :
    Reader.uint 32 { cell := TvmLean.OutAction.reserve m x prev, bitPos := 0, refPos := 1 } =
      some (0x36e6b809, { cell := TvmLean.OutAction.reserve m x prev, bitPos := 32, refPos := 1 }) := by
  have h2 : bitsToNat (natToBits 0x36e6b809 32) = 0x36e6b809 := by decide
  simp only [Reader.uint, bind, StateT.bind, pure, StateT.pure]
  simp only [Reader.bits, Slice.haveBits, Slice.readBits, Slice.advanceBits, TvmLean.OutAction.reserve,
    Cell.mkOrdinary, Array.append_assoc, Nat.zero_add]
  rw [extract_append_32 _ _ (natToBits_size _ _)]
  simp [h2]

/-- A node that `RAWRESERVE` adds never parses as `SETCODE`. -/
theorem parseOutAction_reserve (m x : Nat) (prev c : Cell) :
    parseOutAction (TvmLean.OutAction.reserve m x prev) ≠ some (.setCode c) := by
  intro h
  unfold parseOutAction at h
  simp only [Slice.ofCell] at h
  simp only [uint32_reserve] at h
  simp [TvmLean.OutAction.reserve, Cell.mkOrdinary, Slice.haveRefs, Option.bind_eq_some_iff] at h

/-- A `RAWRESERVE` action added to a list without `SETCODE` leaves a list without `SETCODE`. -/
theorem noSetCode_reserve {prev : Cell} (h : NoSetCode prev) (m x : Nat) :
    NoSetCode (TvmLean.OutAction.reserve m x prev) := by
  rintro c ⟨i, hi, hp⟩
  cases i with
  | zero => exact parseOutAction_reserve m x prev c hp
  | succ k =>
    rw [actionNode_reserve_succ] at hp
    refine h c ⟨k, fun j hj => ?_, hp⟩
    have := hi (j + 1) (by omega)
    rwa [actionNode_reserve_succ] at this

end TvmLean.Tx

namespace TvmLean

/-- An action list made of `SENDRAWMSG` and `RAWRESERVE` actions, from the empty list. -/
inductive SafeActs : Cell → Prop
  | empty : SafeActs Cell.empty
  | send {prev : Cell} (mode : Nat) (msg : Cell) : SafeActs prev → SafeActs (OutAction.sendMsg mode prev msg)
  | reserve {prev : Cell} (mode x : Nat) : SafeActs prev → SafeActs (OutAction.reserve mode x prev)

/-- **An action list of `SENDRAWMSG` and `RAWRESERVE` actions has no `SETCODE`.** -/
theorem SafeActs.noSetCode {c5 : Cell} (h : SafeActs c5) : Tx.NoSetCode c5 := by
  induction h with
  | empty => exact Tx.noSetCode_empty
  | send m msg _ ih => exact Tx.noSetCode_sendMsg ih m msg
  | reserve m x _ ih => exact Tx.noSetCode_reserve ih m x

end TvmLean

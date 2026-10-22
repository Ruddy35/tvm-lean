import TvmLean.Proofs.Exec.Spec.CellExt

/-!
# Specification: `LDMSGADDR` on any slice

`Spec.ldMsgAddr` and `Spec.ldMsgAddr_error` (`Proofs/Exec/Spec/CellExt.lean`) take the result of
`Slice.skipMessageAddr` as a hypothesis of the goal. On a slice the run knows nothing about (the
sender address of an inbound message) there is none: `Spec.ldMsgAddr_any` states the instruction
as a `match` on that result, which `vm_run` splits (the case `.ok rest` with the hypothesis
`skipMessageAddr = .ok rest`). Its failure is always cell_und (`Slice.skipMessageAddr_error`, C++
`skip_message_addr` returns false and `exec_load_message_addr` throws cell_und, tonops.cpp).

The specification is tagged `vm_spec`: a module that imports this one runs every non-quiet
`LDMSGADDR` this way; a slice whose address the run knows reduces the `match` by a rewrite of
`skipMessageAddr` (e.g. `TvmLean.Contracts.Storage.Data.skip_provider`).
-/

namespace TvmLean

/-- An `Except` that fails only with cell_und. -/
def ErrCellUnd {α : Type} (r : Except Excno α) : Prop := ∀ e, r = .error e → e = .cellUnd

theorem ErrCellUnd.ok {α : Type} (a : α) : ErrCellUnd (.ok a : Except Excno α) := by
  intro e h; cases h

theorem ErrCellUnd.throw {α : Type} : ErrCellUnd (throw .cellUnd : Except Excno α) := by
  intro e h; cases h; rfl

theorem ErrCellUnd.bind {α β : Type} {x : Except Excno α} {f : α → Except Excno β} (hx : ErrCellUnd x)
    (hf : ∀ a, ErrCellUnd (f a)) : ErrCellUnd (x >>= f) := by
  intro e h
  cases x with
  | error e' => cases h; exact hx _ rfl
  | ok a => exact hf a e h

theorem ErrCellUnd.pure {α : Type} (a : α) : ErrCellUnd (pure a : Except Excno α) := by
  intro e h; cases h

theorem ErrCellUnd.ite {α : Type} {c : Prop} [Decidable c] {x y : Except Excno α} (hx : ErrCellUnd x)
    (hy : ErrCellUnd y) : ErrCellUnd (if c then x else y) := by
  split
  · exact hx
  · exact hy

/-- `Slice.skipMessageAddr` fails only with cell_und. -/
theorem Slice.skipMessageAddr_error {s : Slice} {gv : Nat} {e : Excno} (h : s.skipMessageAddr gv = .error e) :
    e = .cellUnd := by
  have : ErrCellUnd (s.skipMessageAddr gv) := by
    unfold Slice.skipMessageAddr
    repeat' (first
      | exact ErrCellUnd.ok _ | exact ErrCellUnd.pure _ | exact ErrCellUnd.throw
      | (refine ErrCellUnd.bind ?_ (fun _ => ?_)) | (refine ErrCellUnd.ite ?_ ?_) | split
      | (unfold Slice.takeBitsAsNatCellUnd) | (unfold Slice.skipMaybeAnycast) | (unfold Slice.takeAnycastDepth))
  exact this e h

namespace Spec

/-- **`LDMSGADDR` on any slice** (C++ `exec_load_message_addr`, tonops.cpp): the address
`Slice.skipMessageAddr` reads, as a slice of its own, then the rest; cell_und if there is none. -/
@[vm_spec] theorem ldMsgAddr_any (st : VmState) (s : Stack) (sl : Slice) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.tonEnvOp (.ldMsgAddr false))) st =
      match sl.skipMessageAddr st.globalVersion with
      | .ok rest => (.ok (), { st with stack := (s.push (.slice (Slice.ofCell (sl.prefixCell rest)))).push (.slice rest) })
      | .error _ => (.error .cellUnd, { st with stack := s }) := by
  cases h : sl.skipMessageAddr st.globalVersion with
  | ok rest => rw [Spec.ldMsgAddr st s sl rest false hs h]; rfl
  | error e => rw [Spec.ldMsgAddr_error st s sl e false hs h, Slice.skipMessageAddr_error h]; rfl

end Spec

end TvmLean

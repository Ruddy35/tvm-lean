import TvmLean.Semantics

/-!
# Decidable equality for cells, slices and instructions

`Cell` is a nested inductive (`refs : Array Cell`), for which `deriving DecidableEq` is not
available; equality is decided by structural mutual recursion over `Cell`, `Array Cell`,
`List Cell`, so that the kernel can evaluate it (`decide +kernel`). Everything else is derived.
-/

namespace TvmLean

mutual
/-- Decidable equality of cells by structural recursion (kernel-reducible). -/
def cellDecEq : (a b : Cell) → Decidable (a = b)
  | ⟨⟨b1⟩, r1, s1, l1⟩, ⟨⟨b2⟩, r2, s2, l2⟩ =>
    -- bits compared as lists: one linear pass (indexing an array literal is linear per access)
    match List.hasDecEq b1 b2 with
    | isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
    | isTrue hb =>
      if hs : s1 = s2 then
        if hl : l1 = l2 then
          match cellArrDecEq r1 r2 with
          | isTrue hr => isTrue (by subst hb hs hl hr; rfl)
          | isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
        else isFalse (by intro h; cases h; exact hl rfl)
      else isFalse (by intro h; cases h; exact hs rfl)
termination_by structural a => a
def cellArrDecEq : (as bs : Array Cell) → Decidable (as = bs)
  | ⟨l1⟩, ⟨l2⟩ =>
    match cellListDecEq l1 l2 with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
termination_by structural as => as
def cellListDecEq : (as bs : List Cell) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match cellDecEq a b, cellListDecEq as bs with
    | isTrue h1, isTrue h2 => isTrue (by subst h1 h2; rfl)
    | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
termination_by structural as => as
end

instance : DecidableEq Cell := cellDecEq
deriving instance DecidableEq for Slice

instance : DecidableEq IntVal := by infer_instance
deriving instance DecidableEq for DictExtInstr
deriving instance DecidableEq for TupleInstr
deriving instance DecidableEq for CellInstr
deriving instance DecidableEq for CryptoExtInstr
deriving instance DecidableEq for CryptoInstr
deriving instance DecidableEq for TonEnvInstr
deriving instance DecidableEq for DebugInstr
deriving instance DecidableEq for ContExtInstr
deriving instance DecidableEq for ArithExtInstr
deriving instance DecidableEq for CellExtInstr
deriving instance DecidableEq for Instr

instance : DecidableEq Excno := by infer_instance

instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b =>
      if h : a = b then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .error a, .error b =>
      if h : a = b then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => isFalse (by intro e; cases e)
  | .error _, .ok _ => isFalse (by intro e; cases e)
end TvmLean

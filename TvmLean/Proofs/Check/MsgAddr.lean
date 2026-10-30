import TvmLean.Proofs.WF.Library
import TvmLean.Proofs.Check.Framed

/-!
# Checking an invariant over all transactions: the slice after a message address

`LDMSGADDR` on a slice the run reads (`Spec.ldMsgAddr_any`) leaves, on the path where it reads an
address, a hypothesis `Slice.skipMessageAddr s gv = .ok t` with the rest `t` a variable. The rest is
`s` with its bit position moved forward, over the same cell and with the same references
(`Slice.skipMessageAddr_shape`, C++ `skip_message_addr` advances the slice it reads, tonops.cpp:
1621-1646). `check_skip_shape`, one more alternative of `check_extra_step`, writes the rest so
(`⟨s.cell, q, s.refPos⟩` for a new `q` between the slice's position and the end of its bits): the
reads after the address are then reads of `s`'s cell, the references of a data cell among them
(`LDREF` after `LDMSGADDR`, as the jetton minter and the NFT collection read their data), and the
address the instruction pushes, stored back (`STSLICE`), is the bits read and no reference
(`ofCell_prefixCell_toCellRemaining`).
-/

namespace TvmLean

/-- **The rest of a message address is the slice moved forward**: the same cell and references, a
bit position between the slice's and the end of its bits. -/
theorem Slice.skipMessageAddr_shape {s t : Slice} {gv : Nat} (h : s.skipMessageAddr gv = .ok t) :
    ∃ q, t = { cell := s.cell, bitPos := q, refPos := s.refPos } ∧ s.bitPos ≤ q ∧ q ≤ s.cell.bits.size := by
  have hP : t.cell = s.cell ∧ t.refPos = s.refPos ∧ s.bitPos ≤ t.bitPos ∧ t.bitPos ≤ s.cell.bits.size := by
    refine Except.of_triple (P := fun t : Slice => t.cell = s.cell ∧ t.refPos = s.refPos ∧
      s.bitPos ≤ t.bitPos ∧ t.bitPos ≤ s.cell.bits.size) ?_ h
    mvcgen [Slice.skipMessageAddr, Slice.skipMaybeAnycast, Slice.takeAnycastDepth,
      Slice.takeBitsAsNatCellUnd_spec]
    all_goals simp_all [Slice.advanceBits, Slice.haveBits]
    all_goals omega
  obtain ⟨hc, hr, h1, h2⟩ := hP
  obtain ⟨c, p, r⟩ := t
  simp only at hc hr h1 h2
  subst hc hr
  exact ⟨p, rfl, h1, h2⟩

end TvmLean

namespace TvmLean.Check

/-- The address `LDMSGADDR` pushes, the slice before the rest (`prefixCell` of the slice and its rest
written out), as a store reads it (`STSLICE`): the bits read, no references. -/
@[check_run_simp, check_close] theorem ofCell_prefixCell_toCellRemaining (c : Cell) (p q r : Nat) :
    (Slice.ofCell (Slice.prefixCell ⟨c, p, r⟩ ⟨c, q, r⟩)).toCellRemaining =
      Cell.mkOrdinary (c.bits.extract p q) #[] := by
  show (Slice.ofCell (Cell.mkOrdinary (c.bits.extract p q) (c.refs.extract r r))).toCellRemaining = _
  rw [Array.extract_eq_empty_of_le (Nat.min_le_left _ _)]
  generalize c.bits.extract p q = b
  simp [Slice.toCellRemaining, Slice.ofCell, Cell.mkOrdinary]

open Lean Meta Elab Tactic

/-- `check_skip_shape`: a hypothesis `Slice.skipMessageAddr s gv = .ok t` with `t` a variable (the
rest after `LDMSGADDR`): `t` replaced by `⟨s.cell, q, s.refPos⟩` (`Slice.skipMessageAddr_shape`),
with `s.bitPos ≤ q` and `q ≤ s.cell.bits.size`. Fails if there is no such hypothesis. -/
elab "check_skip_shape" : tactic => withMainContext do
  let mut found : Option Expr := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    if lhs.isAppOfArity ``Slice.skipMessageAddr 2 && rhs.isAppOfArity ``Except.ok 3 && rhs.appArg!.isFVar then
      found := some d.toExpr
      break
  let some h := found | throwError "check_skip_shape: no rest of an address to write out"
  let pf ← mkAppM ``Slice.skipMessageAddr_shape #[h]
  let g ← getMainGoal
  let (_, g) ← (← g.assert `hvm_shape (← inferType pf) pf).intro1P
  replaceMainGoal [g]
  -- `rfl` and the hypothesis by `mkIdent`: written in the quotation they would be hygienic names
  let rflI := mkIdent `rfl
  let hI := mkIdent `hvm_shape
  evalTactic (← `(tactic| obtain ⟨q, $rflI:ident, hq₁, hq₂⟩ := $hI:ident))

end TvmLean.Check

namespace TvmLean

macro_rules
  | `(tactic| check_extra_step [$_args,*]) => `(tactic| check_skip_shape)

end TvmLean

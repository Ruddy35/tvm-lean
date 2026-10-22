import TvmLean.Proofs.Exec.Dict.Gas

/-!
# The cells a dictionary update loads

The handlers of the dictionary updates charge the root, then the cells the update visited after
it (C++ loads each node on the key's path, `load_cell_slice`): the model takes the cells the
function returns and drops the first copy of the root (`dropFirstRootLoad`). On a well-formed
dictionary the cells a set returns, and the cells a lookup visits, are the root followed by
ordinary cells (`set_loaded`, `visited_loaded`), so their loads are in closed form
(`VM.loadOrd`).
-/

namespace TvmLean

mutual
/-- `Cell.beq` is reflexive. -/
theorem Cell.beq_self : ∀ c : Cell, Cell.beq c c = true
  | ⟨⟨b⟩, ⟨r⟩, s, l⟩ => by
    simp only [Cell.beq, beq_self_eq_true, Bool.and_true, Bool.true_and]
    exact Cell.beqList_self r
theorem Cell.beqList_self : ∀ l : List Cell, Cell.beqList l l = true
  | [] => rfl
  | a :: as => by simp only [Cell.beqList, Cell.beq_self a, Cell.beqList_self as, Bool.and_self]
end

namespace DictMap

/-- A node the default resolver reads is ordinary. -/
theorem parse_ordinary {c : Cell} {n : Nat} {lbl : DictLabel}
    (h : parseDictLabel c n Cell.rejectSpecial = .ok lbl) : c.special = false := by
  obtain ⟨c', hr, _⟩ := parseDictLabel_ok h
  unfold Cell.rejectSpecial at hr
  split at hr
  · cases hr
  · simpa using ‹¬c.special = true›

/-- The root of a well-formed non-empty dictionary is ordinary. -/
theorem WF_root_ordinary {c : Cell} {n : Nat} (hwf : Dict.WF (some c) n) : c.special = false := by
  obtain ⟨lbl, hp, _⟩ := WF_parse hwf
  exact parse_ordinary hp

/-- **What a set loads**, on a well-formed dictionary: the root, then ordinary cells (the nodes on
the key's path below the root). -/
theorem set_loaded {sv : Builder → Except Excno Builder} {mode : DictSetMode} :
    ∀ (n : Nat) (c : Cell) (key : BitString), key.size = n → Dict.WF (some c) n →
      ∀ res, dictSetGenAuxWithCells (some c) key sv mode = .ok res →
        ∃ rest : Array Cell, res.2.2.2 = #[c] ++ rest ∧ ∀ x ∈ rest.toList, x.special = false := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro c key hk hwf res h
  subst hk
  rw [dictSetGenAuxWithCells.eq_def] at h
  obtain ⟨lbl, hp, _⟩ := WF_parse hwf
  dsimp only at h
  rw [hp] at h
  dsimp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i v hv
  obtain ⟨hv1, -⟩ := dictValidateNodeExtLe_ok hv
  have hleaf : ∀ x, res = x → x.2.2.2 = #[c] →
      ∃ rest : Array Cell, res.2.2.2 = #[c] ++ rest ∧ ∀ x ∈ rest.toList, x.special = false :=
    fun x hx hx' => ⟨#[], by rw [hx, hx']; rfl, by simp⟩
  split at h
  · -- the edge split: only the root
    repeat' (first | (cases h; done) | split at h)
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; exact hleaf _ h.symm rfl)
  · dsimp only [pure, Except.pure] at h
    split at h
    · repeat' (first | (cases h; done) | split at h)
      all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; exact hleaf _ h.symm rfl)
    · rename_i h0
      have hc1 : Dict.WF (some lbl.remainder.cell.refs[1]!) (key.size - lbl.len - 1) :=
        WF_child hwf hp (by omega) true
      have hc0 : Dict.WF (some lbl.remainder.cell.refs[0]!) (key.size - lbl.len - 1) :=
        WF_child hwf hp (by omega) false
      have hsz : (key.extract (lbl.len + 1) key.size).size = key.size - lbl.len - 1 := by simp; omega
      have hchild : ∀ (ch : Cell), Dict.WF (some ch) (key.size - lbl.len - 1) →
          ∀ v', dictSetGenAuxWithCells (some ch) (key.extract (lbl.len + 1) key.size) sv mode = .ok v' →
          ∀ x, res = x → x.2.2.2 = #[c] ++ v'.2.2.2 →
          ∃ rest : Array Cell, res.2.2.2 = #[c] ++ rest ∧ ∀ x ∈ rest.toList, x.special = false := by
        intro ch hch v' hv' x hx hx'
        obtain ⟨rest', h1, h2⟩ := ih _ (by omega) ch _ hsz hch v' hv'
        refine ⟨v'.2.2.2, by rw [hx, hx'], ?_⟩
        rw [h1]
        intro y hy
        simp only [Array.toList_append, List.mem_append] at hy
        rcases hy with hy | hy
        · simp at hy; subst hy; exact WF_root_ordinary hch
        · exact h2 y hy
      split at h
      all_goals
        split at h
        · cases h
        rename_i v' hv'
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          first | exact hchild _ hc1 v' hv' _ h.symm rfl | exact hchild _ hc0 v' hv' _ h.symm rfl
        repeat' (first | (cases h; done) | split at h)
        all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h
                   first | exact hchild _ hc1 v' hv' _ h.symm rfl | exact hchild _ hc0 v' hv' _ h.symm rfl)

/-- What a lookup visits, on a well-formed dictionary: the root, then ordinary cells. -/
theorem visitedF_loaded (f : Nat) :
    ∀ (c : Cell) (key : BitString) (pos rem : Nat), Dict.WF (some c) rem →
      ∃ rest : Array Cell, dictLookupVisitedCellsAuxF Cell.rejectSpecial f c key pos rem = #[c] ++ rest ∧
        ∀ x ∈ rest.toList, x.special = false := by
  induction f with
  | zero => intro c key pos rem _; exact ⟨#[], rfl, by simp⟩
  | succ f ih =>
    intro c key pos rem hwf
    simp only [dictLookupVisitedCellsAuxF]
    unfold dictLookupVisitedStep
    obtain ⟨lbl, hp, _⟩ := WF_parse hwf
    rw [hp]
    dsimp only
    have here : ∃ rest : Array Cell, #[c] = #[c] ++ rest ∧ ∀ x ∈ rest.toList, x.special = false :=
      ⟨#[], rfl, by simp⟩
    by_cases h0 : rem - lbl.len = 0
    · simp only [h0, if_true]; exact here
    · simp only [h0, if_false]
      split
      · exact here
      split
      · exact here
      split
      · exact here
      have hrest : ∀ (ch : Cell), Dict.WF (some ch) (rem - lbl.len - 1) → ∀ p,
          ∃ rest : Array Cell,
            #[c] ++ dictLookupVisitedCellsAuxF Cell.rejectSpecial f ch key p (rem - lbl.len - 1) = #[c] ++ rest ∧
            ∀ x ∈ rest.toList, x.special = false := by
        intro ch hch p
        obtain ⟨rest', h1, h2⟩ := ih ch key p _ hch
        refine ⟨_, rfl, ?_⟩
        rw [h1]
        intro y hy
        simp only [Array.toList_append, List.mem_append] at hy
        rcases hy with hy | hy
        · simp at hy; subst hy; exact WF_root_ordinary hch
        · exact h2 y hy
      cases hb : key[pos + lbl.len]!
      · simp only [Bool.false_eq_true, if_false]
        exact hrest _ (WF_child hwf hp (by omega) false) _
      · simp only [if_true]
        exact hrest _ (WF_child hwf hp (by omega) true) _

theorem visited_loaded {c : Cell} {key : BitString} (hwf : Dict.WF (some c) key.size) :
    ∃ rest : Array Cell, dictLookupVisitedCells (some c) key = #[c] ++ rest ∧
      ∀ x ∈ rest.toList, x.special = false := by
  simp only [dictLookupVisitedCells, dictLookupVisitedCellsAux]
  exact visitedF_loaded _ c key 0 key.size hwf

/-- What a lookup loads, on a well-formed dictionary: ordinary cells (the nodes on the key's
path). -/
theorem lookupF_loaded (f : Nat) :
    ∀ (c : Cell) (key : BitString) (pos rem : Nat), Dict.WF (some c) rem →
      ∀ v cells, dictLookupAuxWithCellsF Cell.rejectSpecial f c key pos rem = .ok (v, cells) →
        ∀ x ∈ cells.toList, x.special = false := by
  induction f with
  | zero =>
    intro c key pos rem hwf v cells h x hx
    simp only [dictLookupAuxWithCellsF, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp at hx; subst hx; exact WF_root_ordinary hwf
  | succ f ih =>
    intro c key pos rem hwf v cells h x hx
    simp only [dictLookupAuxWithCellsF] at h
    unfold dictLookupWithCellsStep at h
    obtain ⟨lbl, hp, _⟩ := WF_parse hwf
    rw [hp] at h
    dsimp only [bind, Except.bind] at h
    rw [dictValidateNodeExt_eq] at h
    have hroot : c.special = false := WF_root_ordinary hwf
    have hleaf : cells = #[c] → x.special = false := by
      intro hcells; subst hcells; simp at hx; subst hx; exact hroot
    split at h
    · cases h
    dsimp only [pure, Except.pure] at h
    rename_i rem0 hv
    have hrem0 : rem0 = rem - lbl.len := by
      split at hv
      · cases hv
      · cases hv; rfl
    subst hrem0
    split at h
    · cases h; exact hleaf rfl
    split at h
    · cases h; exact hleaf rfl
    split at h
    · cases h; exact hleaf rfl
    rename_i hz _
    have hfork : rem - lbl.len > 0 := by omega
    split at h
    · cases h
    rename_i res hres
    cases h
    simp only [Array.toList_append, List.mem_append] at hx
    rcases hx with hx | hx
    · simp at hx; subst hx; exact hroot
    · exact ih _ key _ _ (WF_child hwf hp hfork _) res.1 res.2 hres x hx

theorem lookup_loaded {c : Cell} {key : BitString} (hwf : Dict.WF (some c) key.size) {v : Option Slice}
    {cells : Array Cell} (h : dictLookupWithCells (some c) key = .ok (v, cells)) :
    ∀ x ∈ cells.toList, x.special = false := by
  simp only [dictLookupWithCells, dictLookupAuxWithCells] at h
  exact lookupF_loaded _ c key 0 key.size hwf v cells h

/-- The cells a delete returns: those loaded, on success or with its error. -/
def delLoads : Except (Excno × Array Cell) (Option Slice × Option Cell × Nat × Array Cell) → Array Cell
  | .ok (_, _, _, l) => l
  | .error (_, l) => l

/-- What a delete loads, on a well-formed dictionary (on success or with its error): ordinary cells
(the nodes on the key's path, and the surviving child of a fork it merges). -/
theorem delete_loaded : ∀ (rem : Nat) (cell : Cell) (key : BitString) (pos : Nat), Dict.WF (some cell) rem →
    ∀ x ∈ (delLoads (dictDeleteAuxWithLoads cell key pos rem)).toList, x.special = false := by
  intro rem
  induction rem using Nat.strongRecOn with
  | _ rem ih =>
  intro cell key pos hwf x hx
  have hroot := WF_root_ordinary hwf
  have hone : x ∈ (#[cell] : Array Cell).toList → x.special = false := by
    intro h; simp at h; subst h; exact hroot
  rw [dictDeleteAuxWithLoads.eq_def] at hx
  obtain ⟨lbl, hp, _⟩ := WF_parse hwf
  rw [hp] at hx
  simp only [withLoads, Except.mapError, bind, Except.bind] at hx
  cases hv : dictValidateNodeExtLe lbl rem with
  | error e => rw [hv] at hx; exact hone hx
  | ok v =>
    rw [hv] at hx
    dsimp only at hx
    obtain ⟨hv1, -⟩ := dictValidateNodeExtLe_ok hv
    by_cases hm : (!dictLabelMatches lbl key pos) = true
    · simp only [hm, if_true, pure, Except.pure, delLoads] at hx; exact hone hx
    · simp only [hm, if_false, Bool.false_eq_true] at hx
      by_cases h0 : v.val = 0
      · simp only [h0, dif_pos, pure, Except.pure, delLoads] at hx; exact hone hx
      · simp only [dif_neg h0] at hx
        have hc1 : Dict.WF (some lbl.remainder.cell.refs[1]!) (v.val - 1) := by
          rw [hv1]; exact WF_child hwf hp (by omega) true
        have hc0 : Dict.WF (some lbl.remainder.cell.refs[0]!) (v.val - 1) := by
          rw [hv1]; exact WF_child hwf hp (by omega) false
        have hs1 := WF_root_ordinary hc1
        have hs0 := WF_root_ordinary hc0
        have hch : ∀ y ∈ (delLoads (dictDeleteAuxWithLoads
            (if key[pos + lbl.len]! = true then lbl.remainder.cell.refs[1]! else lbl.remainder.cell.refs[0]!)
            key (pos + lbl.len + 1) (v.val - 1))).toList, y.special = false := by
          cases key[pos + lbl.len]!
          · exact ih _ (by omega) _ _ _ hc0
          · exact ih _ (by omega) _ _ _ hc1
        have hsurv : (if key[pos + lbl.len]! = true then lbl.remainder.cell.refs[0]!
            else lbl.remainder.cell.refs[1]!).special = false := by
          cases key[pos + lbl.len]!
          · exact hs1
          · exact hs0
        generalize dictDeleteAuxWithLoads
            (if key[pos + lbl.len]! = true then lbl.remainder.cell.refs[1]! else lbl.remainder.cell.refs[0]!)
            key (pos + lbl.len + 1) (v.val - 1) = d at hx hch
        generalize (if key[pos + lbl.len]! = true then lbl.remainder.cell.refs[0]!
            else lbl.remainder.cell.refs[1]!) = surv at hx hsurv
        cases d with
        | error el =>
          obtain ⟨e, l⟩ := el
          simp only [delLoads] at hch
          simp only [underCell, Except.mapError, delLoads, pure, Except.pure, Array.toList_append,
            List.mem_append] at hx
          rcases hx with hx | hx
          · exact hone hx
          · exact hch x hx
        | ok res =>
          have hall2 : ∀ y ∈ (#[cell] ++ res.2.2.2).toList, y.special = false := by
            intro y hy
            simp only [Array.toList_append, List.mem_append] at hy
            rcases hy with hy | hy
            · simp at hy; subst hy; exact hroot
            · exact hch y hy
          have hall : ∀ y ∈ (#[cell] ++ res.2.2.2 ++ #[surv]).toList, y.special = false := by
            intro y hy
            simp only [Array.toList_append, List.mem_append] at hy
            rcases hy with (hy | hy) | hy
            · simp at hy; subst hy; exact hroot
            · exact hch y hy
            · simp at hy; subst hy; exact hsurv
          simp only [underCell, Except.mapError] at hx
          repeat' split at hx
          all_goals (simp only [delLoads, pure, Except.pure] at hx)
          all_goals first
            | exact hall x hx | exact hall2 x hx | exact hone hx
            | (rename_i heq; simp only [pure, Except.pure, reduceCtorEq] at heq; done)
            | (rename_i heq
               split at heq
               · cases heq; exact hall x hx
               · cases heq)

theorem deleteWithLoads_loaded {c : Cell} {key : BitString} (hwf : Dict.WF (some c) key.size) :
    ∀ x ∈ (delLoads (dictDeleteWithLoads (some c) key)).toList, x.special = false := by
  simp only [dictDeleteWithLoads]
  exact delete_loaded key.size c key 0 hwf

end DictMap

end TvmLean

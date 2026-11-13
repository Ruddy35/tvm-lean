import TvmLean.Proofs.Exec.Spec.Dispatch

/-!
# Specifications: `PFXDICTSWITCH`, `PFXDICTGETJMP`, `PFXDICTGETEXEC` on a known dictionary

`PFXDICTSWITCH` (C++ `exec_const_pfx_dict_switch`, dictops.cpp) holds its prefix dictionary as a
reference of the code; `PFXDICTGETJMP` and `PFXDICTGETEXEC` (C++ `exec_pfx_dict_get`) pop it. Each pops
a key slice, looks up the longest prefix of the key in the dictionary (`PrefixDictionary::lookup_prefix`;
the model's private walk `DictExt.pfxLookupPrefixGo` of TvmLean/Semantics/Exec/Dict/Ext.lean), and
when it is found pushes the prefix and the rest of the key and jumps to the value (`PFXDICTGETEXEC`
calls it); when it is not, `PFXDICTSWITCH` and `PFXDICTGETJMP` push the key back and
`PFXDICTGETEXEC` throws cell_und.

The walk is recursive by well-founded recursion, which the kernel does not evaluate; as for the
method dispatch (`dictLookupLoads`, `Proofs/Exec/Spec/Dispatch.lean`), the lookup is stated by a
closed fact that the kernel decides when the dictionary and the key are known:

* `pfxLookupStep`: one step of the walk (the same code), the walk below a fork a parameter;
  `pfxLookupGoF`: the steps with a fuel, by structural recursion (`pfxLookupGoF_eq`: it is the private
  walk, `pfxLookupPrefixGo_step`), and `pfxLookupGoF_of_rejectSpecial`: a walk that succeeds with the
  default resolver gives the same result with the resolver of the VM;
* `pfxLookupLoads root cs n`: the value found with the prefix and the rest of the key, or none, and
  the cells loaded after the root (default resolver);
* `Spec.pfxSwitch_found`, `Spec.pfxSwitch_notFound`, `Spec.pfxGetJmp_found`, `Spec.pfxGetJmp_notFound`,
  `Spec.pfxGetExec_found`, `Spec.pfxGetExec_notFound`: the instructions by that fact (a run evaluates it
  natively and the kernel proves it, `evalClosed?` in `Proofs/Exec/Tactic.lean`);
  `Spec.pfxGetJmp_null`, `Spec.pfxGetExec_null`: on the empty dictionary, for any key.

A key or a dictionary the run does not know leaves the instruction to its handler (the value found
in a dictionary the run does not know is code it does not know).
-/

namespace TvmLean

/-- One step of the walk of `PrefixDictionary::lookup_prefix` (the body of `DictExt.pfxLookupPrefixGo`,
private in TvmLean/Semantics/Exec/Dict/Ext.lean, the same code), the walk below a fork `rec` (given a
key length left smaller than `m`). -/
def pfxLookupStep (keyBits : BitString) (keyLen : Nat) (cell : Cell) (nRem m pos : Nat) (loaded : Array Cell)
    (resolve : Cell → Except Excno Cell)
    (rec : Cell → Nat → (m' : Nat) → m' < m → Nat → Array Cell →
      Except (Excno × Array Cell) (Option Slice × Nat × Array Cell)) :
    Except (Excno × Array Cell) (Option Slice × Nat × Array Cell) := do
  let loaded := loaded.push cell
  let lbl ←
    match parseDictLabel (resolve := resolve) cell nRem with
    | .ok l => pure l
    | .error e => throw (e, loaded)
  let labelBits : BitString := dictLabelBits lbl
  let l : Nat :=
    let keyPart := keyBits.extract pos (pos + Nat.min m lbl.len)
    bitsCommonPrefixLen labelBits keyPart
  if l < lbl.len then
    return (none, pos + l, loaded)
  let nRem := nRem - lbl.len
  let m' := m - lbl.len
  let pos := pos + lbl.len
  let payload0 : Slice := lbl.remainder.advanceBits lbl.storedBits
  if !payload0.haveBits 1 then
    throw (.dictErr, loaded)
  let ctor : Bool := (payload0.readBits 1)[0]!
  let payload : Slice := { payload0 with bitPos := payload0.bitPos + 1 }
  if !ctor then
    return (some payload, pos, loaded)
  -- Fork node
  if nRem = 0 then
    throw (.dictErr, loaded)
  if payload.bitsRemaining != 0 || payload.refsRemaining != 2 then
    throw (.dictErr, loaded)
  if hm : m' = 0 then
    return (none, keyLen, loaded)
  else
    let swBit : Bool := keyBits[pos]!
    let child := payload.cell.refs[if swBit then 1 else 0]!
    rec child (nRem - 1) (m' - 1)
      (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.pos_of_ne_zero hm) Nat.zero_lt_one) (Nat.sub_le m lbl.len))
      (pos + 1) loaded

/-- The walk of `PrefixDictionary::lookup_prefix` with a fuel that bounds its depth: its steps
(`pfxLookupStep`) by structural recursion on the fuel, so that the kernel evaluates it. Out of fuel it
fails (never with more fuel than key bits, `pfxLookupGoF_eq`). -/
def pfxLookupGoF (keyBits : BitString) (keyLen : Nat) :
    Nat → Cell → Nat → Nat → Nat → Array Cell → (Cell → Except Excno Cell) →
      Except (Excno × Array Cell) (Option Slice × Nat × Array Cell)
  | 0, cell, _, _, _, loaded, _ => .error (.fatal, loaded.push cell)
  | fuel + 1, cell, nRem, m, pos, loaded, resolve =>
    pfxLookupStep keyBits keyLen cell nRem m pos loaded resolve
      (fun c nr m' _ p l => pfxLookupGoF keyBits keyLen fuel c nr m' p l resolve)

/-- The private walk is its step with itself below the forks. -/
theorem pfxLookupPrefixGo_step (keyBits : BitString) (keyLen : Nat) (cell : Cell) (nRem m pos : Nat)
    (loaded : Array Cell) (resolve : Cell → Except Excno Cell) :
    (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixGo) keyBits keyLen cell nRem m pos
        loaded resolve =
      pfxLookupStep keyBits keyLen cell nRem m pos loaded resolve (fun c nr m' _ p l =>
        (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixGo) keyBits keyLen c nr m' p l
          resolve) := by
  rw [private_eq% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixGo]
  rfl

/-- **The walk with a fuel is the private walk** when the fuel exceeds the key bits left. -/
theorem pfxLookupGoF_eq (keyBits : BitString) (keyLen : Nat) (resolve : Cell → Except Excno Cell) :
    ∀ (fuel m : Nat), m < fuel → ∀ (cell : Cell) (nRem pos : Nat) (loaded : Array Cell),
      pfxLookupGoF keyBits keyLen fuel cell nRem m pos loaded resolve =
        (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixGo) keyBits keyLen cell nRem m
          pos loaded resolve := by
  intro fuel
  induction fuel with
  | zero => intro m hm; omega
  | succ f ih =>
    intro m hm cell nRem pos loaded
    rw [pfxLookupPrefixGo_step, pfxLookupGoF]
    congr 1
    funext c nr m' h p l
    exact ih m' (by omega) c nr p l

/-- **The walk with any resolver.** A walk that succeeds with the default resolver gives the same
result with any resolver that loads ordinary cells as themselves (the resolver of the VM). -/
theorem pfxLookupGoF_of_rejectSpecial (r : Cell → Except Excno Cell) (hr : ResolvesOrdinary r)
    (keyBits : BitString) (keyLen : Nat) :
    ∀ (fuel : Nat) (cell : Cell) (nRem m pos : Nat) (loaded : Array Cell)
      (x : Option Slice × Nat × Array Cell),
      pfxLookupGoF keyBits keyLen fuel cell nRem m pos loaded Cell.rejectSpecial = .ok x →
        pfxLookupGoF keyBits keyLen fuel cell nRem m pos loaded r = .ok x := by
  intro fuel
  induction fuel with
  | zero => intro cell nRem m pos loaded x h; cases h
  | succ f ih =>
    intro cell nRem m pos loaded x h
    simp only [pfxLookupGoF, pfxLookupStep] at h ⊢
    cases hp : parseDictLabel cell nRem Cell.rejectSpecial with
    | error e =>
      rw [hp] at h
      cases h
    | ok lbl =>
      rw [parseDictLabel_of_rejectSpecial cell nRem r hr lbl hp]
      rw [hp] at h
      revert h
      simp only [bind, Except.bind, pure, Except.pure]
      repeat' (first | exact id | (intro h; cases h; done) | (intro h; exact ih _ _ _ _ _ _ h) | split)

/-- The lookup of `PFXDICTSWITCH`, `PFXDICTGETJMP`, `PFXDICTGETEXEC` in the dictionary `root` (key
length `n`) of the key slice `cs`, with the default resolver: the value found, the prefix of the key
it matched and the rest of the key (C++ `fetch_subslice` of the prefix), or none; and the cells loaded after the root (the model charges
the root first, then the visited cells but the root). Closed for a dictionary of the code and a
known key: the kernel decides it. -/
def pfxLookupLoads (root : Cell) (cs : Slice) (n : Nat) :
    Except Excno (Option (Slice × Slice × Slice) × List Cell) :=
  let keyBits := cs.readBits cs.bitsRemaining
  match pfxLookupGoF keyBits keyBits.size (keyBits.size + 1) root n keyBits.size 0 #[] Cell.rejectSpecial with
  | .error (e, _) => .error e
  | .ok (none, _, cells) => .ok (none, (cells.filter (fun c => c != root)).toList)
  | .ok (some v, pfxLen, cells) =>
    match (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix) cs pfxLen 0 with
    | .ok (p, rest) => .ok (some (v, p, rest), (cells.filter (fun c => c != root)).toList)
    | .error e => .error e

/-- The lookup of the VM (private `DictExt.pfxLookupPrefixWithCells`, the resolver of the VM) from
the walk with a fuel and the default resolver. -/
theorem pfxLookupPrefixWithCells_of_goF {root : Cell} {keyBits : BitString} {n : Nat}
    {x : Option Slice × Nat × Array Cell}
    (h : pfxLookupGoF keyBits keyBits.size (keyBits.size + 1) root n keyBits.size 0 #[] Cell.rejectSpecial = .ok x)
    (libs : Array Cell) (gv : Nat) (refused : Array BitString) :
    (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells) (some root) keyBits
      keyBits.size n (fun c => (libraryResolveLoads libs gv c refused).2) = .ok x := by
  rw [private_eq% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells]
  simp only
  rw [← pfxLookupGoF_eq _ _ _ (keyBits.size + 1) keyBits.size (by omega)]
  exact pfxLookupGoF_of_rejectSpecial _ (resolvesOrdinary_library libs gv refused) _ _ _ _ _ _ _ _ _ h

theorem pfxLookupLoads_found {root : Cell} {cs : Slice} {n : Nat} {v p rest : Slice} {loads : List Cell}
    (h : pfxLookupLoads root cs n = .ok (some (v, p, rest), loads)) :
    ∃ pfxLen cells,
      (∀ libs gv refused,
        (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells) (some root)
          (cs.readBits cs.bitsRemaining) (cs.readBits cs.bitsRemaining).size n
          (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (some v, pfxLen, cells)) ∧
      (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.slicePrefix) cs pfxLen 0 = .ok (p, rest) ∧
      (cells.filter (fun c => c != root)).toList = loads := by
  simp only [pfxLookupLoads] at h
  split at h
  · cases h
  · cases h
  · rename_i v' pfxLen cells hg
    split at h
    · rename_i p' rest' hsp
      cases h
      exact ⟨pfxLen, cells, pfxLookupPrefixWithCells_of_goF hg, hsp, rfl⟩
    · cases h

theorem pfxLookupLoads_notFound {root : Cell} {cs : Slice} {n : Nat} {loads : List Cell}
    (h : pfxLookupLoads root cs n = .ok (none, loads)) :
    ∃ pos cells,
      (∀ libs gv refused,
        (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells) (some root)
          (cs.readBits cs.bitsRemaining) (cs.readBits cs.bitsRemaining).size n
          (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (none, pos, cells)) ∧
      (cells.filter (fun c => c != root)).toList = loads := by
  simp only [pfxLookupLoads] at h
  split at h
  · cases h
  · rename_i pos cells hg
    cases h
    exact ⟨pos, cells, pfxLookupPrefixWithCells_of_goF hg, rfl⟩
  · split at h <;> cases h

/-- The cells loaded after the root (private `DictExt.loadedWithoutRoot`). -/
theorem loadedWithoutRoot_some (root : Cell) (l : Array Cell) :
    (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.loadedWithoutRoot) (some root) l =
      l.filter (fun c => c != root) := rfl

/-- The lookup in the empty dictionary finds nothing and visits no cell. -/
theorem pfxLookupPrefixWithCells_none (keyBits : BitString) (keyLen n : Nat) (r : Cell → Except Excno Cell) :
    (private% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells) none keyBits keyLen n r =
      .ok (none, 0, #[]) := by
  rw [private_eq% TvmLean.Semantics.Exec.Dict.Ext TvmLean.DictExt.pfxLookupPrefixWithCells]
  rfl

namespace Spec

set_option maxHeartbeats 4000000 in
/-- `PFXDICTSWITCH` (C++ `exec_const_pfx_dict_switch`) on the stack `s cs` when a prefix of the key
`cs` is in the dictionary of the code (`pfxLookupLoads`, closed for a known key): the root and the
visited cells are loaded, the prefix and the rest of the key pushed, and the value jumped to. -/
@[vm_spec] theorem pfxSwitch_found (st : VmState) (s : Stack) (cs : Slice) (root : Cell) (n : Nat)
    (v p rest : Slice) (loads : List Cell)
    (hs : st.stack = s.push (.slice cs))
    (hlook : pfxLookupLoads root cs n = .ok (some (v, p, rest), loads)) :
    ExceptT.run (execInstr (.dictExt (.pfxSwitch root n))) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => do
          VM.push (.slice p)
          VM.push (.slice rest)
          modify fun st => st.jumpTo (.ordinary v (.quit 0) OrdCregs.empty OrdCdata.empty)) := by
  obtain ⟨pfxLen, cells, hc, hp, hl⟩ := pfxLookupLoads_found hlook
  simp only [VM.readBits_size] at hc
  vm_simp [hs, hc, hp, pure_bind, VM.cellResolver, VM.forIn_registerCellLoad, loadedWithoutRoot_some, hl, VM.jumpTo_eq]

set_option maxHeartbeats 4000000 in
/-- `PFXDICTSWITCH` on the stack `s cs` when no prefix of the key `cs` is in the dictionary of the
code: the root and the visited cells are loaded, and the key pushed back. -/
@[vm_spec] theorem pfxSwitch_notFound (st : VmState) (s : Stack) (cs : Slice) (root : Cell) (n : Nat)
    (loads : List Cell)
    (hs : st.stack = s.push (.slice cs))
    (hlook : pfxLookupLoads root cs n = .ok (none, loads)) :
    ExceptT.run (execInstr (.dictExt (.pfxSwitch root n))) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => VM.push (.slice cs)) := by
  obtain ⟨pos, cells, hc, hl⟩ := pfxLookupLoads_notFound hlook
  simp only [VM.readBits_size] at hc
  vm_simp [hs, hc, VM.cellResolver, VM.forIn_registerCellLoad, loadedWithoutRoot_some, hl]

set_option maxHeartbeats 4000000 in
/-- `PFXDICTGETJMP` (C++ `exec_pfx_dict_get`) on the stack `s cs root n` when a prefix of the key
`cs` is in the dictionary `root` (`pfxLookupLoads`, closed for a known dictionary and key): the root
and the visited cells are loaded, the prefix and the rest of the key pushed, and the value jumped
to. -/
@[vm_spec] theorem pfxGetJmp_found (st : VmState) (s : Stack) (cs : Slice) (root : Cell) (n : Int)
    (v p rest : Slice) (loads : List Cell)
    (hs : st.stack = ((s.push (.slice cs)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hlook : pfxLookupLoads root cs n.toNat = .ok (some (v, p, rest), loads)) :
    ExceptT.run (execInstr (.dictExt (.pfxGet .getJmp))) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => do
          VM.push (.slice p)
          VM.push (.slice rest)
          modify fun st => st.jumpTo (.ordinary v (.quit 0) OrdCregs.empty OrdCdata.empty)) := by
  obtain ⟨pfxLen, cells, hc, hp, hl⟩ := pfxLookupLoads_found hlook
  simp only [VM.readBits_size] at hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hn1, hn', hc, hp, pure_bind, VM.popMaybeCell, VM.cellResolver, VM.forIn_registerCellLoad, hl, VM.jumpTo_eq]

set_option maxHeartbeats 4000000 in
/-- `PFXDICTGETJMP` on the stack `s cs root n` when no prefix of the key `cs` is in the dictionary
`root`: the root and the visited cells are loaded, and the key pushed back. -/
@[vm_spec] theorem pfxGetJmp_notFound (st : VmState) (s : Stack) (cs : Slice) (root : Cell) (n : Int)
    (loads : List Cell)
    (hs : st.stack = ((s.push (.slice cs)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hlook : pfxLookupLoads root cs n.toNat = .ok (none, loads)) :
    ExceptT.run (execInstr (.dictExt (.pfxGet .getJmp))) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => VM.push (.slice cs)) := by
  obtain ⟨pos, cells, hc, hl⟩ := pfxLookupLoads_notFound hlook
  simp only [VM.readBits_size] at hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hn1, hn', hc, VM.popMaybeCell, VM.cellResolver, VM.forIn_registerCellLoad, hl]

set_option maxHeartbeats 4000000 in
/-- `PFXDICTGETEXEC` (C++ `exec_pfx_dict_get`) on the stack `s cs root n` when a prefix of the key
`cs` is in the dictionary `root`: as `PFXDICTGETJMP`, the value called. -/
@[vm_spec] theorem pfxGetExec_found (st : VmState) (s : Stack) (cs : Slice) (root : Cell) (n : Int)
    (v p rest : Slice) (loads : List Cell)
    (hs : st.stack = ((s.push (.slice cs)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hlook : pfxLookupLoads root cs n.toNat = .ok (some (v, p, rest), loads)) :
    ExceptT.run (execInstr (.dictExt (.pfxGet .getExec))) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => do
          VM.push (.slice p)
          VM.push (.slice rest)
          modify fun st => st.callTo (.ordinary v (.quit 0) OrdCregs.empty OrdCdata.empty)) := by
  obtain ⟨pfxLen, cells, hc, hp, hl⟩ := pfxLookupLoads_found hlook
  simp only [VM.readBits_size] at hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hn1, hn', hc, hp, pure_bind, VM.popMaybeCell, VM.cellResolver, VM.forIn_registerCellLoad, hl]

set_option maxHeartbeats 4000000 in
/-- `PFXDICTGETEXEC` on the stack `s cs root n` when no prefix of the key `cs` is in the dictionary
`root`: the root and the visited cells are loaded, then cell_und. -/
@[vm_spec] theorem pfxGetExec_notFound (st : VmState) (s : Stack) (cs : Slice) (root : Cell) (n : Int)
    (loads : List Cell)
    (hs : st.stack = ((s.push (.slice cs)).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hlook : pfxLookupLoads root cs n.toNat = .ok (none, loads)) :
    ExceptT.run (execInstr (.dictExt (.pfxGet .getExec))) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => throw .cellUnd) := by
  obtain ⟨pos, cells, hc, hl⟩ := pfxLookupLoads_notFound hlook
  simp only [VM.readBits_size] at hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hn1, hn', hc, VM.popMaybeCell, VM.cellResolver, VM.forIn_registerCellLoad, hl]

set_option maxHeartbeats 4000000 in
/-- `PFXDICTGETJMP` on the stack `s cs null n` (the empty dictionary): nothing is found, the key is
pushed back. -/
@[vm_spec] theorem pfxGetJmp_null (st : VmState) (s : Stack) (cs : Slice) (n : Int)
    (hs : st.stack = ((s.push (.slice cs)).push .null).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictExt (.pfxGet .getJmp))) st =
      (.ok (), { st with stack := s.push (.slice cs) }) := by
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hn1, hn', VM.popMaybeCell, pfxLookupPrefixWithCells_none, VM.forIn_registerCellLoad]

set_option maxHeartbeats 4000000 in
/-- `PFXDICTGETEXEC` on the stack `s cs null n` (the empty dictionary): cell_und. -/
@[vm_spec] theorem pfxGetExec_null (st : VmState) (s : Stack) (cs : Slice) (n : Int)
    (hs : st.stack = ((s.push (.slice cs)).push .null).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictExt (.pfxGet .getExec))) st =
      (.error .cellUnd, { st with stack := s }) := by
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hn1, hn', VM.popMaybeCell, pfxLookupPrefixWithCells_none, VM.forIn_registerCellLoad]

end Spec

end TvmLean

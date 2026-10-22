import TvmLean.Proofs.Exec.Load

/-!
# Specifications: the method dispatch

In the format of `Proofs/Exec/Spec/Stack.lean`. Every FunC contract starts with

  `SETCP0  19 DICTPUSHCONST  DICTIGETJMPZ  11 THROWARG`

(the procedures in a dictionary keyed by method id, the code's first reference; Fift's `PROCDICT`
also makes `DICTIGETJMP`, `DICTUGETJMP` and the `*EXEC` forms), and `CALLDICT n` (`PUSHINT n`,
call `c3`, the root of the code) or `JMPDICT n` call a procedure through it again.

The lookup of a key in the dictionary (`DICT{I,U}GET{JMP,EXEC}{Z}`) is stated by the facts it rests
on: the key's bits (`dictKeyBits?`) and the lookup with the default resolver
(`dictLookupLoads`: the value found and the cells loaded after the root), both closed for a
concrete key and dictionary and decided by the kernel. The lookup of the VM, whose resolver follows
libraries, gives the same result (`dictLookupWithCells_of_rejectSpecial`); the loads are charged
in order (`VM.registerCellLoadList`), their gas symbolic (`Proofs/Exec/Load.lean`).
-/

namespace TvmLean.Spec

/-- `SETCP0` (C++ `exec_set_cp`): the codepage is 0. -/
@[vm_spec] theorem setcp0 (st : VmState) :
    ExceptT.run (execInstr (.setcp 0)) st = (.ok (), { st with cp := 0 }) := by
  vm_simp

/-- `DICTPUSHCONST n` (C++ `exec_push_const_dict`): the dictionary (the reference) and its key
length are pushed. -/
@[vm_spec] theorem dictPushConst (st : VmState) (dict : Cell) (n : Nat) :
    ExceptT.run (execInstr (.dictPushConst dict n)) st =
      (.ok (), { st with stack := (st.stack.push (.cell dict)).push (.int (.num n)) }) := by
  vm_simp

/-- The continuation of a procedure found in a dictionary (C++ `exec_dict_get_exec`: the value
slice as an ordinary continuation) is jumped to or called. -/
def dictJump (doCall : Bool) (val : Slice) (st : VmState) : VmState :=
  if doCall then st.callTo (.ordinary val (.quit 0) OrdCregs.empty OrdCdata.empty)
  else st.jumpTo (.ordinary val (.quit 0) OrdCregs.empty OrdCdata.empty)

theorem dictLookupLoads_ok {root : Cell} {key : BitString} {res : Option Slice} {loads : List Cell}
    (h : dictLookupLoads root key = .ok (res, loads)) :
    ∃ cells, dictLookupWithCells (some root) key = .ok (res, cells) ∧
      (cells.filter (fun c => c != root)).toList = loads := by
  unfold dictLookupLoads at h
  split at h
  · rename_i r cells hc
    cases h
    exact ⟨cells, hc, rfl⟩
  · cases h

/-- `DICT{I,U}GET{JMP,EXEC}{Z}` (C++ `exec_dict_get_exec`, dictops.cpp) when the key is found:
the root and the visited cells are loaded, then the procedure is jumped to (`*JMP*`) or called
(`*EXEC*`). -/
@[vm_spec] theorem dictGetExec_found (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned doCall pushZ : Bool) (key : BitString) (val : Slice) (loads : List Cell)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hkey : dictKeyBits? idx n.toNat unsigned = some key)
    (hlook : dictLookupLoads root key = .ok (some val, loads)) :
    ExceptT.run (execInstr (.dictGetExec unsigned doCall pushZ)) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => modify fun st => dictJump doCall val st) := by
  obtain ⟨cells, hc, hl⟩ := dictLookupLoads_ok hlook
  have hc' : ∀ libs gv refused, dictLookupWithCells (some root) key
      (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (some val, cells) :=
    fun libs gv refused => dictLookupWithCells_of_rejectSpecial _ (resolvesOrdinary_library libs gv refused) _ _ _ hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hkey, hc', hn1, hn', VM.cellResolver, VM.forIn_registerCellLoad, hl, dictJump, VM.jumpTo_eq]

/-- `DICT{I,U}GET{JMP,EXEC}{Z}` when the key is not in the dictionary: the root and the visited
cells are loaded, and the key is pushed back by the `*Z` forms (C++ `exec_dict_get_exec`). -/
@[vm_spec] theorem dictGetExec_notFound (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned doCall pushZ : Bool) (key : BitString) (loads : List Cell)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hkey : dictKeyBits? idx n.toNat unsigned = some key)
    (hlook : dictLookupLoads root key = .ok (none, loads)) :
    ExceptT.run (execInstr (.dictGetExec unsigned doCall pushZ)) st =
      VM.bindRes (ExceptT.run (VM.registerCellLoadList (root :: loads)) { st with stack := s })
        (fun _ => if pushZ then VM.push (.int (.num idx)) else pure ()) := by
  obtain ⟨cells, hc, hl⟩ := dictLookupLoads_ok hlook
  have hc' : ∀ libs gv refused, dictLookupWithCells (some root) key
      (fun c => (libraryResolveLoads libs gv c refused).2) = .ok (none, cells) :=
    fun libs gv refused => dictLookupWithCells_of_rejectSpecial _ (resolvesOrdinary_library libs gv refused) _ _ _ hc
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hkey, hc', hn1, hn', VM.cellResolver, VM.forIn_registerCellLoad, hl]

/-- `DICT{I,U}GET{JMP,EXEC}{Z}` on a dictionary `root` with a key out of the range of `n`-bit
keys: not found, the key pushed back by the `*Z` forms; no cell is loaded. -/
@[vm_spec] theorem dictGetExec_noKey (st : VmState) (s : Stack) (idx : Int) (root : Cell) (n : Int)
    (unsigned doCall pushZ : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push (.cell root)).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023)
    (hkey : dictKeyBits? idx n.toNat unsigned = none) :
    ExceptT.run (execInstr (.dictGetExec unsigned doCall pushZ)) st =
      (.ok (), { st with stack := if pushZ then s.push (.int (.num idx)) else s }) := by
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  vm_simp [hs, hkey, hn1, hn', VM.popMaybeCell]
  cases pushZ <;> simp

/-- The lookup in the empty dictionary finds nothing and visits no cell. -/
theorem dictLookupWithCells_none (key : BitString) (r : Cell → Except Excno Cell) :
    dictLookupWithCells none key r = .ok (none, #[]) := rfl

/-- `DICT{I,U}GET{JMP,EXEC}{Z}` on the empty dictionary (`null`): not found, the key pushed back
by the `*Z` forms. -/
@[vm_spec] theorem dictGetExec_empty (st : VmState) (s : Stack) (idx : Int) (n : Int)
    (unsigned doCall pushZ : Bool)
    (hs : st.stack = ((s.push (.int (.num idx))).push .null).push (.int (.num n)))
    (hn : 0 ≤ n ∧ n ≤ 1023) :
    ExceptT.run (execInstr (.dictGetExec unsigned doCall pushZ)) st =
      (.ok (), { st with stack := if pushZ then s.push (.int (.num idx)) else s }) := by
  have hn1 : ¬ n < 0 := by omega
  have hn' : ¬ n.toNat > 1023 := by omega
  cases hk : dictKeyBits? idx n.toNat unsigned <;>
    (vm_simp [hs, hk, hn1, hn', VM.popMaybeCell, dictLookupWithCells_none]; cases pushZ <;> first | rfl | simp)

/-- `CALLDICT n` (C++ `exec_calldict_short`, `exec_calldict`) when `c3` is a plain continuation
(the root of the code, as the compute phase sets it): `n` is pushed and `c3` called. -/
@[vm_spec] theorem callDict (st : VmState) (n : Nat) (hn : n < 16384) (code : Slice) (saved : Continuation)
    (hc3 : st.regs.c3 = .ordinary code saved OrdCregs.empty OrdCdata.empty) :
    ExceptT.run (execInstr (.callDict n)) st =
      (.ok (), { st with stack := st.stack.push (.int (.num n)), regs := { st.regs with c0 := st.retCont }
                         cc := .ordinary code saved OrdCregs.empty OrdCdata.empty }) := by
  have hm : n &&& 0x3fff = n := by
    rw [show (0x3fff : Nat) = 2 ^ 14 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt hn
  vm_simp [hm, hc3, VmState.retCont]

/-- `JMPDICT n` (C++ `exec_jmpdict`) when `c3` is a plain continuation: `n` is pushed and the VM
jumps to `c3`. -/
@[vm_spec] theorem jmpDict (st : VmState) (n : Nat) (hn : n < 16384) (code : Slice) (saved : Continuation)
    (hc3 : st.regs.c3 = .ordinary code saved OrdCregs.empty OrdCdata.empty) :
    ExceptT.run (execInstr (.contExt (.jmpDict n))) st =
      (.ok (), { st with stack := st.stack.push (.int (.num n)),
                         cc := .ordinary code saved OrdCregs.empty OrdCdata.empty }) := by
  have hm : n &&& 0x3fff = n := by
    rw [show (0x3fff : Nat) = 2 ^ 14 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt hn
  vm_simp [hm, hc3]

/-- `PREPAREDICT n` (C++ `exec_preparedict`): `n` and `c3` are pushed. -/
@[vm_spec] theorem prepareDict (st : VmState) (n : Nat) (hn : n < 16384) :
    ExceptT.run (execInstr (.prepareDict n)) st =
      (.ok (), { st with stack := (st.stack.push (.int (.num n))).push (.cont st.regs.c3) }) := by
  have hm : n &&& 0x3fff = n := by
    rw [show (0x3fff : Nat) = 2 ^ 14 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt hn
  vm_simp [hm]

/-- `THROWARG n` (C++ `exec_throw_arg_fixed`): the exception `n` is raised with the top of the
stack as its argument (`11 THROWARG` ends the dispatch of an unknown method id). -/
@[vm_spec] theorem throwArg (st : VmState) (s : Stack) (arg : Value) (e : Int) (hs : st.stack = s.push arg) :
    ExceptT.run (execInstr (.throwArg e)) st =
      ExceptT.run (VM.throwToHandler fun st => st.throwExceptionArg e arg) { st with stack := s } := by
  vm_simp [hs]

end TvmLean.Spec

import TvmLean.Proofs.WF.Cells

/-!
# Calls, `extract_cc` and the continuations instructions build

The specifications of the VM operations of the Cont and Flow families that `Monad.lean` does not
have, and a closing tactic for the conditions they leave:

* `Continuation.WF.defineC0`, `defineC1`: setting a saved register of a well-formed continuation to
  a well-formed one (`BOOLAND`, `ATEXIT`, the loops with `c1` envelopes, ...);
* `VM.extractCc_spec`: C++ `VmState::extract_cc`, the current continuation as an ordinary one with
  the bottom of the stack as its closure stack and `c0`, `c1`, `c2` saved;
* `VM.callComputeStacks_spec`: the stack a call leaves to the callee and the one it saves are parts
  of the stack and of the closure stack;
* `VM.call_spec`: C++ `VmState::call`, with the return continuation it installs in `c0`.

`wf_cont` is `wf_vc` after splitting the continuations, saved registers (`OrdCregs.wf_mk`) and
closure stacks built into their fields: `grind` alone does not take apart the conditions on the
saved registers of a structure literal (each is a `∀` over an `Option`) within its case-split
budget. The lemmas on registers (`VmState.getCtr_WF`, `VmState.setCtr_WF`,
`Continuation.defineCtr_WF`) are stated led by the operation, for `grind` to use them as forward
rules (`wf_cont [→ VmState.getCtr_WF, VmState.wf_iff, Regs.wf_iff]`): `wf_vc` splits `st.WF` into
its fields, so a rule led by `st.WF` would never be instantiated.
-/

open Std.Do

set_option mvcgen.warning false

namespace TvmLean

@[simp] theorem OrdCregs.empty_c0 : OrdCregs.empty.c0 = none := rfl
@[simp] theorem OrdCregs.empty_c1 : OrdCregs.empty.c1 = none := rfl
@[simp] theorem OrdCregs.empty_c2 : OrdCregs.empty.c2 = none := rfl
@[simp] theorem OrdCregs.empty_c3 : OrdCregs.empty.c3 = none := rfl
@[simp] theorem OrdCregs.empty_c4 : OrdCregs.empty.c4 = none := rfl
@[simp] theorem OrdCregs.empty_c5 : OrdCregs.empty.c5 = none := rfl
@[simp] theorem OrdCregs.empty_c7 : OrdCregs.empty.c7 = none := rfl
@[simp] theorem OrdCdata.empty_stack : OrdCdata.empty.stack = #[] := rfl

theorem WF.not_mem_mk_nil {α : Type} (v : α) : ¬ v ∈ (Array.mk [] : Array α) := by simp

/-- The saved registers of a structure literal, field by field. -/
@[simp] theorem OrdCregs.wf_mk (c0 c1 c2 c3 : Option Continuation) (c4 c5 : Option Cell)
    (c7 : Option (Array Value)) :
    (OrdCregs.mk c0 c1 c2 c3 c4 c5 c7).WF ↔
      (∀ k, c0 = some k → k.WF) ∧ (∀ k, c1 = some k → k.WF) ∧
      (∀ k, c2 = some k → k.WF) ∧ (∀ k, c3 = some k → k.WF) ∧
      (∀ c, c4 = some c → c.WF) ∧ (∀ c, c5 = some c → c.WF) ∧
      (∀ t, c7 = some t → ∀ v ∈ t, v.WF) :=
  OrdCregs.wf_iff _

/-- The saved registers of a return continuation (`VM.call`): `c0` alone. -/
theorem OrdCregs.WF.ofC0 {k : Continuation} (hk : k.WF) :
    (OrdCregs.mk (some k) none none none none none none).WF := by
  simp [hk]

/-- `wf_vc` for the conditions on continuations: the continuations, saved registers and closure
stacks built are split into their fields first (`OrdCregs.wf_mk`); `wf_cont [h₁, h₂]` gives
`grind` more lemmas. -/
syntax "wf_cont" (" [" Lean.Parser.Tactic.grindParam,* "]")? : tactic

macro_rules
  | `(tactic| wf_cont) => `(tactic| wf_cont [])
  | `(tactic| wf_cont [$ts,*]) => `(tactic|
    ((try clear_local_functions)
     (try subst_vars)
     (try simp (config := { zetaDelta := true }) only [VmState.consumeGas_WF,
        VmState.consumeTupleGas_WF, VmState.consumeStackGas_WF, VmState.registerChkSgnCall_WF,
        VmState.registerCellLoad_WF, VmState.registerLibraryLoad_WF, VmState.registerCellLoads_WF,
        VmState.admitLibrary_WF, VmState.consumeGas, VmState.consumeStackGas,
        VmState.consumeTupleGas] at *)
     (try simp only [VmState.wf_iff, Regs.wf_iff, Value.wf_cont, Continuation.wf_ordinary,
        Continuation.wf_envelope, Continuation.wf_quit, Continuation.wf_excQuit,
        Continuation.wf_pushInt, Continuation.wf_whileCond, Continuation.wf_untilBody,
        Continuation.wf_repeatBody, Continuation.wf_againBody, OrdCregs.wf_mk, OrdCdata.wf_iff,
        OrdCregs.empty_c0, OrdCregs.empty_c1, OrdCregs.empty_c2, OrdCregs.empty_c3,
        OrdCregs.empty_c4, OrdCregs.empty_c5, OrdCregs.empty_c7, OrdCregs.empty_WF,
        OrdCdata.empty_WF, OrdCdata.empty_stack, Option.some.injEq, forall_eq', reduceCtorEq,
        false_implies, implies_true, true_and, and_true, WF.not_mem_mk_nil, Array.not_mem_empty,
        Array.forall_mem_append] at *)
     wf_vc [OrdCregs.wf_iff, OrdCregs.WF.ofC0, WF.not_mem_mk_nil, Array.not_mem_empty,
       OrdCdata.empty_stack, Continuation.WF.forceCdata, $ts,*]))

/-! ## Registers and saved registers -/

/-- `VmState.WF.getCtr` led by the read: `grind` (`wf_cont [→ VmState.getCtr_WF, VmState.wf_iff,
Regs.wf_iff]`) instantiates it on the read and proves `st.WF` from the fields `wf_vc` splits. -/
theorem VmState.getCtr_WF {st : VmState} {idx : Nat} {v : Value} (hv : st.getCtr idx = .ok v)
    (h : st.WF) : v.WF :=
  h.getCtr hv

/-- `VmState.WF.setCtr` led by the write, as `VmState.getCtr_WF`. -/
theorem VmState.setCtr_WF {st : VmState} {idx : Nat} {v : Value} {st' : VmState}
    (hs : st.setCtr idx v = .ok st') (h : st.WF) (hv : v.WF) : st'.WF :=
  h.setCtr hv hs

/-- `Continuation.WF.defineCtr` led by the definition: `grind` instantiates it on the definition, so
that the value defined may be any term (`SAVECTR` defines a `match` on the index). -/
theorem Continuation.defineCtr_WF {k k' : Continuation} {idx : Nat} {v : Value} {silent : Bool}
    (hd : k.defineCtr idx v silent = .ok k') (h : k.WF) (hv : v.WF) : k'.WF :=
  h.defineCtr hv hd

theorem Continuation.WF.defineC0 {k c : Continuation} (hk : k.WF) (hc : c.WF) :
    (k.defineC0 c).WF := by
  have hf := hk.forceCdata
  unfold Continuation.defineC0
  dsimp only
  split
  · rename_i heq
    rw [heq] at hf
    simp only [Continuation.wf_ordinary] at hf ⊢
    refine ⟨hf.1, hf.2.1, ?_, hf.2.2.2⟩
    have := hf.2.2.1
    split
    · exact this
    · rw [OrdCregs.wf_iff] at this ⊢
      simp_all
  · rename_i heq
    rw [heq] at hf
    simp only [Continuation.wf_envelope] at hf ⊢
    refine ⟨hf.1, ?_, hf.2.2⟩
    have := hf.2.1
    split
    · exact this
    · rw [OrdCregs.wf_iff] at this ⊢
      simp_all
  · exact hf

theorem Continuation.WF.defineC1 {k c : Continuation} (hk : k.WF) (hc : c.WF) :
    (k.defineC1 c).WF := by
  have hf := hk.forceCdata
  unfold Continuation.defineC1
  dsimp only
  split
  · rename_i heq
    rw [heq] at hf
    simp only [Continuation.wf_ordinary] at hf ⊢
    refine ⟨hf.1, hf.2.1, ?_, hf.2.2.2⟩
    have := hf.2.2.1
    split
    · exact this
    · rw [OrdCregs.wf_iff] at this ⊢
      simp_all
  · rename_i heq
    rw [heq] at hf
    simp only [Continuation.wf_envelope] at hf ⊢
    refine ⟨hf.1, ?_, hf.2.2⟩
    have := hf.2.1
    split
    · exact this
    · rw [OrdCregs.wf_iff] at this ⊢
      simp_all
  · exact hf

/-! ## `extract_cc` and calls -/

set_option maxHeartbeats 4000000 in
/-- C++ `VmState::extract_cc`: the continuation made of the rest of the code, with the bottom of the
stack as its closure stack and the registers it saves, is well-formed, and so is the state left. -/
@[spec] theorem VM.extractCc_spec (saveCr : Nat) (stackCopy ccArgs : Int) :
    ⦃fun st => ⌜st.WF⌝⦄ VM.extractCc saveCr stackCopy ccArgs
      ⦃post⟨fun k st => ⌜st.WF ∧ k.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.extractCc]
  all_goals wf_cont

set_option maxHeartbeats 4000000 in
/-- The stacks of a call (C++ `VmState::call`): the saved one and the callee's are parts of the
stack and of the closure stack. -/
@[spec] theorem VM.callComputeStacks_spec (stack captured : Stack) (nargs passArgs : Int) :
    ⦃fun st => ⌜st.WF ∧ (∀ v ∈ stack, v.WF) ∧ ∀ v ∈ captured, v.WF⌝⦄
      VM.callComputeStacks stack captured nargs passArgs
      ⦃post⟨fun r st => ⌜st.WF ∧ (∀ v ∈ r.1, v.WF) ∧ ∀ v ∈ r.2.1, v.WF⌝,
        fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.callComputeStacks]
  all_goals wf_cont

set_option maxHeartbeats 4000000 in
/-- C++ `VmState::call`: a call of a well-formed continuation keeps the state well-formed, with the
return continuation (the rest of the code, the saved stack, the old `c0`) in `c0`. -/
@[spec] theorem VM.call_spec (cont : Continuation) (passArgs retArgs : Int) :
    ⦃fun st => ⌜st.WF ∧ cont.WF⌝⦄ VM.call cont passArgs retArgs
      ⦃post⟨fun _ st => ⌜st.WF⌝, fun _ st => ⌜st.WF⌝⟩⦄ := by
  mvcgen [VM.call]
  all_goals wf_cont

end TvmLean

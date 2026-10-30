import TvmLean.Proofs.Exec.FramedConfig
import TvmLean.Proofs.Exec.Spec.MsgAddr

/-!
# `REWRITEVARADDR` on any slice, framed

`REWRITEVARADDR` parses a message address from a slice and, for an anycast address whose prefix is
shorter than the address, builds a new cell with the prefix rewritten and loads it (C++
`exec_rewrite_message_addr`, tonops.cpp). On a slice the run does not know (the body of a message),
the address is any; the step then loads a cell the run does not know either. The instruction is
framed (`TvmLean.Framed.ExecFramed`): it changes the stack, the gas, the loaded cells and libraries
only; it leaves the workchain and the address (and `-1` for `REWRITEVARADDRQ`), or `0` for
`REWRITEVARADDRQ` on a slice that is no address; it fails only with an exception of code 2 or more.

* `Steps.popSlice`, `Steps.chargeCellCreates`: the parts of the instruction as framed computations;
* `Slice.parseMessageAddr_error`, `rewriteMessageAddr_error`: their parse fails only with cell_und;
* `rewriteVarAddr_framed`, `runWith_rewriteVarAddr`, tactic `vm_rewrite_var_addr_any`.
-/

namespace TvmLean.Framed

open TvmLean

theorem Steps.popSlice : Steps VM.popSlice (fun _ s s' => ∃ v, s = s'.push v) := by
  intro st
  unfold VM.popSlice
  rw [VM.run_bind, VM.run_pop]
  split
  · rename_i h
    rw [VM.bindRes_ok]
    have hst := stack_eq_pop_push_back st.stack h
    split
    · rw [VM.run_pure]
      refine ⟨rfl, fun _ _ => ⟨_, hst⟩, ?_, fun _ => rfl⟩
      intro e he; cases he
    · rw [VM.run_throw]
      refine ⟨rfl, ?_, ?_, fun _ => rfl⟩
      · intro a ha; cases ha
      · intro e he; cases he; decide
  · rw [VM.bindRes_error]
    steps_leaf

theorem Steps.chargeCellCreates (n : Nat) : Steps (VM.chargeCellCreates n) (fun _ s s' => s' = s) := by
  intro st
  rw [VM.run_chargeCellCreates]
  split
  · rw [VmState.createsUntilOut_eq]
    refine ⟨rfl, ?_, ?_, fun _ => rfl⟩
    · intro a h; cases h
    · intro e h; cases h; decide
  · refine ⟨rfl, fun _ _ => rfl, ?_, fun _ => rfl⟩
    intro e h; cases h

end TvmLean.Framed

namespace TvmLean

/-- `Slice.parseMessageAddr` fails only with cell_und. -/
theorem Slice.parseMessageAddr_errCellUnd (s : Slice) (gv : Nat) : ErrCellUnd (s.parseMessageAddr gv) := by
  unfold Slice.parseMessageAddr
  repeat' (first
    | exact ErrCellUnd.ok _ | exact ErrCellUnd.pure _ | exact ErrCellUnd.throw
    | (refine ErrCellUnd.bind ?_ (fun _ => ?_)) | (refine ErrCellUnd.ite ?_ ?_) | split
    | (unfold Slice.takeBitsAsNatCellUnd) | (unfold Slice.parseMaybeAnycast) | (unfold Slice.takeAnycastDepth))

/-- `rewriteMessageAddr` fails only with cell_und. -/
theorem rewriteMessageAddr_errCellUnd (addr : Slice) (pfx : Value) : ErrCellUnd (rewriteMessageAddr addr pfx) := by
  unfold rewriteMessageAddr
  repeat' (first
    | exact ErrCellUnd.ok _ | exact ErrCellUnd.pure _ | exact ErrCellUnd.throw
    | (refine ErrCellUnd.bind ?_ (fun _ => ?_)) | (refine ErrCellUnd.ite ?_ ?_) | split)

end TvmLean

namespace TvmLean.Framed

open TvmLean

/-- What `REWRITEVARADDR` (`quiet` false) and `REWRITEVARADDRQ` (`quiet` true) leave on the stack
`s` under the slice: the workchain and the address (and `-1`), or `0` (`REWRITEVARADDRQ`). -/
def RewriteOk : Bool → Stack → Stack → Prop
  | false, s, s' => ∃ wc a, s' = (s.push (.int (.num wc))).push (.slice a)
  | true, s, s' => (∃ wc a, s' = ((s.push (.int (.num wc))).push (.slice a)).push (.int (.num (-1)))) ∨
      s' = s.push (.int (.num 0))

theorem Steps.rewriteVarAddr (quiet : Bool) :
    Steps (execInstrTonEnvRewriteVarAddr (.tonEnvOp (.rewriteVarAddr quiet)) (Pure.pure () : VM Unit))
      (fun _ s s'' => ∃ s0 v, s = s0.push v ∧ RewriteOk quiet s0 s'') := by
  unfold execInstrTonEnvRewriteVarAddr
  dsimp only
  refine Steps.mono (Steps.bind Steps.popSlice (fun csr => Steps.bind Steps.get (fun x =>
    (?_ : Steps _ (fun _ s s' => RewriteOk quiet s s'))))) ?_
  · split
    · cases quiet
      · simp only [Bool.false_eq_true, if_false]
        split
        · refine Steps.mono (Steps.bind (Steps.chargeCellCreates 1) (fun _ => Steps.bind (Steps.registerCellLoad _)
            (fun _ => Steps.bind (Steps.push _) (fun _ => Steps.bind (Steps.push _) (fun _ => Steps.pure _))))) ?_
          rintro _ s s'' ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, -, h5⟩
          subst_vars
          exact ⟨_, _, rfl⟩
        · refine Steps.mono (Steps.bind (Steps.pure _) (fun _ => Steps.bind (Steps.push _)
            (fun _ => Steps.bind (Steps.push _) (fun _ => Steps.pure _)))) ?_
          rintro _ s s'' ⟨_, s1, ⟨-, h1⟩, _, s3, h3, _, s4, h4, -, h5⟩
          subst_vars
          exact ⟨_, _, rfl⟩
      · simp only [if_true]
        split
        · refine Steps.mono (Steps.bind (Steps.chargeCellCreates 1) (fun _ => Steps.bind (Steps.registerCellLoad _)
            (fun _ => Steps.bind (Steps.push _) (fun _ => Steps.bind (Steps.push _)
              (fun _ => Steps.push (.int (.num (-1)))))))) ?_
          rintro _ s s'' ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, h5⟩
          subst_vars
          exact Or.inl ⟨_, _, rfl⟩
        · refine Steps.mono (Steps.bind (Steps.pure _) (fun _ => Steps.bind (Steps.push _)
            (fun _ => Steps.bind (Steps.push _) (fun _ => Steps.push (.int (.num (-1))))))) ?_
          rintro _ s s'' ⟨_, s1, ⟨-, h1⟩, _, s3, h3, _, s4, h4, h5⟩
          subst_vars
          exact Or.inl ⟨_, _, rfl⟩
    · rename_i e heq
      cases quiet
      · simp only [Bool.false_eq_true, if_false]
        have he : e = .cellUnd := (show ErrCellUnd _ by
          repeat' (first
            | exact ErrCellUnd.ok _ | exact ErrCellUnd.pure _ | exact ErrCellUnd.throw
            | exact Slice.parseMessageAddr_errCellUnd _ _ | exact rewriteMessageAddr_errCellUnd _ _
            | (refine ErrCellUnd.bind ?_ (fun _ => ?_)) | (refine ErrCellUnd.ite ?_ ?_) | split)) e heq
        subst he
        exact Steps.throw _ (by decide) _
      · simp only [if_true]
        exact Steps.mono (Steps.push _) (fun _ s s' h => Or.inr h)
  · rintro _ s s'' ⟨_, s1, ⟨v, h1⟩, _, s2, h2, h3⟩
    rw [h2] at h3
    exact ⟨s1, v, h1, h3⟩

/-- `REWRITEVARADDR`/`REWRITEVARADDRQ` runs as `execInstrTonEnvRewriteVarAddr` (the dispatch). -/
theorem rewriteVarAddr_eq (quiet : Bool) (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp (.rewriteVarAddr quiet))) st =
      ExceptT.run (execInstrTonEnvRewriteVarAddr (.tonEnvOp (.rewriteVarAddr quiet)) (Pure.pure () : VM Unit)) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

/-- **`REWRITEVARADDR`/`REWRITEVARADDRQ` on any slice is framed**: from a stack `s` with the slice on
top, the workchain and the address (and `-1`), or `0`, or an exception of code 2 or more. -/
theorem rewriteVarAddr_framed (quiet : Bool) (st : VmState) (s : Stack) (sl : Slice)
    (hs : st.stack = s.push (.slice sl)) :
    ExecFramed (.tonEnvOp (.rewriteVarAddr quiet)) (RewriteOk quiet s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.rewriteVarAddr quiet st
  rw [← rewriteVarAddr_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, v, e, hok⟩ := h2 () h
  rw [hs] at e
  obtain ⟨_, hs0⟩ := Array.push_eq_push.mp e
  rw [hs0]
  exact hok

/-- **A run from `REWRITEVARADDR`/`REWRITEVARADDRQ` on any slice.** `st` is about to run it on the
stack `s sl`: if `P` holds of every result that commits nothing and of every run from the state after
it with a stack `RewriteOk quiet s`, any gas, loaded cells and libraries, it holds of the run. -/
theorem runWith_rewriteVarAddr {st : VmState} {code rest : Slice} {s : Stack} {sl : Slice} {quiet : Bool}
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (.tonEnvOp (.rewriteVarAddr quiet), k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = s.push (.slice sl))
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hok : ∀ s' g lc ll n, n < fuel → RewriteOk quiet s s' →
      P (VmState.runWith execInstr n (after st rest s' g lc ll))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := RewriteOk quiet s)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom,
      fun st0 h1 _ => rewriteVarAddr_framed quiet st0 s sl (h1.trans hs)⟩ hr hm P hP fuel hok

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_rewrite_var_addr_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S`
written out) is about to run `REWRITEVARADDR` or `REWRITEVARADDRQ` on a slice: by
`Framed.runWith_rewriteVarAddr`, two goals: `P` of a result that commits nothing, and `P` of the runs
from the state after it with a stack `Framed.RewriteOk quiet s`, any gas, loaded cells and
libraries. -/
elab "vm_rewrite_var_addr_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_rewrite_var_addr_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  let iE ← whnfR iE
  unless iE.isAppOfArity ``Instr.tonEnvOp 1 do throwError "vm_rewrite_var_addr_any: the instruction is {iE}"
  let op ← whnfR iE.appArg!
  unless op.isAppOfArity ``TonEnvInstr.rewriteVarAddr 1 do
    throwError "vm_rewrite_var_addr_any: not REWRITEVARADDR"
  let stk ← whnfR (← mkAppM ``VmState.stack #[S])
  unless stk.isAppOfArity ``Array.push 3 do throwError "vm_rewrite_var_addr_any: the stack is not written out"
  let vsl ← whnfR (stk.getArg! 2)
  unless vsl.isAppOfArity ``Value.slice 1 do throwError "vm_rewrite_var_addr_any: no slice on top"
  let motive ← withLocalDeclD `r (mkConst ``StepResult) fun rv => do
    mkLambdaFVars #[rv] ((← kabstract t r).instantiate1 rv)
  let refl (e : Expr) : MetaM Expr := mkEqRefl e
  let hcc ← refl (← mkAppM ``VmState.cc #[S])
  let hcp ← refl (← mkAppM ``VmState.cp #[S])
  let hchain ← Exec.decideProof (← mkAppM ``LT.lt #[← whnfCore (← whnfR (← mkAppM ``VmState.chainJumps #[S])),
    mkConst ``freeNestedContJump])
  let hc2 ← refl (← mkAppM ``Regs.c2 #[← mkAppM ``VmState.regs #[S]])
  let hcom ← refl (← mkAppM ``CommittedState.committed #[← mkAppM ``VmState.cstate #[S]])
  let hr ← refl (← mkAppM ``VmState.librariesRefused #[S])
  let hm ← refl (← mkAppM ``VmState.librariesMissed #[S])
  let hs ← refl (← mkAppM ``VmState.stack #[S])
  let f ← mkAppOptM ``Framed.runWith_rewriteVarAddr #[S, none, none, stk.getArg! 1, vsl.appArg!,
    op.appArg!, hcc, hcp, hbitsNe, hverLe, hdecEx, hchain, hc2, hcom, hr, hm, hs, motive]
  let (f1, goals1) ← Exec.applyRest f 1 #[fuel]
  let (pf, goals2) ← Exec.applyRest f1 1 #[]
  let goals := goals1 ++ goals2
  unless ← isDefEq (← inferType pf) t do throwError "vm_rewrite_var_addr_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

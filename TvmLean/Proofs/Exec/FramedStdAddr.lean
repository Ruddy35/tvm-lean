import TvmLean.Proofs.Exec.FramedAddr

/-!
# `REWRITESTDADDR` on any slice, framed

`REWRITESTDADDR` (FunC `parse_std_addr`) parses a message address from a slice: an `addr_std` or
`addr_var` of 256 bits, the anycast prefix rewritten into the address, and pushes the workchain and
the address as integers (C++ `exec_rewrite_message_addr`, tonops.cpp). On a slice the run does not
know (the sender's address read from the message), the address is any. The instruction is framed
(`TvmLean.Framed.ExecFramed`): it changes the stack and the gas only; it leaves the workchain and the
address (and `-1` for `REWRITESTDADDRQ`), or `0` for `REWRITESTDADDRQ` on a slice that is no such
address; it fails only with an exception of code 2 or more (cell_und, int_ov).

* `rewriteMessageAddr256_errCellUnd`: the rewrite of the address fails only with cell_und;
* `Steps.rewriteStdAddr`, `rewriteStdAddr_framed`, `runWith_rewriteStdAddr`;
* tactic `vm_rewrite_std_addr_any`.
-/

namespace TvmLean

/-- `rewriteMessageAddr256` fails only with cell_und. -/
theorem rewriteMessageAddr256_errCellUnd (addr : Slice) (pfx : Value) : ErrCellUnd (rewriteMessageAddr256 addr pfx) := by
  unfold rewriteMessageAddr256
  repeat' (first
    | exact ErrCellUnd.ok _ | exact ErrCellUnd.pure _ | exact ErrCellUnd.throw
    | (refine ErrCellUnd.bind ?_ (fun _ => ?_)) | (refine ErrCellUnd.ite ?_ ?_) | split)

end TvmLean

namespace TvmLean.Framed

open TvmLean

/-- What `REWRITESTDADDR` (`quiet` false) and `REWRITESTDADDRQ` (`quiet` true) leave on the stack `s`
under the slice: the workchain and the address (and `-1`), or `0` (`REWRITESTDADDRQ`). -/
def RewriteStdOk : Bool → Stack → Stack → Prop
  | false, s, s' => ∃ wc a : Int, s' = (s.push (.int (.num wc))).push (.int (.num a))
  | true, s, s' => (∃ wc a : Int, s' = ((s.push (.int (.num wc))).push (.int (.num a))).push (.int (.num (-1)))) ∨
      s' = s.push (.int (.num 0))

theorem Steps.pushSmallInt (n : Int) : Steps (VM.pushSmallInt n) (fun _ s s' => s' = s.push (.int (.num n))) := by
  unfold VM.pushSmallInt
  exact Steps.push _

/-- `VM.pushIntQuiet` of a number, not quiet: the number pushed, or int_ov. -/
theorem Steps.pushIntQuiet_num (n : Int) :
    Steps (VM.pushIntQuiet (.num n) false) (fun _ s s' => s' = s.push (.int (.num n))) := by
  unfold VM.pushIntQuiet
  dsimp only
  split
  · exact Steps.push _
  · exact Steps.throw _ (by decide) _

theorem Steps.rewriteStdAddr (quiet : Bool) :
    Steps (execInstrTonEnvRewriteStdAddr (.tonEnvOp (.rewriteStdAddr quiet)) (Pure.pure () : VM Unit))
      (fun _ s s'' => ∃ s0 v, s = s0.push v ∧ RewriteStdOk quiet s0 s'') := by
  unfold execInstrTonEnvRewriteStdAddr
  dsimp only
  refine Steps.mono (Steps.bind Steps.popSlice (fun csr => Steps.bind Steps.get (fun x =>
    (?_ : Steps _ (fun _ s s' => RewriteStdOk quiet s s'))))) ?_
  · split
    · cases quiet
      · simp only [Bool.false_eq_true, if_false]
        refine Steps.mono (Steps.bind (Steps.pushSmallInt _) (fun _ => Steps.bind (Steps.pushIntQuiet_num _)
          (fun _ => Steps.pure _))) ?_
        rintro _ s s'' ⟨_, s1, h1, _, s2, h2, -, h3⟩
        subst_vars
        exact ⟨_, _, rfl⟩
      · simp only [if_true]
        refine Steps.mono (Steps.bind (Steps.pushSmallInt _) (fun _ => Steps.bind (Steps.pushIntQuiet_num _)
          (fun _ => Steps.pushSmallInt (-1)))) ?_
        rintro _ s s'' ⟨_, s1, h1, _, s2, h2, h3⟩
        subst_vars
        exact Or.inl ⟨_, _, rfl⟩
    · rename_i e heq
      cases quiet
      · simp only [Bool.false_eq_true, if_false]
        have he : e = .cellUnd := (show ErrCellUnd _ by
          repeat' (first
            | exact ErrCellUnd.ok _ | exact ErrCellUnd.pure _ | exact ErrCellUnd.throw
            | exact Slice.parseMessageAddr_errCellUnd _ _ | exact rewriteMessageAddr256_errCellUnd _ _
            | (refine ErrCellUnd.bind ?_ (fun _ => ?_)) | (refine ErrCellUnd.ite ?_ ?_) | split)) e heq
        subst he
        exact Steps.throw _ (by decide) _
      · simp only [if_true]
        exact Steps.mono (Steps.pushSmallInt _) (fun _ s s' h => Or.inr h)
  · rintro _ s s'' ⟨_, s1, ⟨v, h1⟩, _, s2, h2, h3⟩
    rw [h2] at h3
    exact ⟨s1, v, h1, h3⟩

/-- `REWRITESTDADDR`/`REWRITESTDADDRQ` runs as `execInstrTonEnvRewriteStdAddr` (the dispatch). -/
theorem rewriteStdAddr_eq (quiet : Bool) (st : VmState) :
    ExceptT.run (execInstr (.tonEnvOp (.rewriteStdAddr quiet))) st =
      ExceptT.run (execInstrTonEnvRewriteStdAddr (.tonEnvOp (.rewriteStdAddr quiet)) (Pure.pure () : VM Unit)) st := by
  simp only [TvmLean.Exec.reduceExecInstrRun]
  rfl

/-- **`REWRITESTDADDR`/`REWRITESTDADDRQ` on any slice is framed**: from a stack `s` with the slice on
top, the workchain and the address (and `-1`), or `0`, or an exception of code 2 or more. -/
theorem rewriteStdAddr_framed (quiet : Bool) (st : VmState) (s : Stack) (sl : Slice)
    (hs : st.stack = s.push (.slice sl)) :
    ExecFramed (.tonEnvOp (.rewriteStdAddr quiet)) (RewriteStdOk quiet s) st := by
  obtain ⟨h1, h2, h3, h4⟩ := Steps.rewriteStdAddr quiet st
  rw [← rewriteStdAddr_eq] at h1 h2 h3 h4
  refine ⟨h1, fun h => ?_, h3, h4⟩
  obtain ⟨s0, v, e, hok⟩ := h2 () h
  rw [hs] at e
  obtain ⟨_, hs0⟩ := Array.push_eq_push.mp e
  rw [hs0]
  exact hok

/-- **A run from `REWRITESTDADDR`/`REWRITESTDADDRQ` on any slice.** `st` is about to run it on the
stack `s sl`: if `P` holds of every result that commits nothing and of every run from the state after
it with a stack `RewriteStdOk quiet s`, any gas, loaded cells and libraries, it holds of the run. -/
theorem runWith_rewriteStdAddr {st : VmState} {code rest : Slice} {s : Stack} {sl : Slice} {quiet : Bool}
    (hcc : st.cc = .plain code) (hcp : st.cp = 0) (hbits : code.bitsRemaining ≠ 0)
    (hver : cp0RequiredVersion code.opcode24 ≤ st.globalVersion)
    (hdec : ∃ k, decodeCp0WithBits code = .ok (.tonEnvOp (.rewriteStdAddr quiet), k, rest))
    (hchain : st.chainJumps < freeNestedContJump) (hc2 : st.regs.c2 = .excQuit)
    (hcom : st.cstate.committed = false) (hr : st.librariesRefused = #[]) (hm : st.librariesMissed = #[])
    (hs : st.stack = s.push (.slice sl))
    (P : StepResult → Prop) (hP : ∀ r : StepResult, r.state.cstate.committed = false → P r) (fuel : Nat)
    (hok : ∀ s' g lc ll n, n < fuel → RewriteStdOk quiet s s' →
      P (VmState.runWith execInstr n (after st rest s' g lc ll))) :
    P (VmState.runWith execInstr fuel st) :=
  runWith_framed (Ok := RewriteStdOk quiet s)
    ⟨hcc, hcp, hbits, hver, hdec, hchain, hc2, hcom,
      fun st0 h1 _ => rewriteStdAddr_framed quiet st0 s sl (h1.trans hs)⟩ hr hm P hP fuel hok

end TvmLean.Framed

namespace TvmLean

open Lean Meta Elab Tactic in
/-- `vm_rewrite_std_addr_any`: the run in the goal (`P (VmState.runWith execInstr fuel S)`, `S`
written out) is about to run `REWRITESTDADDR` or `REWRITESTDADDRQ` on a slice: by
`Framed.runWith_rewriteStdAddr`, two goals: `P` of a result that commits nothing, and `P` of the runs
from the state after it with a stack `Framed.RewriteStdOk quiet s`, any gas, loaded cells and
libraries, and any fuel below the run's. -/
elab "vm_rewrite_std_addr_any" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some r := t.find? (·.isAppOfArity ``VmState.runWith 3) | throwError "vm_rewrite_std_addr_any: no run in the goal"
  let fuel := r.getArg! 1
  let S := r.getArg! 2
  let (_, iE, _, hbitsNe, hverLe, hdecEx) ← Exec.framedFacts S
  let iE ← whnfR iE
  unless iE.isAppOfArity ``Instr.tonEnvOp 1 do throwError "vm_rewrite_std_addr_any: the instruction is {iE}"
  let op ← whnfR iE.appArg!
  unless op.isAppOfArity ``TonEnvInstr.rewriteStdAddr 1 do
    throwError "vm_rewrite_std_addr_any: not REWRITESTDADDR"
  let stk ← whnfR (← mkAppM ``VmState.stack #[S])
  unless stk.isAppOfArity ``Array.push 3 do throwError "vm_rewrite_std_addr_any: the stack is not written out"
  let vsl ← whnfR (stk.getArg! 2)
  unless vsl.isAppOfArity ``Value.slice 1 do throwError "vm_rewrite_std_addr_any: no slice on top"
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
  let f ← mkAppOptM ``Framed.runWith_rewriteStdAddr #[S, none, none, stk.getArg! 1, vsl.appArg!,
    op.appArg!, hcc, hcp, hbitsNe, hverLe, hdecEx, hchain, hc2, hcom, hr, hm, hs, motive]
  let (f1, goals1) ← Exec.applyRest f 1 #[fuel]
  let (pf, goals2) ← Exec.applyRest f1 1 #[]
  let goals := goals1 ++ goals2
  unless ← isDefEq (← inferType pf) t do throwError "vm_rewrite_std_addr_any: the goal is not a property of the run"
  g.assign pf
  replaceMainGoal goals.toList

end TvmLean

import TvmLean.Proofs.Exec.LoopInv

/-!
# Pilot: a counting loop, with an invariant

`PUSHINT 0; PUSHCONT { DUP; PUSHINT 10; LESS }; PUSHCONT { INC }; WHILE` counts from 0 while the
counter is below 10. With the invariant `0 ≤ i ∧ i ≤ 10` of the counter (`vm_loop 1 (inv := ...)`)
`vm_run` follows the loop for any fuel: a run that ends normally ends with the stack `[10]`
(`LoopInvPilot.run_count`; out of fuel or gas it ends otherwise). With the invariant of `vm_loop`
alone the counter after the loop would be any integer that is not below 10.
-/

namespace TvmLean.Pilot.LoopInvPilot

/-- `PUSHINT 0` (`0x70`), `PUSHCONT { DUP; PUSHINT 10; LESS }` (`0x93 0x20 0x7a 0xb9`),
`PUSHCONT { INC }` (`0x91 0xa4`), `WHILE` (`0xe8`). -/
def bits : BitString :=
  #[false, true, true, true, false, false, false, false,
    true, false, false, true, false, false, true, true,
    false, false, true, false, false, false, false, false,
    false, true, true, true, true, false, true, false,
    true, false, true, true, true, false, false, true,
    true, false, false, true, false, false, false, true,
    true, false, true, false, false, true, false, false,
    true, true, true, false, true, false, false, false]

/-- The code. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- The state that runs `code` on the empty stack with 10000 gas, `c0` the end of the run and `c2`
the exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) : VmState :=
  { st with stack := #[], cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨10000, 10000, 0, 10000, 10000⟩ }

/-- A run that ends normally ends with the stack `[10]`. -/
def Done (r : StepResult) : Prop :=
  ∀ stF, r = .halt (-1) stF → stF.stack = #[].push (.int (.num 10))

/-- The commit at the end of a run keeps the stack. -/
theorem tryCommit_stack (S : VmState) : S.tryCommit.2.stack = S.stack := by
  unfold VmState.tryCommit
  split <;> rfl

/-- The end of a run (`VmState.haltResult`): normal (`-1`) only with the stack `[10]`. -/
theorem done_haltResult (c : Int) (S : VmState) (h : c = -1 → S.stack = #[].push (.int (.num 10))) :
    Done (VmState.haltResult c S) := by
  intro stF hr
  have hst := tryCommit_stack S
  unfold VmState.haltResult at hr
  generalize S.tryCommit = p at hr hst
  obtain ⟨ok, S''⟩ := p
  dsimp only at hr hst
  split at hr
  · split at hr
    · injection hr with h1 h2
      subst h2
      rw [hst]
      exact h h1
    · injection hr with h1
      exact absurd h1 (by decide)
  · injection hr with h1 h2
    subst h2
    exact h h1

/-- The normal end with the counter `10` on the stack. -/
theorem done_exit (w : Int) (S : VmState) (hS : S.stack = #[].push (.int (.num w))) (hw : w = 10) :
    Done (VmState.haltResult (-1) S) :=
  done_haltResult _ _ (fun _ => by rw [hS, hw])

/-- Any other end (out of fuel, of gas). -/
theorem done_halt (c : Int) (S : VmState) (h : c ≠ -1) : Done (.halt c S) := by
  intro stF hr
  cases hr
  exact absurd rfl h

set_option maxHeartbeats 1000000 in
/-- **The loop counts to 10.** -/
theorem run_count (fuel : Nat) (st : VmState) : Done (VmState.runWith execInstr fuel (start st)) := by
  unfold start
  vm_run
  all_goals try (vm_has_run; vm_loop 1 (inv := fun i => 0 ≤ i ∧ i ≤ 10))
  all_goals try (vm_has_run; vm_step)
  all_goals try vm_run
  all_goals first
    | exact done_halt _ _ (by decide)
    | exact done_haltResult _ _ (fun h => absurd h (by decide))
    | (simp only [VmState.runWith_zero]; exact done_halt _ _ (by decide))
    | exact done_exit _ _ rfl (by omega)

end TvmLean.Pilot.LoopInvPilot

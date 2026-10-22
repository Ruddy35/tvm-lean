import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Closure

/-!
# Pilot: calling a closure

The lemmas of `Proofs/Exec/Closure.lean` used by `vm_run`: the code
`PUSHINT 7; PUSHCONT { ADD }; SETCONTARGS 1,1; PUSHINT 5; SWAP; EXECUTE` on the stack `[x]` makes a
continuation that captured `7` and takes one argument, then calls it with `5`: the call keeps the
argument on top of the captured value (`[7, 5]`), saves `x` in the return continuation, and the
return puts it back: the run halts with the stack `[x, 12]` (`ClosurePilot.run_call`). Without the
argument (the code without `PUSHINT 5; SWAP`, on the empty stack) the call raises stk_underflow
(exit code `~~~2`, `ClosurePilot.run_noArg`).
-/

namespace TvmLean.Pilot.ClosurePilot

/-- `PUSHINT 7` (`0x77`), `PUSHCONT { ADD }` (`0x91 0xa0`), `SETCONTARGS 1,1` (`0xec11`), `PUSHINT 5`
(`0x75`), `SWAP` (`0x01`), `EXECUTE` (`0xd8`). -/
def bits : BitString :=
  #[false, true, true, true, false, true, true, true,
    true, false, false, true, false, false, false, true, true, false, true, false, false, false, false, false,
    true, true, true, false, true, true, false, false, false, false, false, true, false, false, false, true,
    false, true, true, true, false, true, false, true,
    false, false, false, false, false, false, false, true,
    true, true, false, true, true, false, false, false]

/-- The code. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- The same without `PUSHINT 5; SWAP`. -/
def bitsNoArg : BitString :=
  #[false, true, true, true, false, true, true, true,
    true, false, false, true, false, false, false, true, true, false, true, false, false, false, false, false,
    true, true, true, false, true, true, false, false, false, false, false, true, false, false, false, true,
    true, true, false, true, true, false, false, false]

/-- The code without the argument. -/
def codeNoArg : Cell := Cell.mkOrdinary bitsNoArg #[]

/-- The state that runs `c` on the stack `stk` with 1000 gas, `c0` the end of the run and `c2` the
exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) (c : Cell) (stk : Stack) : VmState :=
  { st with stack := stk, cc := .ordinary (Slice.ofCell c) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000, 1000, 0, 1000, 1000⟩ }

set_option maxHeartbeats 1000000 in
/-- **A closure called**: the captured `7` and the argument `5` added, `x` saved and put back. -/
theorem run_call (fuel : Nat) (st : VmState) (x : Int) :
    ∃ stF, VmState.runWith execInstr (fuel + 12) (start st code (#[].push (.int (.num x)))) =
        VmState.haltResult (~~~ 0) stF ∧
      stF.stack = (#[].push (.int (.num x))).push (.int (.num 12)) := by
  unfold start
  vm_run
  all_goals first
    | exact ⟨_, rfl, rfl⟩
    | (exfalso; simp_all)


/-- **A closure called without its argument**: stk_underflow (exit code `~~~2`). -/
theorem run_noArg (fuel : Nat) (st : VmState) :
    ∃ stF, VmState.runWith execInstr (fuel + 6) (start st codeNoArg #[]) = .halt (~~~ 2) stF := by
  unfold start
  vm_run
  all_goals (first | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩) | exact ⟨_, rfl⟩ | (exfalso; simp_all))

end TvmLean.Pilot.ClosurePilot

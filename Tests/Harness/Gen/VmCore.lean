import Tests.Harness.Registry
import Tests.Harness.Gen.Control

/-!
Oracle cases for paths of the C++ VM core (`crypto/vm/vm.cpp`) that the full coverage run of
2026-10-19 did not reach:

- `VmState::try_commit` / `force_commit`: c4 and c5 are committed only if both are at most 512 deep
  and of level 0 — by `COMMIT` (cell_ov otherwise) and automatically when the VM ends with exit
  code 0 or 1 (`run_inner`: the stack becomes `[0]` and the exit code `~cell_ov`);
- `VmState::call`: a call to a continuation with a saved `c0` is a jump; a closure with a captured
  stack or a fixed argument count; an empty captured stack (`BLESSARGS 0,-1`); a shared closure;
  `nargs` above the passed arguments (stk_und);
- `VmState::adjust_jump_cont`: jumps with an empty captured stack, with `nargs` equal to the depth;
- loops (`continuation.cpp`) whose body has a saved `c0`, an `UNTIL` running its body several times.
-/

namespace Tests.Gen.VmCore

open TvmLean

private def iv (n : Int) : Value := .int (.num n)

private def codeOf (prog : Array Instr) : Cell := Tests.Gen.Control.codeOf prog

private def cont (body : Array Instr) : Instr := .pushCont (Slice.ofCell (codeOf body))

private def bitsOfBytes (bs : Array Nat) : BitString := bs.foldl (fun acc b => acc ++ natToBits b 8) #[]

/-- Pruned branch of level 1 (exotic type 1, level mask 1: one hash and one depth). -/
private def pruned : Cell :=
  { bits := bitsOfBytes (#[1, 1] ++ Array.replicate 32 0x5a ++ #[0, 7]), refs := #[], special := true,
    levelMask := 1 }

/-- Chain of `n` ordinary cells, each referencing the next: depth `n`. -/
private def chain (n : Nat) : Cell :=
  (List.range n).foldl (fun c _ => Cell.mkOrdinary #[] #[c]) Cell.empty

private def commitCells : Array (String × Cell) :=
  #[("ordinary", Cell.mkOrdinary (natToBits 5 3) #[]),
    ("pruned", pruned),
    ("level1", Cell.mkOrdinary (natToBits 5 3) #[pruned]),
    ("depth512", chain 512),
    ("depth513", chain 513)]

/-- c4 or c5 set to each cell, then `COMMIT`; or the automatic commit at the end, alone, after an
earlier `COMMIT` (whose state is kept) and when the VM ends with an exception (no commit). -/
private def commitCases (suite : String) : Array OracleCase :=
  commitCells.flatMap fun (cl, c) =>
    (#[4, 5] : Array Nat).flatMap fun r =>
      (#[("commit", #[Instr.popCtr r, .tonEnvOp .commit]),
         ("auto", #[Instr.popCtr r]),
         ("commit-then-auto", #[Instr.tonEnvOp .commit, .popCtr r]),
         ("throw", #[Instr.popCtr r, .throw 5])] : Array (String × Array Instr)).map fun (pl, prog) =>
        { name := s!"oracle/commit/{pl}/c{r}/{cl}", instr := { name := suite }, program := prog,
          initStack := #[.cell c] }

private def addSlice : Value := .slice (Slice.ofCell (codeOf #[.add]))

private def progCase (suite name : String) (prog : Array Instr) (stack : Array Value) : OracleCase :=
  { name := s!"oracle/vm-core/{name}", instr := { name := suite }, codeCell? := some (codeOf prog),
    initStack := stack }

/-- A continuation `c` with saved `c0` (`SETCONTCTR c0` of a continuation pushing 99). -/
private def withSavedC0 (body : Array Instr) : Array Instr :=
  #[cont #[.pushInt (.num 99)], cont body, .setContCtr 0]

private def callCases (suite : String) : Array OracleCase :=
  match suite with
  | "EXECUTE" =>
      #[ -- empty captured stack, nargs -1: `call(cont)` goes to `call(cont, -1, -1)`, whole stack passed
        { name := "oracle/vm-core/blessargs0-empty-stack", instr := { name := suite },
          program := #[.blessArgs 0 (-1), .execute, .pushInt (.num 7)], initStack := #[iv 1, iv 2, addSlice] },
        progCase suite "closure-nargs2" #[cont #[.add], .setContArgs 0 2, .execute] #[iv 1, iv 2, iv 3],
        progCase suite "closure-captured" #[.pushInt (.num 10), cont #[.add], .setContArgs 1 (-1), .execute]
          #[iv 1, iv 2],
        -- the closure is shared (DUP): its captured stack is copied, not moved
        progCase suite "closure-captured-shared"
          #[.pushInt (.num 10), cont #[.pushInt (.num 9)], .setContArgs 1 (-1), .push 0, .execute] #[iv 1, iv 2],
        -- saved c0: the call is a jump, the code after CALLX does not run
        progCase suite "saved-c0" (withSavedC0 #[.pushInt (.num 1)] ++ #[.execute, .pushInt (.num 5)]) #[iv 3],
        progCase suite "saved-c0-closure"
          (withSavedC0 #[.add] ++ #[.setContArgs 0 2, .execute, .pushInt (.num 5)]) #[iv 3, iv 4, iv 6] ]
  | "CALLXARGS" =>
      #[ progCase suite "saved-c0-pass1"
          (withSavedC0 #[.pushInt (.num 1)] ++ #[.callxArgs 1 (-1), .pushInt (.num 5)]) #[iv 3, iv 4],
        progCase suite "saved-c0-pass0"
          (withSavedC0 #[.pushInt (.num 1)] ++ #[.callxArgs 0 2, .pushInt (.num 5)]) #[iv 3, iv 4],
        -- nargs 2 > 1 passed: stk_und
        progCase suite "nargs-above-pass" #[cont #[.add], .setContArgs 0 2, .callxArgs 1 (-1)] #[iv 1, iv 2, iv 3],
        -- nargs 1 < 3 passed: the top one is copied, two dropped, the rest kept for the return
        progCase suite "captured-skip" #[.pushInt (.num 10), cont #[.add], .setContArgs 1 1, .callxArgs 3 (-1)]
          #[iv 1, iv 2, iv 3, iv 4],
        { name := "oracle/vm-core/blessargs0-pass2", instr := { name := suite },
          program := #[.blessArgs 0 (-1), .callxArgs 2 1], initStack := #[iv 1, iv 2, iv 3, addSlice] } ]
  | "JMPX" =>
      #[{ name := "oracle/vm-core/blessargs0-empty-stack", instr := { name := suite },
          program := #[.blessArgs 0 (-1), Instr.jmpx], initStack := #[iv 1, iv 2, addSlice] },
        progCase suite "closure-nargs-eq-depth" #[cont #[.add], .setContArgs 0 2, .jmpx] #[iv 1, iv 2],
        progCase suite "closure-nargs-below-depth" #[cont #[.add], .setContArgs 0 2, .jmpx] #[iv 1, iv 2, iv 3],
        progCase suite "closure-captured-shared"
          #[.pushInt (.num 10), cont #[.pushInt (.num 9)], .setContArgs 1 (-1), .push 0, .jmpx] #[iv 1, iv 2] ]
  | _ => #[]

/-- Loops whose body has a saved `c0` (`RepeatCont`, `AgainCont`, `UntilCont::jump_w`, `VmState::until`:
the loop continuation is not installed, the body returns to its own `c0`), and an `UNTIL` loop that
runs its body three times (the uniquely held loop continuation, `jump_w`, continuing the loop). -/
private def loopCases (suite : String) : Array OracleCase :=
  match suite with
  | "REPEAT" =>
      #[progCase suite "body-saved-c0"
          (#[Instr.pushInt (.num 3)] ++ withSavedC0 #[.pushInt (.num 1)] ++ #[.contExt (.repeat false), .pushInt (.num 5)]) #[],
        progCase suite "body-3"
          #[.pushInt (.num 3), cont #[.inc], .contExt (.repeat false), .pushInt (.num 5)] #[iv 0]]
  | "AGAIN" =>
      #[progCase suite "body-saved-c0" (withSavedC0 #[.pushInt (.num 1)] ++ #[.contExt (.again false), .pushInt (.num 5)]) #[]]
  | "UNTIL" =>
      #[progCase suite "body-3" #[cont #[.dec, .push 0, .eqInt 0], .until, .pushInt (.num 7)] #[iv 3],
        progCase suite "body-saved-c0"
          (withSavedC0 #[.pushInt (.num 1), .pushInt (.num 0)] ++ #[.until, .pushInt (.num 7)]) #[]]
  | _ => #[]

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "COMMIT" => commitCases suite
  | "REPEAT" | "AGAIN" | "UNTIL" => loopCases suite
  | _ => callCases suite

end Tests.Gen.VmCore

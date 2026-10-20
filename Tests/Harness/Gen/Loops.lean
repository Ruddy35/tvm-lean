import Tests.Harness.Registry
import Tests.Harness.Gen.Control

/-!
Oracle cases that run loops and `BOOLEVAL` through their continuations (C++ `continuation.cpp`).
The suites' own cases pass `quit` continuations as the condition and the body, so the program ends
before a loop continuation is reached: `WhileCont::jump[_w]` and `PushIntCont::jump` never ran.

Here the condition and the body are inline continuations (`PUSHCONT`), and the loops run:
- the end of the condition and of the body (`WhileCont`, `UntilCont`, `RepeatCont`, `AgainCont`),
  with a non-boolean, NaN or missing flag, and with the loop continuation also on the stack (the
  shared, "slow" `jump` instead of `jump_w`);
- a condition or body that has `c0`: the loop continuation is not installed;
- a body or condition with `nargs` above the stack depth, or with a captured stack: `jump_to` runs
  `adjust_jump_cont` on every continuation it reaches (`vm.h:394-399`, version 9 and later);
- the end of a loop whose `after` has no saved `c0` (`WHILEEND`, `UNTILEND`, `REPEATEND` take the
  current `c0`), reached with `c0` set by the program: `OrdCont::jump` keeps `c0`;
- `BOOLEVAL`'s continuation returning by `RET` and `RETALT`: `PushIntCont` pushes -1 or 0 and
  jumps to the saved continuation, no instruction is run;
- chains of loop continuations ending in one `jump_to` (nested `REPEATEND`, `UNTILEND`): every jump
  after the eighth costs 1 gas (`free_nested_cont_jump`, `vm.h:391`), also out of gas.
-/

namespace Tests.Gen.Loops

open TvmLean

private def iv (n : Int) : Value := .int (.num n)

private def k (body : Array Instr) : Instr := .pushCont (Slice.ofCell (Tests.Gen.Control.codeOf body))

private def pi (n : Int) : Instr := .pushInt (.num n)

private def mk (suite name : String) (prog : Array Instr) (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {}) : OracleCase :=
  { name := s!"oracle/loops/{name}", instr := { name := suite },
    codeCell? := some (Tests.Gen.Control.codeOf prog), initStack := stack, gasLimits }

/-- `n` nested `1 REPEATEND` loops: when the innermost body ends, the `RepeatCont` of each level
(count 0) jumps to the one above, then to `quit0`: `n + 1` jumps in one `jump_to`. -/
private def nestRepeatEnd (n : Nat) (brk : Bool := false) : Array Instr :=
  (List.replicate n #[pi 1, .contExt (.repeatEnd brk)]).foldl (· ++ ·) #[]

/-- `n` nested `UNTILEND` loops whose bodies all end with a true flag. -/
private def nestUntilEnd (n : Nat) : Array Instr :=
  (List.replicate n #[.contExt (.untilEnd false)]).foldl (· ++ ·) #[] ++ (List.replicate n (pi (-1))).toArray

/-- A condition that sets `c0` to a continuation pushing 55, then jumps to the loop continuation
(taken from `c0`) with a false flag. -/
private def condJumpsToLoop : Array Instr :=
  #[.pushCtr 0, k #[pi 55], .popCtr 0, pi 0, .xchg0 1, .jmpx]

private def whileCases : Array OracleCase :=
  let s := "WHILE"
  #[mk s "count3" #[pi 3, k #[.push 0], k #[.dec], .while_, pi 99],
    mk s "cond-null" #[k #[], k #[], .while_] #[.null],
    mk s "cond-empty" #[k #[], k #[], .while_],
    mk s "cond-nan" #[k #[.pushInt .nan], k #[], .while_],
    mk s "shared" #[pi 2, k #[.pushCtr 0, .push 1], k #[.pop 0, .dec], .while_, pi 99],
    mk s "body-c0" #[pi 1, k #[.push 0], k #[pi 77], k #[.dec], .setContCtr 0, .while_, pi 99],
    mk s "cond-c0" #[pi 1, k #[pi 77], k #[.push 0], .setContCtr 0, k #[.dec], .while_, pi 99],
    mk s "body-nargs" #[pi 1, k #[.push 0], k #[.dec], .setContArgs 0 3, .while_],
    mk s "body-nargs-ok" #[pi 7, pi 1, k #[.push 0], k #[.dec], .setContArgs 0 1, .while_],
    mk s "cond-nargs" #[pi 1, pi 1, k #[], .setContArgs 0 2, k #[.pop 0], .while_],
    mk s "body-stack" #[pi 1, k #[.push 0], pi 42, k #[.dec, .pop 1, pi 0], .setContArgs 1 (-1), .while_],
    mk s "after-c0" #[k condJumpsToLoop, k #[], .while_, pi 99]]

private def whileEndCases : Array OracleCase :=
  let s := "WHILEEND"
  #[mk s "count3" #[pi 3, k #[.push 0], .contExt (.whileEnd false), .dec],
    mk s "after-nargs" #[k #[pi 7], .setContArgs 0 3, .popCtr 0, pi 1, k #[.push 0], .contExt (.whileEnd false), .dec],
    mk s "after-keeps-c0" #[k #[pi 7], .popCtr 0, k condJumpsToLoop, .contExt (.whileEnd false), pi 99]]

private def untilCases : Array OracleCase :=
  let s := "UNTIL"
  #[mk s "count3" #[pi 3, k #[.dec, .push 0, .eqInt 0], .until, pi 99],
    mk s "shared" #[pi 2, k #[.pushCtr 0, .xchg0 1, .dec, .push 0, .eqInt 0], .until, pi 99],
    mk s "body-c0" #[pi 1, k #[pi 77], k #[.dec, .push 0], .setContCtr 0, .until, pi 99],
    mk s "flag-null" #[k #[.pushNull], .until],
    mk s "flag-empty" #[k #[], .until],
    mk s "body-nargs" #[pi 0, k #[.pop 0, pi 0, pi 0], .setContArgs 0 2, .until],
    mk s "body-nargs-next" #[pi 0, pi 0, k #[.pop 0, .pop 0, pi 0], .setContArgs 0 2, .until]]

private def untilEndCases : Array OracleCase :=
  let s := "UNTILEND"
  #[mk s "count3" #[pi 3, .contExt (.untilEnd false), .dec, .push 0, .eqInt 0],
    mk s "after-keeps-c0" #[k #[pi 7], .popCtr 0, .contExt (.untilEnd false), .pushCtr 0, k #[pi 55], .popCtr 0,
      pi (-1), .xchg0 1, .jmpx],
    mk s "nest8" (nestUntilEnd 8),
    mk s "nest12" (nestUntilEnd 12)]

private def repeatCases : Array OracleCase :=
  let s := "REPEAT"
  #[mk s "shared" #[pi 2, k #[.pushCtr 0], .contExt (.repeat false), pi 99],
    mk s "body-nargs" #[pi 5, pi 2, k #[.pop 0], .setContArgs 0 1, .contExt (.repeat false)],
    mk s "after-c0" #[pi 1, k #[.pushCtr 0, k #[pi 55], .popCtr 0, .jmpx], .contExt (.repeat false), pi 99]]

private def repeatEndCases : Array OracleCase :=
  let s := "REPEATEND"
  #[mk s "after-keeps-c0" #[k #[pi 7], .popCtr 0, pi 1, .contExt (.repeatEnd false), .pushCtr 0, k #[pi 55],
      .popCtr 0, .jmpx],
    mk s "nest7" (nestRepeatEnd 7),
    mk s "nest8" (nestRepeatEnd 8),
    mk s "nest9" (nestRepeatEnd 9),
    mk s "nest12" (nestRepeatEnd 12),
    mk s "nest12-gas440" (nestRepeatEnd 12) (gasLimits := { gasLimit := 440, gasMax := 440 }),
    mk s "nest9-excquit" (#[.pushCtr 2, .popCtr 0] ++ nestRepeatEnd 9)]

private def againCases : Array OracleCase :=
  let s := "AGAIN"
  #[mk s "shared" #[pi 0, k #[.pushCtr 0, .pop 0, .inc, .push 0, .eqInt 3, .throwIf 55], .contExt (.again false)],
    mk s "shared-kept" #[pi 0, k #[.pushCtr 0, .xchg0 1, .inc, .push 0, .eqInt 3, .throwIf 55],
      .contExt (.again false)],
    mk s "body-nargs" #[pi 0, k #[.pop 0, .pop 0, pi 1], .setContArgs 0 2, .contExt (.again false)]]

private def boolevalCases : Array OracleCase :=
  let s := "BOOLEVAL"
  #[mk s "ret" #[k #[pi 5], .contExt .booleval, pi 9],
    mk s "retalt" #[k #[.retAlt], .contExt .booleval, pi 9],
    mk s "shared-c0" #[k #[.pushCtr 0], .contExt .booleval, pi 9],
    mk s "shared-c1" #[k #[.pushCtr 1, .retAlt], .contExt .booleval, pi 9],
    mk s "after-loops" #[k (nestRepeatEnd 8), .contExt .booleval, pi 9],
    mk s "jmpx" #[k #[.pushCtr 0, pi 3, .xchg0 1, .jmpx], .contExt .booleval, pi 9]]

/-- The cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "WHILE" => whileCases
  | "WHILEEND" => whileEndCases
  | "WHILEBRK" =>
      #[mk suite "retalt" #[pi 5, k #[.push 0], k #[.retAlt], .contExt (.while true), pi 99],
        mk suite "count3" #[pi 3, k #[.push 0], k #[.dec], .contExt (.while true), pi 99]]
  | "WHILEENDBRK" =>
      #[mk suite "retalt" #[pi 5, k #[.push 0], .contExt (.whileEnd true), .retAlt],
        mk suite "count3" #[pi 3, k #[.push 0], .contExt (.whileEnd true), .dec]]
  | "UNTIL" => untilCases
  | "UNTILEND" => untilEndCases
  | "UNTILBRK" =>
      #[mk suite "retalt" #[k #[.retAlt], .contExt (.until true), pi 99],
        mk suite "count3" #[pi 3, k #[.dec, .push 0, .eqInt 0], .contExt (.until true), pi 99]]
  | "UNTILENDBRK" =>
      #[mk suite "count3" #[pi 3, .contExt (.untilEnd true), .dec, .push 0, .eqInt 0]]
  | "REPEAT" => repeatCases
  | "REPEATEND" => repeatEndCases
  | "REPEATENDBRK" => #[mk suite "nest8" (nestRepeatEnd 8 true)]
  | "AGAIN" => againCases
  | "BOOLEVAL" => boolevalCases
  | _ => #[]

end Tests.Gen.Loops

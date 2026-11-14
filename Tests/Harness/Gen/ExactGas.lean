import Tests.Harness.Registry
import Tests.Harness.OracleHarness

/-!
The gas cases of the suites at the exact budget of their own run. A suite's gas case says in its
name what its budget is: `exact` (its run has just the gas it uses: it ends as it ends with ample
gas) or `exact-minus-one` / `oog` (one unit less: it runs out of gas). The suites computed those
budgets by hand, mostly as the base cost of their opcode (`computeExactGasBudget`), which a path that
loads or creates cells, throws, or runs a continuation exceeds; the variants on advanced slices
(`Tests.Gen.AdvancedSlices`) run extra code before the case's; and gas prices differ between global
versions. So at version 16, 7110 of the 27 804 such cases (on 262 suites) ran out of gas at `exact`,
or had gas to spare at `exact-minus-one`.

`fix c` gives such a case the budget of its own run on the Lean model at the process's global
version: the least `b` with which the case, its literal `PUSHINT x; SETGASLIMIT` pairs set to
`PUSHINT b; SETGASLIMIT` (in its program, or at the start of its code cell) and its own gas limit
and maximum (when it has them) set to `b`, uses at most `b` gas. Then it uses exactly `b`: the price
of `PUSHINT b` only grows with `b`. `exact` cases get `b`, `minus-one`/`oog` cases `b - 1`. The
oracle runs each case on C++ too, so a wrong gas price of the model shows there.

A gas case is a case whose name has `gas` and one of `exact`, `minus`, `oog` (any case), and does not
start with `sweep/` (`Tests.Gen.GasSweep`). A case with gas credit, with no budget to set (no literal
`PUSHINT; SETGASLIMIT`, default limits), or that does not end within its fuel is left as it is.
`Tests.suiteOracleCases` applies `fix` to a suite's own oracle cases and their advanced variants,
the fuzz (`Tests.runFuzzSpec`, `Tests.fuzzSpecCases`) to every case it generates and its variant.
-/

namespace Tests.Gen.ExactGas

open TvmLean

private def nameHas (name s : String) : Bool :=
  (name.toLower.splitOn s).length > 1

/-- Whether `name` names a gas case (see the module doc). -/
def isGasCase (name : String) : Bool :=
  !name.startsWith "sweep/" && nameHas name "gas" &&
    (nameHas name "exact" || nameHas name "minus" || nameHas name "oog")

/-- Whether the gas case `name` wants one unit less than its run uses. -/
def wantsMinusOne (name : String) : Bool :=
  nameHas name "minus" || nameHas name "oog"

private def defaultLimits : OracleGasLimits := {}

private def hasOwnLimits (c : OracleCase) : Bool :=
  c.gasLimits.gasLimit != defaultLimits.gasLimit || c.gasLimits.gasMax != defaultLimits.gasMax

/-- Every literal `PUSHINT x; SETGASLIMIT` of the program with `x := b`, and whether there was one. -/
private def setPushes (b : Int) : List Instr → List Instr × Bool
  | .pushInt (.num _) :: .tonEnvOp .setGasLimit :: rest =>
      let (r, _) := setPushes b rest
      (.pushInt (.num b) :: .tonEnvOp .setGasLimit :: r, true)
  | i :: rest =>
      let (r, f) := setPushes b rest
      (i :: r, f)
  | [] => ([], false)

/-- The code cell with its leading `PUSHINT x; SETGASLIMIT` set to `PUSHINT b`, if it has one. -/
private def setCellPush (b : Int) (cell : Cell) : Option Cell :=
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (.pushInt (.num _), _, s1) =>
      match decodeCp0WithBits s1 with
      | .ok (.tonEnvOp .setGasLimit, _, s2) =>
          match assembleCp0 [.pushInt (.num b), .tonEnvOp .setGasLimit] with
          | .ok pre =>
              let rem := s2.toCellRemaining
              if pre.bits.size + rem.bits.size ≤ 1023 && pre.refs.size + rem.refs.size ≤ 4 then
                some (Cell.mkOrdinary (pre.bits ++ rem.bits) (pre.refs ++ rem.refs))
              else none
          | .error _ => none
      | _ => none
  | _ => none

/-- The case with the budget `b` (see the module doc); with `ample`, its own limits stay 10^6 (only
its `SETGASLIMIT` uses `b`), to measure its run. `none` if it has no budget to set. -/
private def withBudget (c : OracleCase) (b : Int) (ample : Bool) : Option OracleCase :=
  let limits : OracleGasLimits :=
    if ample || !hasOwnLimits c then c.gasLimits else { gasLimit := b, gasMax := b, gasCredit := 0 }
  match c.codeCell? with
  | some cell =>
      match setCellPush b cell with
      | some cell' => some { c with codeCell? := some cell', gasLimits := limits }
      | none => if hasOwnLimits c then some { c with gasLimits := limits } else none
  | none =>
      let (prog, found) := setPushes b c.program.toList
      if found || hasOwnLimits c then some { c with program := prog.toArray, gasLimits := limits }
      else none

/-- The gas the Lean model uses on the case `c` run with ample gas but the budget `b` (`none` if it
does not end within its fuel). -/
private def gasUsed (c : OracleCase) (b : Int) : Option Int := do
  let c' ← withBudget c b true
  let c' := if hasOwnLimits c then { c' with gasLimits := defaultLimits } else c'
  match oracleLeanInitState c' with
  | .error _ => none
  | .ok st0 =>
      match VmState.run c'.fuel st0 with
      | .halt _ st => some st.gas.gasConsumed
      | .continue _ => none

/-- The least budget `b` with which the case uses at most `b` gas (see the module doc). -/
def exactBudget? (c : OracleCase) : Option Int := do
  -- from above: the run never runs out of gas there, and `gasUsed c b` falls with `b`
  let mut b : Int := 1_000_000
  for _ in [0:24] do
    let g ← gasUsed c b
    if g == b then break
    b := g
  -- the least such `b` (a smaller `PUSHINT` can make a smaller budget enough)
  for _ in [0:64] do
    match gasUsed c (b - 1) with
    | some g => if g ≤ b - 1 then b := b - 1 else break
    | none => break
  if gasUsed c b == some b then pure b else none

/-- The gas case `c` at the exact budget of its run, or at one unit less (see the module doc). -/
def fix (c : OracleCase) : OracleCase :=
  if !isGasCase c.name || c.gasLimits.gasCredit != 0 then c
  else
    match exactBudget? c with
    | none => c
    | some b =>
        let b' := if wantsMinusOne c.name then b - 1 else b
        (withBudget c b' false).getD c

end Tests.Gen.ExactGas

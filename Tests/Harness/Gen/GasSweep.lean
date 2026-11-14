import Tests.Harness.Registry
import Tests.Harness.OracleHarness

/-!
Small-gas variants of every suite's own oracle cases, run for every suite
(`Tests.suiteOracleCases`). The suites run almost every case with the gas limit 10^6, so a run that
ends out of gas inside an instruction is rare, while C++ ends such a run in several ways:

- before version 4 `VmState::consume_gas` only subtracts (crypto/vm/vm.h:203-209): the handler runs
  to its end, building its whole result, and the `gas.check()` that ends the step finds the gas
  gone (vm.cpp:485); `run` then ends the VM with the gas consumed as its stack (vm.cpp:526-533);
- from version 4 it throws at the first charge that leaves the gas below zero: the instruction's
  basic charge (`gas_per_instr` plus its bits, opctable.cpp:156-303), a cell load or creation
  (vm.cpp:680, 688), stack or tuple entries (vm.h:210-225), a charge of the handler's own;
- `consume_gas_chk` throws at every version: the exception (`throw_exception`, vm.cpp:389, 399),
  the implicit `JMPREF` and `RET` (vm.cpp:467, 472).

For each suite, up to `maxCases` of its oracle cases are taken as bases, spread over the list (from
each of `maxCases` equal parts, the first of at most `scanMax` cases that runs on the model to its end
without running out of gas). Each base runs on the Lean model from the state `runOracleCase` starts it
from (`oracleLeanInitState`) at versions 16 and 3, and the gas limits come from the model's own gas
use (a wrong gas use of the model still shows: the oracle compares each case with C++):

- `end`: one below the gas consumed at the end of the base's main step (the first that runs the
  suite's opcode; without one, the instruction step that charges the most): before version 4 the
  handler runs to its end and the step's gas check fails, from version 4 the step's last charge
  fails; when the instruction throws, that is the exception charge.
- `basic`: one below the instruction's basic charge: from version 4 the step ends before the handler.
- `needed`: one below the gas the whole run consumes: the run's last charge fails (mostly the implicit
  `RET` after the instruction).
- `charge`: one below each charge inside the main step after the basic one (a cell load or creation,
  stack or tuple entries, the exception, ...): the gas consumed when a run at version 16 ends out of
  gas there. A run at version 16 ends out of gas at the first charge that exceeds its limit, with that
  charge's total, so the total it ends with is a nondecreasing step function of the limit, whose
  values on the main step's limits `valuesIn` finds by bisection (at most `chargeBudget` runs).

The `end` and `needed` limits are taken from both versions when they differ. The cases are the same
at every version and run at every version 0..16 like the suite's other cases: from version 4 the
limits fall at the charges, before version 4 every limit inside the main step runs the handler to its
end. Each case has `gasLimit = gasMax = limit` and no credit: `runOracleCase` gives `runvmx` the limit
plus the credit as its limit, which `interpret_run_vm` also takes as the maximum
(crypto/fift/words.cpp:2662-2678), so the model gets the limits C++ gets and `ACCEPT` or `SETGASLIMIT`
meet the same maximum on both sides.

Order, at most `maxCases` cases per suite: the first base's `end`, `basic` and `needed` cases; then the
other bases' `end` cases (the handler's whole run before version 4 on different operands) alternating
with the `charge` cases of the `chargeBases` bases whose main step charges the most after its basic
charge.
-/

namespace Tests.Gen.GasSweep

open TvmLean

/-- At most this many cases per suite. -/
def maxCases : Nat := 8

/-- Cases tried in each part of a suite's list for a base. -/
def scanMax : Nat := 4

/-- Bases whose charges inside the main step are searched (those whose main step charges the most
after the basic charge). -/
def chargeBases : Nat := 2

/-- Runs on the model per base for the charges inside its main step. -/
def chargeBudget : Nat := 40

/-- The exit code of the model's runs that end out of gas (`VmState.outOfGasHalt`: C++ `run` returns
`out_of_gas` without `~`). -/
def outOfGasExit : Int := Excno.outOfGas.toInt

/-- One step of a run on the model: the gas consumed before and after it, the basic charge of the
instruction it runs (`instrGas`: `gas_per_instr` plus its bits; 0 for a step without one: an implicit
`RET` or `JMPREF`, a jump into a continuation) and whether that instruction is of the suite's opcode. -/
structure StepGas where
  before : Int
  after : Int
  basic : Int
  own : Bool
  deriving Inhabited

/-- The gas use of a run on the model: its main step (the first that runs the suite's opcode, else the
instruction step that charges the most), whether that step runs the suite's opcode, the exit code and
the gas consumed at the end. -/
structure RunGas where
  main : StepGas
  ownFound : Bool
  exit : Int
  consumed : Int
  deriving Inhabited

/-- `st` at global version `v`, with the gas limit and maximum `limit` and no credit (as `runvmx` runs
a case of limit `limit`). -/
def atLimit (st : VmState) (v : Nat) (limit : Int) : VmState :=
  { st with globalVersion := v, gas := GasLimits.ofLimits limit limit 0 }

/-- The instruction the next step of `st` runs and its length in bits: an ordinary continuation with
code left, an opcode of codepage 0 that decodes and exists at the version of `st` (as
`VmState.stepOnceWith` runs it). -/
def nextInstr? (st : VmState) : Option (Instr × Nat) :=
  match st.cc with
  | .ordinary code _ _ _ =>
      if st.cp == 0 && decide (code.bitsRemaining > 0) then
        let head : BitString := code.readBits (Nat.min 24 code.bitsRemaining)
        let opcode24 : Nat := bitsToNat (head ++ Array.replicate (24 - head.size) false)
        if st.globalVersion < cp0RequiredVersion opcode24 then none
        else
          match decodeCp0WithBits code with
          | .ok (i, bits, _) => some (i, bits)
          | .error _ => none
      else none
  | _ => none

/-- The gas use of the run from `st0` (at most `fuel` steps); `none` if it does not halt within them
or runs no instruction. -/
def runGas (isOwn : Instr → Bool) (fuel : Nat) (st0 : VmState) : Option RunGas := Id.run do
  let mut st := st0
  let mut own? : Option StepGas := none
  let mut big? : Option StepGas := none
  for _ in [0:fuel] do
    let instr? := nextInstr? st
    let basic : Int := match instr? with
      | some (i, bits) => instrGas i bits
      | none => 0
    let o : Bool := match instr? with
      | some (i, _) => isOwn i
      | none => false
    let r := st.step
    let s : StepGas := { before := st.gas.gasConsumed, after := r.state.gas.gasConsumed, basic, own := o }
    if o && own?.isNone then
      own? := some s
    let bigger : Bool := match big? with
      | some b => decide (0 < basic) && decide (s.after - s.before > b.after - b.before)
      | none => decide (0 < basic)
    if bigger then
      big? := some s
    match r with
    | .continue st' => st := st'
    | .halt e st' =>
        return match own?, big? with
          | some m, _ => some { main := m, ownFound := true, exit := e, consumed := st'.gas.gasConsumed }
          | none, some m => some { main := m, ownFound := false, exit := e, consumed := st'.gas.gasConsumed }
          | none, none => none
  return none

/-- The gas consumed at the end of the run from `st0` at version `v` under the limit `limit` if it
ends out of gas; `none` if it has gas enough. -/
def outOfGasAt (fuel : Nat) (st0 : VmState) (v : Nat) (limit : Int) : Option Int :=
  match VmState.run fuel (atLimit st0 v limit) with
  | .halt e st => if e == outOfGasExit then some st.gas.gasConsumed else none
  | .continue _ => none

/-- The values of a nondecreasing `f` on the limits `[lo, hi]`, given `flo = f lo` and `fhi = f hi`,
found by bisection with at most `budget` more calls of `f` (fewer values when it runs out), and the
budget left. `depth` bounds the recursion: an interval of up to `2^depth` limits is split down to
single limits. -/
def valuesIn (f : Int → Option Int) :
    (depth budget : Nat) → (lo hi : Int) → (flo fhi : Option Int) → Array (Option Int) × Nat
  | 0, budget, _, _, flo, fhi => (#[flo, fhi], budget)
  | depth + 1, budget, lo, hi, flo, fhi =>
      if flo = fhi ∨ hi ≤ lo + 1 ∨ budget = 0 then (#[flo, fhi], budget)
      else
        let mid := lo + (hi - lo) / 2
        let fm := f mid
        let (xs, b1) := valuesIn f depth (budget - 1) lo mid flo fm
        let (ys, b2) := valuesIn f depth b1 mid hi fm fhi
        (xs ++ ys, b2)

/-- The integers of `xs`, ascending, each once. -/
def sortedDistinct (xs : Array Int) : Array Int :=
  (xs.qsort (fun a b => decide (a < b))).foldl
    (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

/-- The charges inside the main step of the run `r` from `st0` after its basic charge, as the gas
consumed when the run at version 16 ends out of gas there (at most `budget` runs). -/
def innerCharges (fuel : Nat) (st0 : VmState) (r : RunGas) (budget : Nat) : Array Int :=
  let m := r.main
  let lo := m.before + m.basic
  let hi := m.after - 1
  if m.basic ≤ 0 ∨ hi < lo then #[]
  else
    let f := outOfGasAt fuel st0 16
    let (vals, _) := valuesIn f 64 budget lo hi (f lo) (f hi)
    sortedDistinct ((vals.filterMap id).filter fun c => decide (lo < c ∧ c < m.after))

/-- A base: the case, its index in the suite's list, the state its runs start from and its runs at
versions 16 and 3 under its own limits. -/
structure Base where
  idx : Nat
  oc : OracleCase
  st0 : VmState
  v16 : RunGas
  v3 : Option RunGas

/-- The case `c` (index `idx`) as a base: its runs on the model at versions 16 and 3 under its own
limits (`runvmx` gets the limit plus the credit), if the run at version 16 halts within the case's
fuel without running out of gas. The run at version 3 is kept if it does too. -/
def base? (isOwn : Instr → Bool) (idx : Nat) (c : OracleCase) : Option Base := do
  let st0 ← (oracleLeanInitState c).toOption
  let limit := c.gasLimits.gasLimit + c.gasLimits.gasCredit
  let r16 ← runGas isOwn c.fuel (atLimit st0 16 limit)
  guard (r16.exit != outOfGasExit)
  let r3 := (runGas isOwn c.fuel (atLimit st0 3 limit)).filter fun r => r.exit != outOfGasExit
  pure { idx, oc := c, st0, v16 := r16, v3 := r3 }

/-- Up to `maxCases` bases among `cases`: from each of `maxCases` equal parts of the list (all of it
when shorter), the first of at most `scanMax` cases that is a base. -/
def pickBases (isOwn : Instr → Bool) (cases : Array OracleCase) : Array Base := Id.run do
  let n := cases.size
  let m := Nat.min n maxCases
  let mut out : Array Base := #[]
  for k in [0:m] do
    let s := k * n / m
    let e := Nat.min ((k + 1) * n / m) (s + scanMax)
    let mut found := false
    for i in [s:e] do
      if !found then
        if let some c := cases[i]? then
          if let some b := base? isOwn i c then
            out := out.push b
            found := true
  return out

/-- The `end` limits of a base: of its run at version 16, and of its run at version 3 when that one's
main step runs the suite's opcode. -/
def endLimits (b : Base) : Array (String × Int) :=
  #[("end", b.v16.main.after - 1)] ++
    (match b.v3 with
     | some r => if r.ownFound then #[("end", r.main.after - 1)] else #[]
     | none => #[])

/-- The limits of the first base: `end`, `basic`, `needed` (of the run at version 3 too when its main
step runs the suite's opcode). -/
def firstLimits (b : Base) : Array (String × Int) :=
  let m := b.v16.main
  endLimits b ++
    (if m.basic > 0 then #[("basic", m.before + m.basic - 1)] else #[]) ++
    #[("needed", b.v16.consumed - 1)] ++
    (match b.v3 with
     | some r => if r.ownFound then #[("needed", r.consumed - 1)] else #[]
     | none => #[])

/-- The `charge` limits of a base. -/
def chargeLimits (b : Base) : Array (String × Int) :=
  (innerCharges b.oc.fuel b.st0 b.v16 chargeBudget).map fun c => ("charge", c - 1)

/-- The gas the main step of a base charges after the instruction's basic charge. -/
def extraGas (b : Base) : Int :=
  b.v16.main.after - b.v16.main.before - b.v16.main.basic

/-- The `chargeBases` bases whose main step charges the most after its basic charge (some gas). -/
def chargeBasesOf (bases : Array Base) : Array Base :=
  let more (a b : Base) : Bool :=
    decide (extraGas a > extraGas b) || (extraGas a == extraGas b && decide (a.idx < b.idx))
  ((bases.filter fun b => decide (0 < extraGas b)).qsort more).extract 0 chargeBases

/-- `xs[0], ys[0], xs[1], ys[1], ...`, the rest of the longer one at the end. -/
def interleave {α : Type} (xs ys : Array α) : Array α := Id.run do
  let mut out : Array α := #[]
  for i in [0:Nat.max xs.size ys.size] do
    if h : i < xs.size then out := out.push xs[i]
    if h : i < ys.size then out := out.push ys[i]
  return out

/-- The first elements of the arrays of `xss`, then their second ones, and so on. -/
def roundRobin {α : Type} (xss : Array (Array α)) : Array α := Id.run do
  let mut out : Array α := #[]
  for i in [0:xss.foldl (fun a xs => Nat.max a xs.size) 0] do
    for xs in xss do
      if h : i < xs.size then out := out.push xs[i]
  return out

/-- The case `c` with the gas limit and maximum `limit` and no credit. -/
def variant (c : OracleCase) (kind : String) (limit : Int) : OracleCase :=
  { c with
    name := s!"sweep/gas/{kind}-{limit}/{c.name}"
    gasLimits := { gasLimit := limit, gasMax := limit, gasCredit := 0 } }

/-- The small-gas cases of a suite with the oracle cases `cases`, `isOwn` telling the instructions of
its opcode (see the module doc). -/
def casesFor (isOwn : Instr → Bool) (cases : Array OracleCase) : Array OracleCase := Id.run do
  let bases := pickBases isOwn cases
  let some b0 := bases[0]? | return #[]
  let ends := (bases.extract 1 bases.size).flatMap fun b => (endLimits b).map fun l => (b, l)
  let charges := roundRobin ((chargeBasesOf bases).map fun b => (chargeLimits b).map fun l => (b, l))
  let order := (firstLimits b0).map (fun l => (b0, l)) ++ interleave ends charges
  let mut out : Array OracleCase := #[]
  let mut seen : Array (Nat × Int) := #[]
  for (b, kind, limit) in order do
    if decide (out.size < maxCases) && decide (0 ≤ limit) && !seen.contains (b.idx, limit) then
      seen := seen.push (b.idx, limit)
      out := out.push (variant b.oc kind limit)
  return out

end Tests.Gen.GasSweep

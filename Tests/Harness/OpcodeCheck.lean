import Tests.Harness.Runner
import TvmLean.Spec.Index

/-!
Check that every suite's oracle runs the opcode the suite is named after (`--opcode-check`).

A suite written while the assembler rejected its form ran a neighbour instead (`PUSHINT n; PLDIX`
for `PLDI n`, the variable shift for `LSHIFT`, ...); C++ runs both through one `exec_*` function,
so neither the oracle nor the C++ function coverage shows that the suite's own opcode is untested.
The opcode of a suite is the prefix of its row in `TvmLean.Spec.Index`; the code of every case run
for the suite (`suiteOracleCases`, references included) is decoded and its instructions compared.
-/

namespace Tests

open TvmLean

/-- The encodings of the instructions of `c` and of the cells below it, up to `fuel` cells deep. -/
private def instrEncodings : Nat → Cell → Array BitString
  | 0, _ => #[]
  | fuel + 1, c => Id.run do
      let mut out : Array BitString := #[]
      let mut s := Slice.ofCell c
      for _ in [0:c.bits.size] do
        if s.bitsRemaining == 0 then break
        match decodeCp0WithBits s with
        | .ok (_, used, s') =>
            if used == 0 then break
            out := out.push (c.bits.extract s.bitPos (s.bitPos + used))
            s := s'
        | .error _ => break
      for r in c.refs do
        out := out ++ instrEncodings fuel r
      return out

/-- Whether the code of `c` (its code cell, else its assembled program) has an instruction whose
encoding begins with one of `pfxs`. -/
private def caseHasOpcode (pfxs : Array BitString) (c : OracleCase) : Bool :=
  let code? : Option Cell :=
    match c.codeCell? with
    | some cc => some cc
    | none => (assembleCp0 c.program.toList).toOption
  match code? with
  | none => false
  | some cc =>
      (instrEncodings 8 cc).any fun e =>
        pfxs.any fun p => e.size ≥ p.size && e.extract 0 p.size == p

/-- Prints the suites whose oracle never runs their own opcode; returns how many there are. -/
def opcodeCheck : IO Nat := do
  let suites ← registeredSuites
  let mut bad := 0
  for suite in suites do
    let cases := suiteOracleCases suite
    if cases.isEmpty then continue
    match allInstrRows.find? (fun r => r.id.name == suite.id.name) with
    | none => pure ()
    | some row =>
        if !cases.any (caseHasOpcode (specRowPrefixes row)) then
          bad := bad + 1
          IO.println s!"[opcode-check] {suite.id.name}: no oracle case runs its opcode"
  IO.println s!"opcode check: suites={suites.size} without their opcode={bad}"
  return bad

/-- Prints, for each suite in which fewer than half of the oracle cases have their own opcode in
their code (`--opcode-share`), how many do, fewest first: the suites whose own opcode is tested by a
part of their cases only, and how many cases of all suites have it. With `filter?` (`--filter S`), the names of the cases of suite `S` without
it. -/
def opcodeShare (filter? : Option String := none) : IO Unit := do
  let suites ← registeredSuites
  let mut rows : Array (String × Nat × Nat) := #[]
  for suite in suites do
    let cases := suiteOracleCases suite
    if cases.isEmpty then continue
    match allInstrRows.find? (fun r => r.id.name == suite.id.name) with
    | none => pure ()
    | some row =>
        let own := (cases.filter (caseHasOpcode (specRowPrefixes row))).size
        if filter? == some suite.id.name then
          for c in cases do
            if !caseHasOpcode (specRowPrefixes row) c then IO.println s!"[opcode-share] {suite.id.name} without: {c.name}"
        if 2 * own < cases.size then rows := rows.push (suite.id.name, own, cases.size)
  let sorted := rows.qsort fun (_, a, n) (_, b, m) => a * m < b * n
  -- the cases of every suite, for how many cases of all suites run each of these opcodes
  let mut all : Array OracleCase := #[]
  for suite in suites do
    all := all ++ suiteOracleCases suite
  for (name, own, n) in sorted do
    let pfxs := match allInstrRows.find? (fun r => r.id.name == name) with
      | some row => specRowPrefixes row
      | none => #[]
    let anywhere := (all.filter (caseHasOpcode pfxs)).size
    IO.println s!"[opcode-share] {name}: {own} / {n}; in all suites {anywhere}"
  IO.println s!"opcode share: suites={suites.size} with fewer than half their cases on their opcode={rows.size}"

end Tests

import TvmLean.Semantics.Exec.Common

namespace TvmLean

inductive StepResult : Type
  | continue (st : VmState)
  | halt (exitCode : Int) (st : VmState)
  deriving Repr

def VmState.outOfGasHalt (st : VmState) : StepResult :=
  -- Match `VmState::run()` behavior: unhandled out-of-gas returns the plain
  -- exception number (13) and leaves `stack=[gas_consumed]`.  Note that the
  -- Fift `runvmx` primitive applies `~` to this return value, so the oracle
  -- observes `-14` for out-of-gas.
  let consumed := st.gas.gasConsumed
  let st' := { st with stack := #[.int (.num consumed)], steps := st.steps + 1 }
  StepResult.halt Excno.outOfGas.toInt st'

/-- One jump of C++ `VmState::jump_to` (vm.h:386-401): from version 9 every jump of a chain after
the first `freeNestedContJump` costs 1 gas (`consume_gas`, out of gas at once). -/
def VmState.countJump (st : VmState) : VmState :=
  let n := st.chainJumps + 1
  let st := { st with chainJumps := n }
  if n > freeNestedContJump ∧ st.globalVersion ≥ 9 then st.consumeGas 1 else st

/-- The step jumped from a continuation that is not ordinary to `st.cc`, in the same `jump_to`. -/
def VmState.jumped (st : VmState) : StepResult :=
  let st := st.countJump
  if st.gasExhaustedNow then st.outOfGasHalt else .continue st

/-- Gas ran out entering a continuation in a step that starts with the state `before`: the stack
gas of the jump is checked at once from version 4, else by the `gas.check()` that ends the step
that jumped. A step starts out of gas only before version 4, after the jump to the exception
handler (`VmState.raiseException`), which no check follows: the handler's first instruction runs. -/
def VmState.ranOutEntering (before after : VmState) : Bool :=
  decide (after.gas.gasRemaining < 0) && decide (0 ≤ before.gas.gasRemaining)

/-- C++ `adjust_jump_cont` (vm.cpp:259-260), run by every jump (`jump`, and `jump_to` for each
continuation of a chain): a continuation expecting more arguments than the stack holds is not
entered, stk_und. The model applies the jump's control data when the continuation is entered (the
next step), so the check is made there; `VM.jump` and `VM.call` apply it at once and clear it. -/
def OrdCdata.needsMoreArgs (cdata : OrdCdata) (depth : Nat) : Bool :=
  decide (0 ≤ cdata.nargs) && cdata.nargs.toNat > depth

/-- The control data a continuation is entered with. C++ runs `adjust_jump_cont` (closure stack and
`nargs`) on the first continuation of a jump (`VmState::jump`, `throw_exception`) and, from version
9, on every continuation `jump_to` reaches after it (vm.h:394-399). Before version 9 a continuation
reached in a chain is entered by its own `jump` alone (`OrdCont::jump`, `ArgContExt::jump`): its save
list is applied, its stack and `nargs` are not. `chainJumps` is 0 on the first continuation. -/
def VmState.enteredCdata (st : VmState) (cdata : OrdCdata) : OrdCdata :=
  if st.globalVersion ≥ 9 ∨ st.chainJumps = 0 then cdata else OrdCdata.empty

def VmState.applyCregsCdata (st : VmState) (cregs : OrdCregs) (cdata : OrdCdata) : VmState :=
  -- Mirrors C++ `adjust_cr(save)` + `adjust_jump_cont` stack truncation/merge on jump/call.
  let regs0 := st.regs
  let regs1 := match cregs.c0 with | some c0 => { regs0 with c0 := c0 } | none => regs0
  let regs2 := match cregs.c1 with | some c1 => { regs1 with c1 := c1 } | none => regs1
  let regs3 := match cregs.c2 with | some c2 => { regs2 with c2 := c2 } | none => regs2
  let regs4 := match cregs.c3 with | some c3 => { regs3 with c3 := c3 } | none => regs3
  let regs5 := match cregs.c4 with | some c4 => { regs4 with c4 := c4 } | none => regs4
  let regs6 := match cregs.c5 with | some c5 => { regs5 with c5 := c5 } | none => regs5
  let regs7 := match cregs.c7 with | some c7 => { regs6 with c7 := c7 } | none => regs6
  let st1 : VmState := { st with regs := regs7 }
  let stack0 := st1.stack
  let (stack1, truncated) : Stack × Bool :=
    if decide (0 ≤ cdata.nargs) then
      let copy : Nat := cdata.nargs.toNat
      if copy < stack0.size then
        (stack0.extract (stack0.size - copy) stack0.size, true)
      else
        (stack0, false)
    else
      (stack0, false)
  let st1' : VmState := { st1 with stack := stack1 }
  if cdata.stack.isEmpty then
    -- C++ `adjust_jump_cont` charges stack gas only if it actually truncates the stack.
    if truncated then
      st1'.consumeStackGas stack1.size
    else
      st1'
  else
    -- C++ `adjust_jump_cont` / `call` merges the continuation's saved stack and then charges stack gas for
    -- the resulting depth via `consume_stack_gas(new_stk)`.
    let newStack := cdata.stack ++ stack1
    ( { st1' with stack := newStack } ).consumeStackGas newStack.size

/-- C++ `run_inner` handling an exception `e` raised in a step: `throw_exception(e)` makes the stack
`[0, e]`, charges the exception gas (`consume_gas_chk`: out of gas at once) and jumps to `c2`. If that
jump fails (`c2` expects more arguments), the VM ends with stk_und ("exception while handling
exception"). The jump (`VmState::jump`) applies the closure stack of `c2` at once
(`adjust_jump_cont`), its stack gas `consume_gas`: out of gas at once from version 4; before, no
`gas.check()` follows this jump (it is made after the step's check), and the handler's first
instruction runs. The jump to `c2` starts a new chain of jumps. -/
def VmState.raiseException (st : VmState) (e : Int) : StepResult :=
  let st := { st with steps := st.steps + 1 }
  let stExc := (st.throwException e).consumeGas exceptionGasPrice
  if decide (stExc.gas.gasRemaining < 0) then
    stExc.outOfGasHalt
  else if stExc.excHandlerNeedsMoreArgs then
    .halt (~~~ Excno.stkUnd.toInt) stExc
  else
    let stJ :=
      match stExc.cc with
      | .ordinary code saved cregs cdata =>
          { stExc.applyCregsCdata OrdCregs.empty cdata with cc := .ordinary code saved cregs OrdCdata.empty }
      | .envelope ext cregs cdata =>
          { stExc.applyCregsCdata OrdCregs.empty cdata with cc := .envelope ext cregs OrdCdata.empty }
      | _ => stExc
    if stJ.gasExhaustedNow then stJ.outOfGasHalt else .continue { stJ with chainJumps := 0 }

def cp0InvOpcodeGasBits (code : Slice) : Nat :=
  -- Approximate C++ opcode-table charging for invalid/too-short opcodes:
  -- decode the same prefix after zero-padding bits so short fixed/ext opcodes
  -- report their declared bit length (e.g. 16/24) instead of falling back to 8.
  let bits0 : BitString := code.readBits code.bitsRemaining
  -- Some cp0 opcodes (e.g. PUSHSLICE_REFS/LONG, PUSHCONT) validate the presence of
  -- inline payload bits and refs *after* their header is recognized. When the code
  -- slice is truncated in the payload, C++ still charges based on the matched
  -- opcode entry width (header bits), not the 8-bit fallback.
  --
  -- To approximate this, always pad enough bits so the decoder can proceed past
  -- payload-length guards and report the header width.
  let padBitsTo : Nat := 2048
  let bitsPad : BitString :=
    if bits0.size < padBitsTo then
      bits0 ++ Array.replicate (padBitsTo - bits0.size) false
    else
      bits0
  let refs0 : Array Cell := code.cell.refs.extract code.refPos code.cell.refs.size
  let refsPad : Array Cell :=
    if refs0.size < 4 then
      refs0 ++ Array.replicate (4 - refs0.size) Cell.empty
    else
      refs0
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary bitsPad refsPad)) with
  | .ok (_instr, totBits, _rest) => totBits
  | .error _ =>
      -- If we still can't match a real opcode-table entry even after padding,
      -- treat this as a dummy `inv_opcode` dispatch (C++ charges `gas_per_instr`
      -- without per-bit cost in this case).
      0

/-- One step of C++ `VmState::run`: the jump into `cc` if it is not an ordinary continuation that
is running, else the next instruction of `cc` (run by `exec`), its implicit `RET` or `JMPREF`; the
libraries of `librariesRefused` are refused (`VmState.stepWith` runs it). -/
def VmState.stepOnceWith (exec : Instr → VM Unit) (st : VmState) : StepResult :=
  match st.cc with
  | .quit n =>
      -- C++ `QuitCont::jump`: the VM ends with exit code `~n`
      let st := st.countJump
      if st.gasExhaustedNow then st.outOfGasHalt else .halt (~~~ n) st
  | .excQuit =>
      let action : VM Int := do
        -- Match `pop_smallint_range(0xffff)` behavior closely enough for MVP.
        let v ← VM.popInt
        match v with
        | .nan => throw .rangeChk
        | .num n =>
            if n < 0 ∨ n > 0xffff then
              throw .rangeChk
            else
              return n
      let (res, st') := (action.run st)
      let n : Int :=
        match res with
        | .ok n => n
        | .error e => e.toInt
      let st' := st'.countJump
      if st'.gasExhaustedNow then st'.outOfGasHalt else .halt (~~~ n) st'
  | .whileCond cond body after =>
      -- C++ `WhileCont::jump[_w]` at the end of the condition: on true run `body`, installing the
      -- loop as `c0` unless `body` has `c0`; on false jump to `after`
      match VM.popBool.run st with
      | (.error e, st') => st'.raiseException e.toInt
      | (.ok true, st') =>
          if body.hasC0 then
            VmState.jumped { st' with cc := body }
          else
            VmState.jumped { st' with regs := { st'.regs with c0 := .whileBody cond body after }, cc := body }
      | (.ok false, st') => VmState.jumped { st' with cc := after }
  | .whileBody cond body after =>
      -- Match C++ `WhileCont::jump[_w]`: install while-cond continuation in c0 only if `cond` has no c0.
      if cond.hasC0 then
        VmState.jumped { st with cc := cond }
      else
        VmState.jumped { st with regs := { st.regs with c0 := .whileCond cond body after }, cc := cond }
  | .untilBody body after =>
      -- C++ `UntilCont::jump[_w]` at the end of the body: on true jump to `after`; on false run `body`
      -- again, installing the loop as `c0` unless `body` has `c0`
      match VM.popBool.run st with
      | (.error e, st') => st'.raiseException e.toInt
      | (.ok true, st') => VmState.jumped { st' with cc := after }
      | (.ok false, st') =>
          if body.hasC0 then
            VmState.jumped { st' with cc := body }
          else
            VmState.jumped { st' with regs := { st'.regs with c0 := .untilBody body after }, cc := body }
  | .repeatBody body after count =>
      -- C++ `RepeatCont::jump[_w]`
      if count = 0 then
        VmState.jumped { st with cc := after }
      else if body.hasC0 then
        VmState.jumped { st with cc := body }
      else
        VmState.jumped { st with regs := { st.regs with c0 := .repeatBody body after (count - 1) }, cc := body }
  | .againBody body =>
      -- C++ `AgainCont::jump[_w]`
      if body.hasC0 then
        VmState.jumped { st with cc := body }
      else
        VmState.jumped { st with regs := { st.regs with c0 := .againBody body }, cc := body }
  | .pushInt n next =>
      -- C++ `PushIntCont::jump` (continuation.cpp:321-330): push `n` and jump to `next`; no
      -- instruction runs
      VmState.jumped { st with stack := st.stack.push (.int (.num n)), cc := next }
  | .envelope ext cregs cdata =>
      let cdata := st.enteredCdata cdata
      if cdata.needsMoreArgs st.stack.size then st.raiseException Excno.stkUnd.toInt else
      -- Mirrors C++ `ArgContExt::jump`: apply saved control regs, closure stack and nargs, then jump to `ext`.
      let st' := st.applyCregsCdata cregs cdata
      -- the stack gas of that jump is `consume_stack_gas` (adjust_jump_cont)
      if VmState.ranOutEntering st st' then
        st'.outOfGasHalt
      else
        VmState.jumped { st' with cc := ext }
  | .ordinary code saved cregs cdata =>
      let cdata := st.enteredCdata cdata
      if cdata.needsMoreArgs st.stack.size then st.raiseException Excno.stkUnd.toInt else
      -- Apply pending continuation control regs (MVP: c0,c1,c2,c3,c4,c5,c7), once.
      let st2 := st.applyCregsCdata cregs cdata
      -- the stack gas of applying a closure (the jump to this continuation) is `consume_stack_gas`
      -- (adjust_jump_cont), before the next instruction is charged
      if VmState.ranOutEntering st st2 then
        st2.outOfGasHalt
      else
        -- entering an ordinary continuation is the last jump of its chain (C++ `OrdCont::jump`)
        let st2 := st2.countJump
        if st2.gasExhaustedNow then st2.outOfGasHalt else
        -- Closure stack / nargs are applied once on entry.
        let cdata' : OrdCdata := { cdata with stack := #[], nargs := -1 }
        -- a step of C++ `VmState::step`: the next instruction, the implicit `RET` or `JMPREF`
        let st : VmState := { st2 with cc := .ordinary code saved OrdCregs.empty cdata', chainJumps := 0,
                                       steps := st2.steps + 1 }
        if code.bitsRemaining == 0 then
          if code.refsRemaining == 0 then
            -- Implicit RET.
            let st0 := st.consumeGas implicitRetGasPrice
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else
              let (res, st1) := (VM.ret).run st0
              match res with
              | .ok _ =>
                  -- `gas.check()` ends the step (the stack gas of the jump to `c0`)
                  if decide (st1.gas.gasRemaining < 0) then st1.outOfGasHalt else .continue st1
              | .error e =>
                  st1.raiseException e.toInt
          else
            -- Implicit JMPREF to the first reference.
            let st0 := st.consumeGas implicitJmpRefGasPrice
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else
              if code.refPos < code.cell.refs.size then
                let refCell := code.cell.refs[code.refPos]!
                let (st1, exhausted) := st0.registerCellLoads (.cell refCell :: (st0.libraryLoads refCell).toList)
                if exhausted then
                  st1.outOfGasHalt
                else
                  -- C++ `load_cell_slice_ref`: a library cell runs its library's root; exotic cells are cell_und
                  match (libraryResolveLoads st1.libraries st1.globalVersion refCell st1.librariesRefused).2 with
                  | .ok root =>
                      -- `gas.check()` ends the step (the load, before version 4)
                      if decide (st1.gas.gasRemaining < 0) then st1.outOfGasHalt else
                      .continue { st1 with cc := .ordinary (Slice.ofCell root) (.quit 0) OrdCregs.empty OrdCdata.empty }
                  | .error e => st1.raiseException e.toInt
              else
                st0.raiseException Excno.cellUnd.toInt
        else
          -- C++ `OpcodeTable::lookup_instr`: the first 24 bits of the code, zero-padded
          let head : BitString := code.readBits (Nat.min 24 code.bitsRemaining)
          let opcode24 : Nat := bitsToNat (head ++ Array.replicate (24 - head.size) false)
          if st.cp = 0 ∧ st.globalVersion < cp0RequiredVersion opcode24 then
            -- C++ `OpcodeInstrWithVersion::dispatch` (opctable.cpp:457-461): an opcode of a later
            -- global version charges `gas_per_instr`, then inv_opcode
            let st0 := st.consumeGas gasPerInstr
            if st0.gasExhaustedNow then st0.outOfGasHalt else st0.raiseException Excno.invOpcode.toInt
          else
          let decoded : Except Excno (Instr × Nat × Slice) :=
            if st.cp = 0 then
              decodeCp0WithBits code
            else
              .error .invOpcode
          match decoded with
          | .error e =>
              -- Align with C++ opcode-table behavior: some invalid/too-short opcode paths
              -- charge one instruction slot before raising `inv_opcode`.
              let st0 :=
                if e = .invOpcode ∧ code.bitsRemaining > 0 then
                  let invalBits : Nat := cp0InvOpcodeGasBits code
                  st.consumeGas (gasPerInstr + Int.ofNat invalBits)
                else
                  st
              -- that charge is `consume_gas` (opctable.cpp): from version 4 out of gas there, no
              -- inv_opcode; before, the exception is raised, and its gas runs out
              if st0.gasExhaustedNow then
                st0.outOfGasHalt
              else
                st0.raiseException e.toInt
          | .ok (instr, totBits, rest) =>
              let st0 := { st with cc := .ordinary rest (.quit 0) OrdCregs.empty OrdCdata.empty }
              let stGas := st0.consumeGas (instrGas instr totBits)
              -- `consume_gas` (opctable.cpp): from version 4 out of gas at once; before, the
              -- instruction runs and the `gas.check()` after it finds it
              if stGas.gasExhaustedNow then
                stGas.outOfGasHalt
              else
                let (res, st1) := (exec instr).run stGas
                match res with
                | .ok _ =>
                    if decide (st1.gas.gasRemaining < 0) then
                      -- C++ gas.check() after step → VmNoGas → propagates to run(),
                      -- bypassing throw_exception.  No exception_gas charged.
                      st1.outOfGasHalt
                    else
                      .continue st1
                | .error e =>
                    if e = .outOfGas then
                      -- VmNoGas thrown mid-instruction (e.g. from consume_gas during
                      -- cell load).  Propagates to run(), no exception_gas charged.
                      st1.outOfGasHalt
                    else
                      -- TVM behavior: convert VM errors into an exception jump to c2.
                      st1.raiseException e.toInt

/-- The state a step ends in. -/
def StepResult.state : StepResult → VmState
  | .continue st => st
  | .halt _ st => st

def StepResult.mapState (f : VmState → VmState) : StepResult → StepResult
  | .continue st => .continue (f st)
  | .halt exitCode st => .halt exitCode (f st)

/-- The most times `VmState.stepWith` runs a step again. A run again refuses the libraries the run
before found C++ refuses; C++ ends an instruction at the first library it refuses (cell_und from
`load_cell_slice_impl`, CellSlice.cpp:1113-1122, which the dictionary loading the cell passes on), so
the first run again finds no other: the bound only keeps the definition total. -/
def libraryStepReruns : Nat := 8

/-- Runs the step from `st` with the libraries `refused` refused, and again with those it finds C++
refuses as well (`librariesMissed`) until it finds none, at most `reruns` times again. -/
def VmState.stepRefusingWith (exec : Instr → VM Unit) (st : VmState) (refused : Array BitString) :
    Nat → StepResult
  | 0 => (VmState.stepOnceWith exec { st with librariesRefused := refused, librariesMissed := #[] }).mapState
      fun st => { st with librariesRefused := #[], librariesMissed := #[] }
  | reruns + 1 =>
      let r := VmState.stepOnceWith exec { st with librariesRefused := refused, librariesMissed := #[] }
      let missed := r.state.librariesMissed
      if missed.isEmpty then
        r.mapState fun st => { st with librariesRefused := #[], librariesMissed := #[] }
      else
        st.stepRefusingWith exec (refused ++ missed) reruns

/-- One step of C++ `VmState::run` (`VmState.stepOnceWith`). The VM and the child VMs of `RUNVM`
step with this function; they differ only in `exec`.

With `max_library_loads` set (`VmState.maxLibraryLoads`), C++ `load_library` refuses a library not
yet loaded once that many are (vm.cpp:646-656): the set of loaded libraries grows during the step,
while the step resolves library cells with a resolver fixed for the step (`VM.cellResolver`, which
the dictionary functions take, and `VM.loadCellSlice`). The step is therefore run with no library
refused, its loads registered in C++ order (`VmState.registerCellLoads`, which admits each library as
C++ does and notes the refusals the step did not make), and run again with those libraries refused
too, until a run notes none; that run is the step of C++. A library C++ refuses was not loaded before
in the step (it would have been admitted), so a run that refuses it is the same up to its load and
refuses it there; from then on the set of loaded libraries is full and no longer changes, so a
library refused once is refused at every load. Without the limit the step runs once. -/
def VmState.stepWith (exec : Instr → VM Unit) (st : VmState) : StepResult :=
  if st.maxLibraryLoads.isNone then
    st.stepOnceWith exec
  else
    st.stepRefusingWith exec #[] libraryStepReruns

/-- Steps within which a VM with gas `g` halts, the fuel for a VM that only gas bounds (the child
of `RUNVM`): every step charges gas (an instruction, an implicit `RET` or `JMPREF`, an exception)
except the free jumps of a chain, at most `freeNestedContJump` in a row, and at most
`max (gasLimit + gasCredit) gasMax` gas is charged before the VM runs out of gas. -/
def GasLimits.stepBound (g : GasLimits) : Nat :=
  (freeNestedContJump + 1) * ((max (g.gasLimit + g.gasCredit) g.gasMax).toNat + 2)

/-- C++ `VmState::run` with `run_inner`: step until the VM halts, then `try_commit` after exit code 0
or 1 (`(res | 1) == -1`); `fuel` bounds the number of steps. -/
def VmState.runWith (exec : Instr → VM Unit) (fuel : Nat) (st : VmState) : StepResult :=
  match fuel with
  | 0 => .halt (Excno.fatal.toInt) st
  | fuel + 1 =>
      match st.stepWith exec with
      | .continue st' => VmState.runWith exec fuel st'
      | .halt exitCode st' =>
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              -- C++: clear stack, push 0, return ~cell_ov on commit failure.
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

end TvmLean

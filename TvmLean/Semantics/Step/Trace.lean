import TvmLean.Semantics.Step.Run

namespace TvmLean

structure TraceEntry where
  step : Nat
  event : String
  cp : Int
  cc_before : String
  cc_after : String
  gas_before : Int
  gas_after : Int
  stack_before : String
  stack_after : String
  deriving Repr

instance : Inhabited TraceEntry where
  default :=
    { step := 0
      event := ""
      cp := 0
      cc_before := ""
      cc_after := ""
      gas_before := 0
      gas_after := 0
      stack_before := ""
      stack_after := "" }

def stackStr (s : Stack) : String :=
  let elems := s.toList.map (fun v => v.pretty)
  "[" ++ String.intercalate ", " elems ++ "]"

def Stack.pretty (s : Stack) : String :=
  stackStr s

def Slice.peekByteHex (s : Slice) : String :=
  if s.haveBits 8 then
    let b := bitsToNat (s.readBits 8)
    let hex := String.mk (Nat.toDigits 16 b)
    let hex := if b < 16 then "0" ++ hex else hex
    s!"0x{hex}"
  else
    "<eof>"

def natToHexPad (n : Nat) (digits : Nat) : String :=
  let hex := String.mk (Nat.toDigits 16 n)
  if hex.length ≥ digits then
    hex
  else
    String.mk (List.replicate (digits - hex.length) '0') ++ hex

def Slice.peekWord16Hex (s : Slice) : String :=
  if s.haveBits 16 then
    s!"0x{natToHexPad (bitsToNat (s.readBits 16)) 4}"
  else
    "<eof>"

def VmState.ccSummary (cc : Continuation) : String :=
  match cc with
  | .quit n => s!"quit {n}"
  | .excQuit => "excquit"
  | .whileCond _ _ _ => "whileCond"
  | .whileBody _ _ _ => "whileBody"
  | .untilBody _ _ => "untilBody"
  | .repeatBody _ _ _ => "repeatBody"
  | .againBody _ => "againBody"
  | .pushInt n _ => s!"pushInt {n}"
  | .envelope _ _ _ => "envelope"
  | .ordinary code _ _ _ =>
      s!"ord(bitPos={code.bitPos},refPos={code.refPos},bitsRem={code.bitsRemaining},refsRem={code.refsRemaining},next8={code.peekByteHex},next16={code.peekWord16Hex})"

/-- The trace event of the step from `st`: what the step does, by the continuation in `cc`. -/
private def stepEvent (st : VmState) : String :=
  match st.cc with
  | .quit n => s!"quit({n})"
  | .excQuit => "excquit"
  | .whileCond .. => "while_cond"
  | .whileBody .. => "while_body"
  | .untilBody .. => "until_body"
  | .repeatBody _ _ count => s!"repeat_body({count})"
  | .againBody .. => "again_body"
  | .pushInt n _ => s!"push_int({n})"
  | .envelope .. => "envelope"
  | .ordinary code .. =>
      if code.bitsRemaining == 0 then
        if code.refsRemaining == 0 then "implicit_ret" else "implicit_jmpref"
      else
        match (if st.cp = 0 then decodeCp0WithBits code else .error .invOpcode) with
        | .ok (instr, _, _) => s!"exec({instr.pretty})"
        | .error e => s!"decode_error({reprStr e})"

/-- `VmState.step` with a trace entry; a step that halts the VM is marked with its exit code. -/
def VmState.stepTrace (st : VmState) (step : Nat) : TraceEntry × StepResult :=
  let res := st.step
  let (event, stAfter) :=
    match res with
    | .continue st' => (stepEvent st, st')
    | .halt code st' => (s!"{stepEvent st} halt({code})", st')
  ({ step
     event
     cp := st.cp
     cc_before := VmState.ccSummary st.cc
     cc_after := VmState.ccSummary stAfter.cc
     gas_before := st.gas.remaining
     gas_after := stAfter.gas.remaining
     stack_before := stackStr st.stack
     stack_after := stackStr stAfter.stack },
   res)

def VmState.runTrace (fuel : Nat) (st : VmState) (maxTrace : Nat := 200) :
    StepResult × Array TraceEntry × Bool :=
  Id.run do
    let mut stCur := st
    let mut fuelCur := fuel
    let mut step : Nat := 0
    let mut trace : Array TraceEntry := #[]
    let mut pos : Nat := 0
    let mut wrapped : Bool := false
    let mut res : StepResult := .continue stCur

    while fuelCur > 0 do
      let (entry, stepRes) := stCur.stepTrace step
      if maxTrace > 0 then
        if trace.size < maxTrace then
          trace := trace.push entry
        else
          trace := trace.set! pos entry
          pos := (pos + 1) % maxTrace
          wrapped := true

      match stepRes with
      | .continue st' =>
          stCur := st'
          res := .continue st'
          fuelCur := fuelCur - 1
          step := step + 1
      | .halt exitCode st' =>
          res := .halt exitCode st'
          stCur := st'
          fuelCur := 0

    match res with
    | .continue st' =>
        res := .halt (Excno.fatal.toInt) st'
    | .halt _ _ => pure ()

    -- Mirror the C++ commit wrapper shape; precise commit checks come later.
    let res' :=
      match res with
      | .continue st' => .halt (Excno.fatal.toInt) st'
      | .halt exitCode st' =>
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

    let traceOut :=
      if wrapped && trace.size > 0 then
        let n := trace.size
        Array.ofFn (n := n) fun i =>
          let idx := (pos + i.1) % n
          trace[idx]!
      else
        trace

    return (res', traceOut, wrapped)

end TvmLean

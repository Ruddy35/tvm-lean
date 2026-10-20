import Tests.Harness.Registry

/-!
Oracle cases for exceptions (`THROW*`, `TRY`, `TRYARGS`; C++ `contops.cpp`), `CDATASIZE`/`SDATASIZE`
(`cellops.cpp`), `SETCP*` and the debug instructions (`debugops.cpp`). Programs that need
continuations build them with `PUSHCONT` inline; the code cell is assembled with `encodeCp0Code`,
which also encodes inline data and references. The model is compared with C++: exit code, gas, stack.
-/

namespace Tests.Gen.Control

open TvmLean

private def iv (n : Int) : Value := .int (.num n)

/-- Code cell of a program (bits, inline data and references of every instruction). -/
def codeOf (prog : Array Instr) : Cell :=
  let r : Except Excno (BitString × Array Cell) :=
    prog.foldlM (fun acc i => do
      let (b, refs) ← encodeCp0Code i
      pure (acc.1 ++ b, acc.2 ++ refs)) (#[], #[])
  match r with
  | .ok (b, refs) => Cell.mkOrdinary b refs
  | .error e => panic! s!"Tests.Gen.Control.codeOf: cannot encode {reprStr prog}: {reprStr e}"

private def cont (body : Array Instr) : Instr := .pushCont (Slice.ofCell (codeOf body))

private def cross (suite : String) (variants : Array (String × Instr)) (stacks : Array (Array Value)) :
    Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for (vl, i) in variants do
    for k in [0:stacks.size] do
      out := out.push
        { name := s!"oracle/{vl}/stack{k}", instr := { name := suite }, program := #[i],
          initStack := stacks[k]! }
  return out

/-- Cases whose code is given as a cell (programs with inline continuations). -/
private def crossProg (suite : String) (progs : Array (String × Array Instr)) (stacks : Array (Array Value)) :
    Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for (pl, p) in progs do
    for k in [0:stacks.size] do
      out := out.push
        { name := s!"oracle/{pl}/stack{k}", instr := { name := suite }, codeCell? := some (codeOf p),
          initStack := stacks[k]! }
  return out

private def plain : Array (Array Value) := #[#[], #[iv 5], #[iv 5, .null]]
private def conds : Array (Array Value) :=
  #[#[iv 0], #[iv 1], #[iv (-1)], #[.null], #[], #[iv 9, iv 0], #[iv 9, iv 5]]
private def argStacks : Array (Array Value) := #[#[iv 42], #[.null], #[], #[iv 1, iv 2]]
private def argConds : Array (Array Value) :=
  #[#[iv 42, iv 0], #[iv 42, iv 1], #[iv 42, .null], #[iv 42], #[]]
private def anyCodes : Array (Array Value) :=
  ((#[0, 1, 5, 2047, 65535, 65536, -1] : Array Int).map (fun n => #[iv n])) ++ #[#[.null], #[]]
private def argAny : Array (Array Value) :=
  #[#[iv 42, iv 5], #[iv 42, iv 65535], #[iv 42, iv 65536], #[iv 42, iv (-1)], #[iv 42], #[]]
private def anyIf : Array (Array Value) :=
  #[#[iv 5, iv 0], #[iv 5, iv 1], #[iv 70000, iv 1], #[iv 5, .null], #[iv 5], #[]]
private def argAnyIf : Array (Array Value) :=
  #[#[iv 42, iv 5, iv 0], #[iv 42, iv 5, iv (-1)], #[iv 42, iv 65536, iv 1], #[iv 42, iv 5], #[]]

private def labelled (f : Int → Instr) (ns : Array Int) : Array (String × Instr) :=
  ns.map (fun n => (s!"n{n}", f n))

/-- TRY bodies and handlers: normal return, THROW, THROWARG, values left on the stack, rethrow. -/
private def bodies : Array (String × Array Instr) :=
  #[ ("empty", #[]), ("push7", #[.pushInt (.num 7)]), ("throw9", #[.throw 9]),
     ("throwarg11", #[.pushInt (.num 3), .throwArg 11]),
     ("push-push-throw5", #[.pushInt (.num 1), .pushInt (.num 2), .throw 5]) ]
private def handlers : Array (String × Array Instr) :=
  #[ ("h-empty", #[]), ("h-push100", #[.pushInt (.num 100)]), ("h-rethrow13", #[.throw 13]) ]

private def tryProgs (t : Instr) : Array (String × Array Instr) :=
  bodies.flatMap (fun (bl, b) => handlers.map (fun (hl, h) => (s!"{bl}/{hl}", #[cont b, cont h, t])))

/-- Cells with shared children (deduplicated counting) and a deep chain. -/
private def cellPool : Array Cell :=
  let c1 := Cell.mkOrdinary (natToBits 0xabc 12) #[]
  let c2 := Cell.mkOrdinary (natToBits 5 3) #[c1, c1]
  let c3 := Cell.mkOrdinary #[] #[c2, Cell.mkOrdinary (natToBits 1 1) #[c2]]
  let chain := (List.range 10).foldl (fun c k => Cell.mkOrdinary (natToBits k 8) #[c]) Cell.empty
  #[Cell.empty, c1, c2, c3, chain]

private def bounds : Array Int := #[0, 1, 2, 3, 10, 1000, -1, 2 ^ 63]

private def dataSizeStacks (asSlice : Bool) : Array (Array Value) :=
  let v (c : Cell) : Value := if asSlice then .slice (Slice.ofCell c) else .cell c
  (cellPool.flatMap (fun c => bounds.map (fun n => #[v c, iv n]))) ++
    -- a NaN bound (`!bound->is_valid()`: range_chk, `exec_compute_data_size`), checked after the
    -- cell or slice is popped (type_chk first)
    #[#[.null, iv 5], #[v Cell.empty], #[], #[v Cell.empty, .int .nan], #[iv 3, .int .nan]]

private def dbg (o : DebugInstr) : Instr := .debugOp o
private def two : Array (Array Value) := #[#[], #[iv 1, iv 2]]


/-- The exception handler `c2` is a closure holding 45 stack values (three SETCONTARGS 15).
C++ `throw_exception` charges exception_gas_price and jumps to `c2` at once; the jump merges the
closure stack with the two exception values and charges stack gas (adjust_jump_cont ->
consume_stack_gas, 47 - 32 = 15) in the same step. Limits around those charges
(`PUSHINT lim; SETGASLIMIT; THROW 5` after installing the handler). -/
private def closureHandlerCases (suite : String) : Array OracleCase :=
  -- `PUSHCONT { NOP }` (short form 9x, one byte of code), assembled by hand: assembleCp0 has no
  -- inline continuations
  let pushHandler : BitString := natToBits 0x9100 16
  let rest (lim : Nat) : BitString :=
    match assembleCp0 [.setContArgs 15 (-1), .setContArgs 15 (-1), .setContArgs 15 (-1), .popCtr 2,
        .pushInt (.num (Int.ofNat lim)), .tonEnvOp .setGasLimit, .throw 5] with
    | .ok c => c.bits
    | .error _ => #[]
  (Array.range 91).map fun k =>
    let lim := 220 + k
    { name := s!"oracle/closure-handler/limit{lim}", instr := { name := suite },
      codeCell? := some (Cell.mkOrdinary (pushHandler ++ rest lim) #[]),
      initStack := (Array.range 45).map (fun j => iv (Int.ofNat j)) }

/-- The handler `c2` is a closure expecting `nargs` arguments (SETCONTARGS 0,nargs) while an
exception passes two (value, number): C++ `adjust_jump_cont` raises stk_und inside
`throw_exception`, `run_inner` handles it by `throw_exception(stk_und)`, whose jump fails again,
and the VM ends with the second exception's number (vm.cpp, run_inner: "exception while handling
exception"). -/
private def closureArgsHandlerCases (suite : String) : Array OracleCase :=
  let pushHandler : BitString := natToBits 0x9100 16
  (#[0, 1, 2, 3, 4] : Array Nat).flatMap fun nargs =>
    #[(s!"throw/nargs{nargs}", #[Instr.setContArgs 0 (Int.ofNat nargs), .popCtr 2, .throw 5]),
      (s!"throwarg/nargs{nargs}", #[Instr.setContArgs 0 (Int.ofNat nargs), .popCtr 2, .pushInt (.num 7), .throwArg 5]),
      (s!"stk-und/nargs{nargs}", #[Instr.setContArgs 0 (Int.ofNat nargs), .popCtr 2, .pop 5])].map fun (name, prog) =>
      let code : Cell :=
        match assembleCp0 prog.toList with
        | .ok c => Cell.mkOrdinary (pushHandler ++ c.bits) #[]
        | .error _ => Cell.empty
      { name := s!"oracle/closure-args-handler/{name}", instr := { name := suite }, codeCell? := some code,
        initStack := #[iv 1, iv 2] }

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "THROW" => cross suite (labelled .throw #[0, 63, 64, 1000, 2047]) plain ++ closureHandlerCases suite ++
      closureArgsHandlerCases suite
  | "THROW_SHORT" => cross suite (labelled .throw #[0, 1, 11, 63]) plain
  | "THROWIF" => cross suite (labelled .throwIf #[0, 64, 2047]) conds
  | "THROWIFNOT" => cross suite (labelled .throwIfNot #[0, 64, 2047]) conds
  | "THROWIF_SHORT" => cross suite (labelled .throwIf #[1, 63]) conds
  | "THROWIFNOT_SHORT" => cross suite (labelled .throwIfNot #[1, 63]) conds
  | "THROWARG" => cross suite (labelled .throwArg #[0, 63, 2047]) argStacks
  | "THROWARGIF" => cross suite (labelled .throwArgIf #[0, 63, 2047]) argConds
  | "THROWARGIFNOT" => cross suite (labelled .throwArgIfNot #[0, 63, 2047]) argConds
  | "THROWANY" => cross suite #[("any", .throwAny false false false)] anyCodes
  | "THROWARGANY" => cross suite #[("any", .throwAny true false false)] argAny
  | "THROWANYIF" => cross suite #[("any", .throwAny false true true)] anyIf
  | "THROWANYIFNOT" => cross suite #[("any", .throwAny false true false)] anyIf
  | "THROWARGANYIF" => cross suite #[("any", .throwAny true true true)] argAnyIf
  | "THROWARGANYIFNOT" => cross suite #[("any", .throwAny true true false)] argAnyIf
  | "TRY" => crossProg suite (tryProgs .try_) #[#[], #[iv 1, iv 2]]
  | "TRYARGS" =>
      crossProg suite
        (#[(0, 0), (1, 1), (2, 1), (0, 2), (15, 15)].flatMap
          (fun (p, r) => (tryProgs (.tryArgs p r)).map (fun (l, prog) => (s!"p{p}r{r}/{l}", prog))))
        #[#[], #[iv 1, iv 2, iv 3]]
  | "CDATASIZE" => cross suite #[("c", .cellExt (.cdataSize false))] (dataSizeStacks false)
  | "CDATASIZEQ" => cross suite #[("cq", .cellExt (.cdataSize true))] (dataSizeStacks false)
  | "SDATASIZE" => cross suite #[("s", .cellExt (.sdataSize false))] (dataSizeStacks true)
  | "SDATASIZEQ" => cross suite #[("sq", .cellExt (.sdataSize true))] (dataSizeStacks true)
  | "SETCP" =>
      crossProg suite
        ((#[0, 1, 100, 239] : Array Int).flatMap
          (fun x => #[(s!"x{x}", #[.setcp x]), (s!"x{x}-then-push", #[.setcp x, .pushInt (.num 1)])]))
        #[#[], #[iv 1]]
  | "SETCP_SHORT" =>
      crossProg suite
        ((#[-1, -15] : Array Int).flatMap
          (fun x => #[(s!"x{x}", #[.setcp x]), (s!"x{x}-then-push", #[.setcp x, .pushInt (.num 1)])]))
        #[#[], #[iv 1]]
  | "SETCPX" => cross suite #[("setcpx", .setcpX)]
      (((#[0, 1, -1, -15, -16, 255, 256, 2 ^ 63] : Array Int).map (fun x => #[iv x])) ++ #[#[.null], #[]])
  | "DEBUG" => cross suite #[("d1", dbg (.debug 1)), ("d13", dbg (.debug 0x13))] two
  | "DEBUG_1" => cross suite #[("t15", dbg (.debug1 0x15)), ("t1f", dbg (.debug1 0x1f))] two
  | "DEBUG_2" => cross suite #[("t30", dbg (.debug2 0x30)), ("tef", dbg (.debug2 0xef))] two
  | "DUMP" => cross suite #[("i0", dbg (.dump 0)), ("i5", dbg (.dump 5)), ("i14", dbg (.dump 14))] two
  | "DUMPSTK" => cross suite #[("dumpstk", dbg .dumpStk)] two
  | "STRDUMP" => cross suite #[("strdump", dbg .strDump)]
      #[#[.slice (Slice.ofCell (Cell.mkOrdinary (natToBits 0x41424344 32) #[]))], #[iv 1], #[]]
  | "DEBUGSTR" => cross suite
      #[("1byte", dbg (.debugStr (Slice.ofCell (Cell.mkOrdinary (natToBits 0x41 8) #[])))),
        ("16bytes", dbg (.debugStr (Slice.ofCell (Cell.mkOrdinary (natToBits 0x4142434445464748494a4b4c4d4e4f50 128) #[]))))]
      two ++
      -- data shorter than the length in the opcode: OpcodeInstrExt::dispatch charges 10 + 16, then
      -- exec_dummy_debug_str throws inv_opcode (debugops.cpp)
      ((#[("len4-8bits", natToBits 0xfef3 16 ++ natToBits 0x41 8), ("len1-none", natToBits 0xfef0 16),
          ("len16-100bits", natToBits 0xfeff 16 ++ natToBits 5 100)] : Array (String × BitString)).map fun (n, b) =>
        { name := s!"oracle/raw/truncated/{n}", instr := { name := suite }, codeCell? := some (Cell.mkOrdinary b #[]),
          initStack := #[iv 1] })
  | _ => #[]

end Tests.Gen.Control

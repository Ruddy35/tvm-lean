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

/-! ### Loading exotic cells (`load_cell_slice_impl`, `cells/CellSlice.cpp`)

An instruction loading a library cell goes on to the library's root when the collection has it
(the coverage run never did); a library whose root is a library cell again is cell_und
("recursive library cells are not allowed"); pruned branches and Merkle proofs and updates are
cell_und. Library collections are dictionaries of 256-bit hashes to a reference to the root. -/

private def bytesBits (bs : Array UInt8) : BitString := bs.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

private def reprHash (c : Cell) : Array UInt8 := Cell.hashBytes c

/-- Library cell (exotic type 2) referring to `target`. -/
private def libCell (target : Cell) : Cell :=
  { bits := natToBits 2 8 ++ bytesBits (reprHash target), refs := #[], special := true, levelMask := 0 }

private def libCollection (targets : Array Cell) : Cell :=
  let root := targets.foldl (fun root t =>
    match dictSetRefWithCells root (bytesBits (reprHash t)) t .set with
    | .ok (some r, _, _, _) => some r
    | _ => root) none
  root.getD Cell.empty

private def depth2 (d : Nat) : BitString := natToBits d 16

/-- Merkle proof of an ordinary (level 0) cell: its hash and depth at level 0 are `hashBytes` and `depth`. -/
private def merkleProof (child : Cell) : Cell :=
  { bits := natToBits 3 8 ++ bytesBits (reprHash child) ++ depth2 child.depth,
    refs := #[child], special := true, levelMask := 0 }

private def merkleUpdate (a b : Cell) : Cell :=
  { bits := natToBits 4 8 ++ bytesBits (reprHash a) ++ bytesBits (reprHash b) ++ depth2 a.depth ++ depth2 b.depth,
    refs := #[a, b], special := true, levelMask := 0 }

private def loadTarget : Cell := Cell.mkOrdinary (natToBits 0xbeef 16) #[Cell.mkOrdinary (natToBits 5 3) #[]]
/-- A library cell whose library is another library cell (of `loadTarget`). -/
private def libOfLib : Cell := libCell (libCell loadTarget)

private def loadCases (suite : String) : Array OracleCase :=
  let mk (name : String) (stack : Array Value) (libs : Array Cell) (prog : Array Instr) : OracleCase :=
    { name := s!"oracle/load/{name}", instr := { name := suite }, program := prog, initStack := stack,
      initLibraries := if libs.isEmpty then #[] else #[libCollection libs] }
  let cells : Array (String × Cell × Array Cell) :=
    #[("lib-hit", libCell loadTarget, #[loadTarget]), ("lib-miss", libCell loadTarget, #[]),
      ("lib-recursive", libOfLib, #[libCell loadTarget, loadTarget]),
      ("pruned", pruned, #[]), ("merkle-proof", merkleProof loadTarget, #[]),
      ("merkle-update", merkleUpdate loadTarget (Cell.mkOrdinary (natToBits 1 1) #[]), #[])]
  match suite with
  | "CTOS" => cells.map fun (n, c, libs) => mk n #[.cell c] libs #[.ctos]
  | "LDREFRTOS" =>
      cells.map fun (n, c, libs) => mk n #[.slice (Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[c]))] libs #[.ldrefRtos]
  | "DICTUGET" =>
      -- the dictionary root itself is a library cell
      let dict : Cell :=
        match dictSetSliceWithCells none (natToBits 3 4) (Slice.ofCell (Cell.mkOrdinary (natToBits 9 8) #[])) .set with
        | .ok (some r, _, _, _) => r
        | _ => Cell.empty
      -- a two-entry dictionary: a fork node whose children are leaves; one child replaced by an
      -- exotic cell (the fork's own bits and the other child unchanged)
      let dict2 : Cell :=
        match dictSetSliceWithCells (some dict) (natToBits 12 4) (Slice.ofCell (Cell.mkOrdinary (natToBits 7 8) #[])) .set with
        | .ok (some r, _, _, _) => r
        | _ => Cell.empty
      let withChild (c : Cell) : Cell := Cell.mkOrdinary dict2.bits (dict2.refs.set! 0 c)
      let get : Array Instr := #[Instr.dictGet true true false]
      #[mk "dict-root-lib-hit" #[iv 3, .cell (libCell dict), iv 4] #[dict] get,
        mk "dict-root-lib-miss" #[iv 3, .cell (libCell dict), iv 4] #[] get,
        mk "dict-root-pruned" #[iv 3, .cell pruned, iv 4] #[] get,
        mk "dict-root-merkle" #[iv 3, .cell (merkleProof dict), iv 4] #[] get,
        mk "dict-child-lib-hit" #[iv 3, .cell (withChild (libCell (dict2.refs[0]!))), iv 4] #[dict2.refs[0]!] get,
        mk "dict-child-lib-hit-other-key" #[iv 12, .cell (withChild (libCell (dict2.refs[0]!))), iv 4] #[dict2.refs[0]!] get,
        mk "dict-child-pruned" #[iv 3, .cell (withChild pruned), iv 4] #[] get,
        mk "dict-child-pruned-other-key" #[iv 12, .cell (withChild pruned), iv 4] #[] get]
  | _ => #[]

/-- Instructions with a code or slice reference (`ref_to_cont` / `load_cell_slice_ref`): the reference
is a library cell whose library is present (its root, the code `PUSHINT 7`, runs), a library cell
without it, a pruned branch, a Merkle proof. `pre` are the opcode bits, `stack` the initial stack
under which the reference is taken; the implicit JMPREF of a code cell without bits is under
`JMPREF`. -/
private def codeRefCases (suite : String) : Array OracleCase :=
  let target : Cell := Cell.mkOrdinary (natToBits 0x77 8) #[]
  let refs : Array (String × Cell × Array Cell) :=
    #[("lib-hit", libCell target, #[target]), ("lib-miss", libCell target, #[]),
      ("pruned", pruned, #[]), ("merkle-proof", merkleProof target, #[])]
  let shape : Option (BitString × Array Value) :=
    match suite with
    | "CALLREF" => some (natToBits 0xdb3c 16, #[])
    | "JMPREF" => some (natToBits 0xdb3d 16, #[])
    | "JMPREFDATA" => some (natToBits 0xdb3e 16, #[])
    | "IFREF" => some (natToBits 0xe300 16, #[iv (-1)])
    | "IFNOTREF" => some (natToBits 0xe301 16, #[iv 0])
    | "IFJMPREF" => some (natToBits 0xe302 16, #[iv (-1)])
    | "IFNOTJMPREF" => some (natToBits 0xe303 16, #[iv 0])
    -- PUSHCONT {NOP} before: (f c -) with the reference taken when f is true / false
    | "IFREFELSE" => some (natToBits 0x9100 16 ++ natToBits 0xe30d 16, #[iv (-1)])
    | "IFELSEREF" => some (natToBits 0x9100 16 ++ natToBits 0xe30e 16, #[iv 0])
    | "IFBITJMPREF" => some (natToBits 0xe3c0 16, #[iv 1])
    | "IFNBITJMPREF" => some (natToBits 0xe3e0 16, #[iv 0])
    | "PUSHREFSLICE" => some (natToBits 0x89 8, #[])
    | "PUSHREFCONT" => some (natToBits 0x8a 8, #[])
    | _ => none
  let main : Array OracleCase :=
    match shape with
    | none => #[]
    | some (pre, stack) =>
        refs.map fun (n, r, libs) =>
          { name := s!"oracle/load/ref-{n}", instr := { name := suite }, codeCell? := some (Cell.mkOrdinary pre #[r]),
            initStack := stack, initLibraries := if libs.isEmpty then #[] else #[libCollection libs] }
  let both : Array OracleCase :=
    if suite == "IFREFELSEREF" then
      refs.flatMap fun (n, r, libs) =>
        #[(-1 : Int), 0].map fun f =>
          { name := s!"oracle/load/ref-{n}/f{f}", instr := { name := suite },
            codeCell? := some (Cell.mkOrdinary (natToBits 0xe30f 16) (if f == 0 then #[target, r] else #[r, target])),
            initStack := #[iv f], initLibraries := if libs.isEmpty then #[] else #[libCollection libs] }
    else #[]
  let implicit : Array OracleCase :=
    if suite == "JMPREF" then
      refs.map fun (n, r, libs) =>
        { name := s!"oracle/load/implicit-jmpref-{n}", instr := { name := suite }, codeCell? := some (Cell.mkOrdinary #[] #[r]),
          initLibraries := if libs.isEmpty then #[] else #[libCollection libs] }
    else #[]
  main ++ both ++ implicit

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "CTOS" | "LDREFRTOS" | "DICTUGET" => loadCases suite
  | "CALLREF" | "JMPREFDATA" | "IFREF" | "IFNOTREF" | "IFJMPREF" | "IFNOTJMPREF" | "IFREFELSE"
  | "IFELSEREF" | "IFREFELSEREF" | "IFBITJMPREF" | "IFNBITJMPREF" | "PUSHREFSLICE" | "PUSHREFCONT" => codeRefCases suite
  | "JMPREF" => codeRefCases suite
  | "COMMIT" => commitCases suite
  | "REPEAT" | "AGAIN" | "UNTIL" => loopCases suite
  | _ => callCases suite

end Tests.Gen.VmCore

import Tests.Harness.Registry
import Tests.Harness.Gen.VmCore

/-!
Oracle cases for the action instructions (C++ `tonops.cpp`: SENDRAWMSG, SENDMSG, RAWRESERVE{X},
SETCODE, SETLIBCODE, CHANGELIB). They append output actions to `c5`; the oracle compares the `c5`
hash with C++, so the exact serialization of every action is checked, together with exit code,
gas and stack. Messages are serialized by hand per `block.tlb` (internal to basechain and
masterchain, body inline or in a reference, large value; external outbound; malformed cells).
-/

namespace Tests.Gen.Msg

open TvmLean

private def iv (n : Int) : Value := .int (.num n)

/-- Grams (VarUInteger 16): 4-bit byte length, then the value. -/
private def grams (g : Nat) : BitString :=
  let len := (Nat.log2 g + 8) / 8
  let len := if g = 0 then 0 else len
  natToBits len 4 ++ natToBits g (8 * len)

private def addrStd (wc : Nat) (h : Nat) : BitString :=
  natToBits 0b10 2 ++ #[false] ++ natToBits wc 8 ++ natToBits h 256

/-- int_msg_info$0 ihr_disabled bounce bounced src dest value ihr_fee fwd_fee created_lt created_at,
then no init and the body (inline empty, or in a reference). -/
private def intMsg (wc : Nat) (value : Nat) (bodyRef : Option Cell) : Cell :=
  let hdr := #[false, true, true, false] ++ natToBits 0 2 ++ addrStd wc 0x1234 ++ grams value ++ #[false] ++
    grams 0 ++ grams 0 ++ natToBits 0 64 ++ natToBits 0 32 ++ #[false]
  match bodyRef with
  | none => Cell.mkOrdinary (hdr ++ #[false]) #[]
  | some b => Cell.mkOrdinary (hdr ++ #[true]) #[b]

/-- ext_out_msg_info$11 src:addr_none dest:addr_none created_lt created_at, no init, empty body. -/
private def extOutMsg : Cell :=
  Cell.mkOrdinary (natToBits 0b11 2 ++ natToBits 0 2 ++ natToBits 0 2 ++ natToBits 0 64 ++ natToBits 0 32 ++
    #[false, false]) #[]

private def body : Cell := Cell.mkOrdinary (natToBits 0xdeadbeef 32) #[]

/-- Message cells. -/
def msgPool : Array Cell :=
  #[ intMsg 0 100 none, intMsg 255 1000000000 none, intMsg 0 (2 ^ 100) (some body), extOutMsg,
     Cell.empty, Cell.mkOrdinary (natToBits 0x5a 8) #[] ]

private def cross (suite : String) (i : Instr) (stacks : Array (Array Value)) : Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for k in [0:stacks.size] do
    out := out.push
      { name := s!"oracle/stack{k}", instr := { name := suite }, program := #[i], initStack := stacks[k]! }
  return out

private def env (o : TonEnvInstr) : Instr := .tonEnvOp o

private def msgModeStacks (modes : Array Int) : Array (Array Value) :=
  (msgPool.flatMap (fun c => modes.map (fun m => #[.cell c, iv m]))) ++
    #[#[.null, iv 0], #[.cell (msgPool[0]!)], #[]]

/-! ### SENDMSG: messages and parameters the coverage run did not reach (`exec_send_message`)

Messages with a StateInit (inline, or moved into a reference when the root would overflow, or a
reference already), bodies inline, in a reference or moved into one (more than 1023 bits or 4
references in the root), extra currencies (their dictionary is not counted, global version >= 10),
a masterchain destination, a user `fwd_fee` (taken as a minimum below version 14), repeated
subtrees (counted once) and an external message. Parameters: `MYADDR` in the masterchain or not a
slice, `BALANCE` and `INCOMINGVALUE` not tuples or without an integer, the forwarding prices
(unpacked config 4 and 5) missing or malformed, the size limits (unpacked config 6) malformed or
limiting the counted cells to 2. -/

private def tup (xs : Array Value) : Value := .tuple xs
private def sl (bits : BitString) : Value := .slice (Slice.ofCell (Cell.mkOrdinary bits #[]))

/-- msg_forward_prices#ea lump_price bit_price cell_price ihr_price_factor first_frac next_frac -/
private def fwdPrices (lump bit cell : Nat) : Value :=
  sl (natToBits 0xea 8 ++ natToBits lump 64 ++ natToBits bit 64 ++ natToBits cell 64 ++ natToBits 98304 32 ++
    natToBits 21845 16 ++ natToBits 21845 16)

/-- size_limits_config#01 with `max_msg_cells` cells. -/
private def sizeLimitsBits (maxCells : Nat) : BitString :=
  natToBits 1 8 ++ natToBits 65535 32 ++ natToBits maxCells 32 ++ natToBits 1000 32 ++ natToBits 512 16 ++
    natToBits 65535 32 ++ natToBits 512 16

private def sizeLimits (maxCells : Nat) : Value := sl (sizeLimitsBits maxCells)

private def unpackedConfig (mcPrices prices limits : Value) : Value :=
  tup #[.null, .null, .null, .null, mcPrices, prices, limits]

private def goodConfig : Value :=
  unpackedConfig (fwdPrices 10000000 655360000 65536000000) (fwdPrices 400000 26214400 2621440000) .null

/-- The parameter tuple: `Tests.Gen.TonEnv.params`-like, with what SENDMSG reads. -/
private def sendParams (myAddr balance incoming config : Value) : Array Value :=
  (Array.range 18).map fun i =>
    match i with
    | 0 => iv 0x076ef1ea
    | 7 => balance
    | 8 => myAddr
    | 11 => incoming
    | 14 => config
    | _ => .null

private def myAddrBase : Value := .slice (Slice.ofCell (Cell.mkOrdinary (addrStd 0 0x99) #[]))
private def myAddrMc : Value := .slice (Slice.ofCell (Cell.mkOrdinary (addrStd 255 0x99) #[]))
private def bal : Value := tup #[iv 5000000000, .null]

private def sendC7 (myAddr : Value := myAddrBase) (balance : Value := bal) (incoming : Value := bal)
    (config : Value := goodConfig) : Array Value :=
  #[tup (sendParams myAddr balance incoming config)]

private def sendC7Pool : Array (String × Array Value) :=
  #[ ("base", sendC7),
     ("mc-myaddr", sendC7 (myAddr := myAddrMc)),
     ("limits-2-cells", sendC7 (config := unpackedConfig (fwdPrices 1 2 3) (fwdPrices 400000 26214400 2621440000)
        (sizeLimits 2))) ]

private def sendC7Errors : Array (String × Array Value) :=
  #[ ("myaddr-null", sendC7 (myAddr := .null)),
     ("balance-null", sendC7 (balance := .null)),
     ("balance-no-int", sendC7 (balance := tup #[.null, .null])),
     ("incoming-null", sendC7 (incoming := .null)),
     ("incoming-no-int", sendC7 (incoming := tup #[.null])),
     ("prices-null", sendC7 (config := unpackedConfig .null .null .null)),
     ("prices-malformed", sendC7 (config := unpackedConfig (sl (natToBits 0xeb 8)) (sl (natToBits 0xea 8 ++ natToBits 1 40)) .null)),
     ("limits-malformed", sendC7 (config := unpackedConfig (fwdPrices 1 2 3) (fwdPrices 1 2 3) (sl (natToBits 4 8)))),
     ("limits-v1-truncated", sendC7 (config := unpackedConfig (fwdPrices 1 2 3) (fwdPrices 1 2 3)
        (sl (natToBits 1 8 ++ natToBits 65535 32 ++ natToBits 2 32)))),
     ("limits-v1-trailing", sendC7 (config := unpackedConfig (fwdPrices 1 2 3) (fwdPrices 1 2 3)
        (sl (sizeLimitsBits 2 ++ #[true])))),
     ("config-short", sendC7 (config := tup #[.null, .null, .null, .null, fwdPrices 1 2 3, fwdPrices 1 2 3])),
     ("config-5", sendC7 (config := tup #[.null, .null, .null, .null, fwdPrices 1 2 3])),
     ("config-not-tuple", sendC7 (config := iv 5)) ]

/-- Size limits that apply (counted cells limited to 2): v1, v2 with and without
`max_transaction_library_loads`, v3; and values that are not slices (the defaults apply). -/
private def sendC7Limits : Array (String × Array Value) :=
  let v2 (loads : Bool) : BitString :=
    natToBits 2 8 ++ (sizeLimitsBits 2).extract 8 168 ++ natToBits 100 32 ++ natToBits 200 32 ++ natToBits 300 32 ++
      natToBits 400 32 ++ natToBits 500 32 ++ natToBits 8 8 ++ natToBits 600 32 ++
      (if loads then #[true] ++ natToBits 7 32 else #[false])
  let v3 : BitString := natToBits 3 8 ++ (v2 true).extract 8 (v2 true).size ++ natToBits 1000 32 ++ natToBits 2000 32
  let cfg (l : Value) : Array Value := sendC7 (config := unpackedConfig (fwdPrices 1 2 3) (fwdPrices 400000 26214400 2621440000) l)
  #[("limits-v2", cfg (sl (v2 false))), ("limits-v2-loads", cfg (sl (v2 true))), ("limits-v3", cfg (sl v3)),
    ("limits-int", cfg (iv 2)), ("limits-cell", cfg (.cell (Cell.mkOrdinary (sizeLimitsBits 2) #[]))),
    ("limits-tuple", cfg (tup #[]))]

/-- `extra_currencies` dictionary with one entry (HashmapE 32 (VarUInteger 32)). -/
private def extraDict : Cell :=
  match dictSetSliceWithCells none (natToBits 7 32) (Slice.ofCell (Cell.mkOrdinary (natToBits 1 5 ++ natToBits 100 8) #[])) .set with
  | .ok (some r, _, _, _) => r
  | _ => Cell.empty

/-- An internal message: header (src addr_none), then the StateInit and the body, each `(inline bits,
refs)` or in a reference (`init := some (true, c)`). -/
private def intMsgWith (wc : Nat) (value : Nat) (extra : Bool) (fwdFee : Nat)
    (init : Option (Bool × BitString × Array Cell)) (bodyRef : Bool) (bodyBits : BitString) (bodyRefs : Array Cell) :
    Cell :=
  let hdr := #[false, true, true, false] ++ natToBits 0 2 ++ addrStd wc 0x1234 ++ grams value ++ #[extra] ++
    grams 0 ++ grams fwdFee ++ natToBits 0 64 ++ natToBits 0 32
  let hdrRefs : Array Cell := if extra then #[extraDict] else #[]
  let (initBits, initRefs) : BitString × Array Cell :=
    match init with
    | none => (#[false], #[])
    | some (false, b, rs) => (#[true, false] ++ b, rs)
    | some (true, b, rs) => (#[true, true], #[Cell.mkOrdinary b rs])
  let (bBits, bRefs) : BitString × Array Cell :=
    if bodyRef then (#[true], #[Cell.mkOrdinary bodyBits bodyRefs]) else (#[false] ++ bodyBits, bodyRefs)
  Cell.mkOrdinary (hdr ++ initBits ++ bBits) (hdrRefs ++ initRefs ++ bRefs)

private def leaf (n : Nat) : Cell := Cell.mkOrdinary (natToBits n 16) #[]

/-- StateInit: no prefix length, special (tick), code and data, no library. -/
private def stateInit : BitString × Array Cell := (#[false, true, true, false, true, true, false], #[leaf 1, leaf 2])

private def sendMsgPool : Array (String × Cell) :=
  #[ ("init-inline", intMsgWith 0 100 false 0 (some (false, stateInit.1, stateInit.2)) false #[] #[]),
     ("init-ref", intMsgWith 0 100 false 0 (some (true, stateInit.1, stateInit.2)) true (natToBits 5 8) #[]),
     ("body-inline-refs", intMsgWith 0 100 true 0 none false #[] #[leaf 7, leaf 8, leaf 9]),
     ("body-ref", intMsgWith 0 100 false 0 none true (natToBits 0xabcd 16) #[leaf 11]),
     ("extra-currencies", intMsgWith 0 100 true 0 none false (natToBits 3 2) #[]),
     ("mc-dest", intMsgWith 255 100 false 0 none false #[] #[]),
     ("user-fwd-fee", intMsgWith 0 100 false 1000000000 none false #[] #[]),
     -- two references to equal subtrees: counted once
     ("shared-subtrees", intMsgWith 0 100 false 0 none true #[]
        #[Cell.mkOrdinary (natToBits 1 8) #[leaf 12], Cell.mkOrdinary (natToBits 1 8) #[leaf 12]]),
     -- destinations a MessageRelaxed admits but parse_addr_workchain reads differently
     ("dest-var-mc", Cell.mkOrdinary (#[false, true, true, false] ++ natToBits 0 2 ++ natToBits 0b11 2 ++ #[false] ++
        natToBits 100 9 ++ natToBits (2 ^ 32 - 1) 32 ++ natToBits 5 100 ++ grams 100 ++ #[false] ++ grams 0 ++
        grams 0 ++ natToBits 0 64 ++ natToBits 0 32 ++ #[false, false]) #[]),
     ("dest-anycast-mc", Cell.mkOrdinary (#[false, true, true, false] ++ natToBits 0 2 ++ natToBits 0b10 2 ++ #[true] ++
        natToBits 3 5 ++ natToBits 5 3 ++ natToBits 255 8 ++ natToBits 7 256 ++ grams 100 ++ #[false] ++ grams 0 ++
        grams 0 ++ natToBits 0 64 ++ natToBits 0 32 ++ #[false, false]) #[]),
     -- addresses of the wrong kind or an anycast/addr_var source: TL-B decides (invalid -> unknown)
     ("dest-none", Cell.mkOrdinary (#[false, true, true, false] ++ natToBits 0 2 ++ natToBits 0 2 ++ grams 100 ++ #[false] ++
        grams 0 ++ grams 0 ++ natToBits 0 64 ++ natToBits 0 32 ++ #[false, false]) #[]),
     ("dest-anycast-depth0", Cell.mkOrdinary (#[false, true, true, false] ++ natToBits 0 2 ++ natToBits 0b10 2 ++ #[true] ++
        natToBits 0 5 ++ natToBits 0 8 ++ natToBits 7 256 ++ grams 100 ++ #[false] ++ grams 0 ++
        grams 0 ++ natToBits 0 64 ++ natToBits 0 32 ++ #[false, false]) #[]),
     ("src-var", Cell.mkOrdinary (#[false, true, true, false] ++ natToBits 0b11 2 ++ #[false] ++ natToBits 16 9 ++
        natToBits 5 32 ++ natToBits 1 16 ++ addrStd 0 0x1234 ++ grams 100 ++ #[false] ++ grams 0 ++
        grams 0 ++ natToBits 0 64 ++ natToBits 0 32 ++ #[false, false]) #[]),
     ("ext-dest-std", Cell.mkOrdinary (natToBits 0b11 2 ++ natToBits 0 2 ++ addrStd 0 5 ++ natToBits 0 64 ++
        natToBits 0 32 ++ #[false, false]) #[]),
     ("ext-src-anycast", Cell.mkOrdinary (natToBits 0b11 2 ++ natToBits 0b10 2 ++ #[true] ++ natToBits 2 5 ++
        natToBits 3 2 ++ natToBits 0 8 ++ natToBits 9 256 ++ natToBits 0b01 2 ++ natToBits 8 9 ++ natToBits 0x77 8 ++
        natToBits 0 64 ++ natToBits 0 32 ++ #[false, false]) #[]),
     -- a body reference must end the message (type_unpack_cell: empty_ext)
     ("body-ref-trailing", Cell.mkOrdinary (#[false, true, true, false] ++ natToBits 0 2 ++ addrStd 0 0x1234 ++ grams 100 ++
        #[false] ++ grams 0 ++ grams 0 ++ natToBits 0 64 ++ natToBits 0 32 ++ #[false, true, true]) #[leaf 13]),
     ("body-ref-extra-ref", Cell.mkOrdinary (#[false, true, true, false] ++ natToBits 0 2 ++ addrStd 0 0x1234 ++ grams 100 ++
        #[false] ++ grams 0 ++ grams 0 ++ natToBits 0 64 ++ natToBits 0 32 ++ #[false, true]) #[leaf 13, leaf 14]),
     ("ext-out", extOutMsg) ]

/-- `MYADDR` slices: parse_addr_workchain (tonops.cpp) does not validate them: an anycast is
skipped only if its depth (5 bits, consumed anyway) is at most 30 and its prefix is there, the
workchain is int8 (addr_std) or int32 after 9 skipped bits (addr_var), and a field cut short
reads as 0; a first bit 0 (or none) is range_chk. -/
private def myAddrPool : Array (String × Value) :=
  let s (b : BitString) : Value := .slice (Slice.ofCell (Cell.mkOrdinary b #[]))
  #[("none", s (natToBits 0 2)), ("extern", s (natToBits 0b01 2 ++ natToBits 8 9 ++ natToBits 0xa5 8)),
    ("empty", s #[]), ("one-bit", s #[true]), ("var-cut", s #[true, true]),
    ("std-anycast-mc", s (natToBits 0b10 2 ++ #[true] ++ natToBits 3 5 ++ natToBits 5 3 ++ natToBits 255 8 ++ natToBits 1 256)),
    ("std-anycast-depth0-mc", s (natToBits 0b10 2 ++ #[true] ++ natToBits 0 5 ++ natToBits 255 8 ++ natToBits 1 256)),
    ("std-anycast-depth31", s (natToBits 0b10 2 ++ #[true] ++ natToBits 31 5 ++ natToBits 255 8)),
    ("std-anycast-cut", s (natToBits 0b10 2 ++ #[true] ++ natToBits 20 5 ++ natToBits 255 8)),
    ("std-wc-cut", s (natToBits 0b10 2 ++ #[false] ++ natToBits 15 4)),
    ("std-mc-only", s (natToBits 0b10 2 ++ #[false] ++ natToBits 255 8)),
    ("var-mc", s (natToBits 0b11 2 ++ #[false] ++ natToBits 64 9 ++ natToBits (2 ^ 32 - 1) 32 ++ natToBits 3 64)),
    ("var-len-cut", s (natToBits 0b11 2 ++ #[false] ++ natToBits 64 5)),
    ("var-wc-cut", s (natToBits 0b11 2 ++ #[false] ++ natToBits 64 9 ++ natToBits 255 8))]

/-- Inline bodies of `n` bits, with and without an inline StateInit: the message cell holds them, but
the root SENDMSG prices (`MYADDR` instead of addr_none, the fees written) may exceed 1023 bits, and
then the StateInit and/or the body move into references. The lengths cross both thresholds. -/
private def movingMsgs : Array (String × Cell) :=
  ((List.range 15).map (fun k => 560 + 5 * k)).toArray.flatMap fun n =>
    #[(s!"body{n}", intMsgWith 0 100 false 0 none false (natToBits 0x5a5 n) #[leaf 6]),
      (s!"init-body{n}", intMsgWith 0 100 false 0 (some (false, stateInit.1, stateInit.2)) false
        (natToBits 0x5a5 (n - 9)) #[leaf 6])]

private def sendMsgCoverageCases (suite : String) : Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for (ml, m) in movingMsgs do
    for (cl, c7) in #[("base", sendC7), ("mc-myaddr", sendC7 (myAddr := myAddrMc))] do
      out := out.push
        { name := s!"oracle/cov/moves/{cl}/{ml}", instr := { name := suite }, program := #[env .sendMsg],
          initStack := #[.cell m, iv 1024], initC7 := c7 }
  for (cl, c7) in sendC7Pool ++ sendC7Limits do
    for (ml, m) in sendMsgPool do
      for mode in (#[0, 64, 128, 1024] : Array Int) do
        out := out.push
          { name := s!"oracle/cov/{cl}/{ml}/mode{mode}", instr := { name := suite }, program := #[env .sendMsg],
            initStack := #[.cell m, iv mode], initC7 := c7 }
  for (al, a) in myAddrPool do
    for (ml, m) in #[sendMsgPool[0]!, sendMsgPool[sendMsgPool.size - 1]!] do
      out := out.push
        { name := s!"oracle/cov/myaddr-{al}/{ml}", instr := { name := suite }, program := #[env .sendMsg],
          initStack := #[.cell m, iv 0], initC7 := sendC7 (myAddr := a) }
  for (cl, c7) in sendC7Errors do
    for mode in (#[0, 64, 128] : Array Int) do
      out := out.push
        { name := s!"oracle/cov/{cl}/mode{mode}", instr := { name := suite }, program := #[env .sendMsg],
          initStack := #[.cell (sendMsgPool[0]!).2, iv mode], initC7 := c7 }
  return out

/-- Exotic message cells. C++ loads the message cell twice, both times by `load_cell_slice_impl`
(cells/CellSlice.cpp): `tlb::type_unpack_cell` and `load_cell_slice(msg_cell)` before the cells
are counted. A library cell is replaced by the root of its library: the root is parsed and the
cells below it counted, the action keeps the library cell. A missing library, a library cell
whose library is a library cell, a pruned branch and a Merkle proof are cell_und. -/
private def libMsgCases (suite : String) : Array OracleCase := Id.run do
  let lib := Tests.Gen.VmCore.libCell
  let mk (name : String) (msg : Cell) (libs : Array Cell) (mode : Int) : OracleCase :=
    { name := s!"oracle/cov/lib-msg/{name}/mode{mode}", instr := { name := suite }, program := #[env .sendMsg],
      initStack := #[.cell msg, iv mode], initC7 := sendC7,
      initLibraries := if libs.isEmpty then #[] else #[Tests.Gen.VmCore.libCollection libs] }
  let mut out : Array OracleCase := #[]
  for (ml, m) in sendMsgPool do
    for mode in (#[0, 1024] : Array Int) do
      out := out.push (mk s!"hit/{ml}" (lib m) #[m] mode)
  let m := (sendMsgPool[0]!).2
  let others : Array (String × Cell × Array Cell) :=
    #[("miss", lib m, #[]), ("recursive", lib (lib m), #[lib m, m]), ("not-a-message", lib (leaf 3), #[leaf 3]),
      ("pruned", Tests.Gen.VmCore.pruned, #[]), ("merkle-proof", Tests.Gen.VmCore.merkleProof m, #[])]
  for (n, c, libs) in others do
    for mode in (#[0, 1024] : Array Int) do
      out := out.push (mk n c libs mode)
  return out

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "SENDRAWMSG" => cross suite (env .sendRawMsg) (msgModeStacks #[0, 1, 2, 64, 128, 130, 255, 256, -1])
  | "SENDMSG" => cross suite (env .sendMsg) (msgModeStacks #[0, 1, 64, 128, 1024, 1025, 255, 256, -1]) ++
      sendMsgCoverageCases suite ++ libMsgCases suite
  | "RAWRESERVE" => cross suite (env .rawReserve)
      (((#[0, 1, 1000000000, 2 ^ 120 - 1, 2 ^ 120, -1] : Array Int).flatMap
        (fun a => (#[0, 1, 2, 3, 4, 8, 15, 16, 31, 32, -1] : Array Int).map (fun m => #[iv a, iv m]))) ++
        #[#[.null, iv 0], #[iv 5], #[]])
  | "RAWRESERVEX" => cross suite (env .rawReserveX)
      (((#[0, 1000, 2 ^ 120] : Array Int).flatMap (fun a =>
        (#[Value.null, .cell Cell.empty] : Array Value).flatMap (fun d =>
          (#[0, 2, 16, 32, -1] : Array Int).map (fun m => #[iv a, d, iv m])))) ++
        #[#[iv 1, iv 2, iv 0], #[iv 1, .null], #[]])
  | "SETCODE" => cross suite (env .setCode) #[#[.cell Cell.empty], #[.cell body], #[.null], #[iv 1], #[]]
  | "SETLIBCODE" => cross suite (env .setLibCode)
      (((#[0, 1, 2, 3, 16, 17, 18, -1] : Array Int).map (fun m => #[.cell body, iv m])) ++
        #[#[.null, iv 1], #[.cell body], #[]])
  | "CHANGELIB" => cross suite (env .changeLib)
      (((#[0, 2 ^ 256 - 1, -1] : Array Int).flatMap (fun h =>
        (#[0, 1, 2, 3, 16, 17, 18, 19, 31, 32, -1] : Array Int).map (fun m => #[iv h, iv m]))) ++ #[#[.null, iv 1], #[iv 5], #[]])
  | _ => #[]

end Tests.Gen.Msg

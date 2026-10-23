import Tests.Harness.Registry
import Tests.Harness.Gen.VmCore

/-!
Oracle cases for the TON environment instructions (C++ `crypto/vm/tonops.cpp`): each instruction
variant runs under a pool of `c7` values (the default `c7` of the oracle, full / long / short / empty
parameter tuples, a non-tuple `c7[0]`, parameters of wrong types, globals) and a pool of stacks
(integers incl. out-of-range ones, address slices, wrong types), and the model is compared with C++:
exit code, gas, stack, `c4`/`c5`. `initC7 = #[]` means the oracle's default `c7`.
-/

namespace Tests.Gen.TonEnv

open TvmLean

private def iv (n : Int) : Value := .int (.num n)
private def tup (xs : Array Value) : Value := .tuple xs
private def sl (bits : BitString) : Value := .slice (Slice.ofCell (Cell.mkOrdinary bits #[]))

/-- addr_std$10 anycast:nothing wc:int8 addr:bits256 -/
private def addrStdBits (wc : Nat) (h : Nat) : BitString :=
  natToBits 0b10 2 ++ #[false] ++ natToBits wc 8 ++ natToBits h 256

/-- Message address slices: valid forms of every kind, truncated and with trailing bits. -/
def addrPool : Array Value :=
  #[ sl (natToBits 0 2),                                                   -- addr_none
     sl (natToBits 0b01 2 ++ natToBits 8 9 ++ natToBits 0xa5 8),           -- addr_extern
     sl (addrStdBits 0 0x1234567890abcdef),                                -- addr_std, basechain
     sl (addrStdBits 255 0xfedcba),                                        -- addr_std, masterchain
     sl (natToBits 0b10 2 ++ #[true] ++ natToBits 3 5 ++ natToBits 5 3 ++ natToBits 0 8 ++
         natToBits 0x77 256),                                              -- addr_std with anycast
     sl (natToBits 0b11 2 ++ #[false] ++ natToBits 64 9 ++ natToBits 7 32 ++ natToBits 0xab 64), -- addr_var
     sl (natToBits 0b10 2 ++ #[false] ++ natToBits 0 8 ++ natToBits 1 100), -- truncated addr_std
     sl (addrStdBits 0 0x42 ++ natToBits 5 3),                             -- addr_std + 3 extra bits
     sl #[true],                                                           -- too short
     sl (natToBits 0b01 2 ++ natToBits 3 5),                               -- addr_extern, length cut
     sl (natToBits 0b01 2 ++ natToBits 100 9 ++ natToBits 5 10),           -- addr_extern, data cut
     sl (natToBits 0b10 2 ++ #[false] ++ natToBits 5 4),                   -- addr_std, workchain cut
     sl (natToBits 0b10 2),                                                -- addr_std, nothing after the tag
     iv 5, .null ]

/-- A full parameter tuple of length `len` (the slots TON defines get values of the right shape). -/
def params (len : Nat) : Array Value :=
  (Array.range len).map fun i =>
    match i with
    | 0 => iv 0x076ef1ea
    | 7 => tup #[iv 5000, .null]
    | 8 => sl (addrStdBits 0 0x99)
    | 9 => .null
    | 10 => .cell Cell.empty
    | 11 => tup #[iv 777, .null]
    | 13 => tup #[tup #[iv 1, iv 2], tup #[iv 3], tup #[]]
    | 14 => tup #[iv 11, iv 12, iv 13]
    | 17 => tup ((Array.range 10).map (fun k => iv (300 + Int.ofNat k)))
    | _ => iv (1000 + Int.ofNat i)

/-- Parameters whose structured slots hold integers instead of tuples. -/
private def paramsWrongTypes : Array Value :=
  (params 18).set! 7 (iv 1) |>.set! 13 (iv 2) |>.set! 14 (iv 3) |>.set! 17 (iv 4)

/-- `c7` whose `CONFIGROOT` (`c7[0][9]`) is a configuration dictionary (HashmapE 32 ^Cell, signed
keys 0, 8, 34, -1, each value a cell holding its key), or a cell that is not a dictionary. -/
private def configC7Pool : Array (String × Array Value) :=
  let entries : List Int := [0, 8, 34, -1]
  let root := entries.foldl (fun root k =>
    match dictSetRefWithCells root (natToBits ((k + 2 ^ 32).toNat % 2 ^ 32) 32)
        (Cell.mkOrdinary (natToBits ((k + 256).toNat % 256) 8) #[]) .set with
    | .ok (some r, _, _, _) => some r
    | _ => root) none
  let withRoot (v : Value) : Array Value := #[tup ((params 18).set! 9 v)]
  #[("config-dict", withRoot (match root with | some r => .cell r | none => .null)),
    ("config-not-dict", withRoot (.cell (Cell.mkOrdinary #[true] #[]))),
    ("config-int", withRoot (iv 9))]

/-- The `c7` pool (contents of `c7`; `#[]` = the oracle's default). A parameter tuple of 255 entries
is read; one of 256 is not (`get_param` and the other readers of `c7[0]` take it
`as_tuple_range(255)`, tonops.cpp:121-128, stack.cpp:312-319: type_chk); `c7` itself may have more
than 255 entries (`GETGLOB`, `SETGLOB`: `tuple_extend_index`, `tuple_extend_set_index`). -/
def c7Pool : Array (String × Array Value) :=
  #[ ("default", #[]),
     ("full18", #[tup (params 18)]),
     ("long20-globals", #[tup (params 20), iv 1, iv 2, .null, tup #[iv 3]]),
     ("short10", #[tup (params 10)]),
     ("empty-params", #[tup #[]]),
     ("c7-0-not-tuple", #[iv 5]),
     ("wrong-types", #[tup paramsWrongTypes]),
     ("params255", #[tup (params 255)]),
     ("params256", #[tup (params 256)]),
     ("c7-256", #[tup (params 18)] ++ (Array.range 255).map (fun k => iv (2000 + Int.ofNat k))) ]

/-- `c7[0]` with its entry `k` replaced by a tuple of `n` entries, the first ones `xs`, then integers
(the readers of an inner tuple of `c7[0]` take it `as_tuple_range(255)` or `as_tuple()`). -/
private def c7WithLong (k n : Nat) (xs : Array Value) : Array Value :=
  #[tup ((params 18).set! k (tup (xs ++ (Array.range (n - xs.size)).map (fun j => iv (3000 + Int.ofNat j)))))]

/-- The previous blocks' tuple `c7[0][13]` of 255 and 256 entries (`exec_get_prev_blocks_info`,
tonops.cpp:264-273: `as_tuple_range(255)`; `PREVBLOCKSINFOTUPLE` is `get_param(13)` and pushes it). -/
private def prevC7Pool : Array (String × Array Value) :=
  #[ ("prev255", c7WithLong 13 255 #[tup #[iv 1, iv 2], tup #[iv 3], tup #[]]),
     ("prev256", c7WithLong 13 256 #[tup #[iv 1, iv 2], tup #[iv 3], tup #[]]) ]

/-- The message's parameters `c7[0][17]` of 256 entries: `exec_get_in_msg_param` takes them
`as_tuple()` (tonops.cpp:169), of any length. -/
private def inMsgC7Pool : Array (String × Array Value) :=
  #[ ("inmsg256", c7WithLong 17 256 #[]) ]

private def cross (suite : String) (variants : Array (String × Instr)) (c7s : Array (String × Array Value))
    (stacks : Array (Array Value)) : Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for (vl, i) in variants do
    for (cl, c7) in c7s do
      for k in [0:stacks.size] do
        out := out.push
          { name := s!"oracle/{vl}/{cl}/stack{k}", instr := { name := suite }, program := #[i],
            initStack := stacks[k]!, initC7 := c7 }
  return out

private def noArgs : Array (Array Value) := #[#[], #[iv 1]]

/-- One integer argument per stack, plus wrong types. -/
private def ints1 (xs : Array Int) : Array (Array Value) := xs.map (fun n => #[iv n]) ++ #[#[.null], #[]]

private def env (o : TonEnvInstr) : Instr := .tonEnvOp o


/-! ### GETEXTRABALANCE (`exec_get_extra_currency_balance`)

The extra-currency dictionary `c7[0][7][1]` (HashmapE 32 (VarUInteger 32)) is looked up with the
cell loads charged specially for the first `get_extra_balance_cheap_count` (5) calls: at most
`get_extra_balance_cheap_max_gas_price` (200) per call, the rest counted as free gas, which
`RUNVM` with isolated gas (mode 128) charges to the parent (`vm.cpp`, `run_child_vm`). -/

/-- VarUInteger 32: 5-bit byte length, then the value. -/
private def varUInt32 (v : Nat) : BitString :=
  let len := if v = 0 then 0 else (Nat.log2 v + 8) / 8
  natToBits len 5 ++ natToBits v (8 * len)

/-- An extra-currency dictionary built by the model's dictionary insertion (C++ only reads it). -/
private def ecDict (entries : List (Nat × BitString)) : Value :=
  let root := entries.foldl (fun root (k, v) =>
    match dictSetSliceWithCells root (natToBits k 32) (Slice.ofCell (Cell.mkOrdinary v #[])) .set with
    | .ok (r, _, _, _) => r
    | .error _ => root) none
  match root with
  | some c => .cell c
  | none => .null

private def ecKeys : List Nat :=
  [0, 1, 2, 3, 7, 100, 1000, 65535, 2 ^ 31, 2 ^ 32 - 1, 12345678, 0xdeadbeef, 0x80000001, 0x7fffffff]

/-- Dictionaries: one entry; fourteen entries (lookups load up to six cells, beyond the cheap
limit); a value that is not a VarUInteger 32; a malformed root. -/
private def ecDicts : Array (String × Value) :=
  #[ ("null", .null),
     ("one", ecDict [(7, varUInt32 1000)]),
     ("many", ecDict (ecKeys.map (fun k => (k, varUInt32 (k * 1000 + (if k = 3 then 2 ^ 200 else 0)))))),
     ("zero-value", ecDict [(7, varUInt32 0), (8, varUInt32 5)]),
     ("bad-value", ecDict [(7, natToBits 31 5 ++ natToBits 1 8), (9, varUInt32 1)]),
     ("malformed-root", .cell (Cell.mkOrdinary #[true] #[])) ]

/-- `c7` with the balance tuple `bal` in `c7[0][7]`. -/
private def c7WithBalance (bal : Value) : Array Value := #[tup ((params 18).set! 7 bal)]

private def ecC7Pool : Array (String × Array Value) :=
  ecDicts.map (fun (n, d) => (s!"dict-{n}", c7WithBalance (tup #[iv 5000, d]))) ++
    #[ ("default", #[]), ("bal-short", c7WithBalance (tup #[iv 5000])),
       ("bal-int", c7WithBalance (tup #[iv 5000, iv 1])), ("bal-not-tuple", c7WithBalance (iv 5)),
       ("bal-long", c7WithBalance (tup #[iv 5000, ecDicts[1]!.2, iv 1])),
       -- the balance of 255 and 256 entries (tonops.cpp:398: `as_tuple_range(255)`)
       ("bal-255", c7WithBalance (tup (#[iv 5000, ecDicts[1]!.2] ++ Array.replicate 253 .null))),
       ("bal-256", c7WithBalance (tup (#[iv 5000, ecDicts[1]!.2] ++ Array.replicate 254 .null))),
       ("params-256", #[tup ((params 256).set! 7 (tup #[iv 5000, ecDicts[1]!.2]))]),
       ("params-short", #[tup (params 7)]), ("c7-empty", #[tup #[]]), ("c7-0-not-tuple", #[iv 5]) ]

private def getExtraBalance : Instr := env .getExtraBalance

/-- Several calls in a row: the cheap limit, the switch to ordinary gas after five calls, reloads
of cells loaded by earlier calls; then `RUNVM` with and without isolated gas (an empty child). -/
private def ecSeqCases (suite : String) : Array OracleCase := Id.run do
  let c7 := c7WithBalance (tup #[iv 5000, ecDicts[2]!.2])
  let call (k : Nat) : Array Instr := #[.pushInt (.num (Int.ofNat k)), getExtraBalance, .pop 0]
  let seqs : Array (String × List Nat) :=
    #[("distinct7", [0, 0xdeadbeef, 1000, 2 ^ 31, 65535, 3, 0x7fffffff]), ("same7", [7, 7, 7, 7, 7, 7, 7]),
      ("absent7", [5, 6, 8, 9, 10, 11, 12])]
  let mut out : Array OracleCase := #[]
  for (name, ks) in seqs do
    let prog := (ks.toArray.map call).flatten
    out := out.push { name := s!"oracle/seq/{name}", instr := { name := suite }, program := prog, initC7 := c7 }
    for mode in [0, 128] do
      out := out.push
        { name := s!"oracle/seq/{name}/runvm{mode}", instr := { name := suite },
          program := prog ++ #[.contExt (.runvm mode)],
          initStack := #[iv 0, .slice (Slice.ofCell Cell.empty)], initC7 := c7 }
  -- free gas charged by an isolated RUNVM may exceed what is left
  out := out.push
    { name := "oracle/seq/distinct7/runvm128/low-gas", instr := { name := suite },
      program := #[.pushInt (.num 3000), .tonEnvOp .setGasLimit] ++ ((seqs[0]!.2.toArray.map call).flatten) ++
        #[.contExt (.runvm 128)],
      initStack := #[iv 0, .slice (Slice.ofCell Cell.empty)], initC7 := c7 }
  return out

/-- A library cell as the dictionary or as a node of it. C++ loads the nodes with
`load_cell_slice_impl` under the call's `VmStateInterface` (`LocalVmState` for the cheap calls,
whose `load_library` asks the VM): the library's root replaces it, a missing library is cell_und. -/
private def ecLibCases (suite : String) : Array OracleCase := Id.run do
  let lib := Tests.Gen.VmCore.libCell
  let root : Cell := match ecDicts[2]!.2 with | .cell c => c | _ => Cell.empty
  -- the root with its first child replaced by a library cell of that child
  let child : Cell := root.refs[0]!
  let rootChildLib : Cell := Cell.mkOrdinary root.bits (root.refs.set! 0 (lib child))
  let dicts : Array (String × Cell × Array Cell) :=
    #[("root-lib-hit", lib root, #[root]), ("root-lib-miss", lib root, #[]),
      ("child-lib-hit", rootChildLib, #[child]), ("child-lib-miss", rootChildLib, #[])]
  let mut out : Array OracleCase := #[]
  for (dn, d, libs) in dicts do
    let c7 := c7WithBalance (tup #[iv 5000, .cell d])
    let initLibraries := if libs.isEmpty then #[] else #[Tests.Gen.VmCore.libCollection libs]
    for k in [0, 7, 0xdeadbeef, 5] do
      out := out.push
        { name := s!"oracle/lib/{dn}/key{k}", instr := { name := suite }, program := #[getExtraBalance],
          initStack := #[iv k], initC7 := c7, initLibraries }
    -- seven calls: five cheap (LocalVmState), then the VM's own interface
    let call (k : Nat) : Array Instr := #[.pushInt (.num (Int.ofNat k)), getExtraBalance, .pop 0]
    out := out.push
      { name := s!"oracle/lib/{dn}/seq7", instr := { name := suite },
        program := (#[0, 0xdeadbeef, 1000, 2 ^ 31, 65535, 3, 7].map call).flatten, initC7 := c7, initLibraries }
  return out

/-! ### Config-dependent instructions on real and malformed config entries

`c7[0][14]` (the unpacked config) with storage prices, a global id, gas prices in each form
(`gas_flat_pfx` around `gas_prices_ext`, plain `gas_prices`, plain `gas_prices_ext`) and
forwarding prices; then entries with a wrong tag, cut short, or with trailing bits. The coverage
run of 2026-10-19 never reached `do_get_one_storage_prices`, a global id under 32 bits, or the
unflattened gas prices. -/

private def u64 (n : Nat) : BitString := natToBits n 64
private def storagePrices (bp cp mbp mcp : Nat) : BitString :=
  natToBits 0xcc 8 ++ natToBits 1700000000 32 ++ u64 bp ++ u64 cp ++ u64 mbp ++ u64 mcp
private def gasDd (price : Nat) : BitString :=
  natToBits 0xdd 8 ++ u64 price ++ u64 1000000 ++ u64 10000 ++ u64 10000000 ++ u64 100000000 ++ u64 1000000000
private def gasDe (price : Nat) : BitString :=
  natToBits 0xde 8 ++ u64 price ++ u64 1000000 ++ u64 35000000 ++ u64 10000 ++ u64 10000000 ++ u64 100000000 ++
    u64 1000000000
private def gasFlat (limit price : Nat) (other : BitString) : BitString :=
  natToBits 0xd1 8 ++ u64 limit ++ u64 price ++ other
private def fwdPrices (lump bit cell : Nat) : BitString :=
  natToBits 0xea 8 ++ u64 lump ++ u64 bit ++ u64 cell ++ natToBits 98304 32 ++ natToBits 21845 16 ++ natToBits 21845 16

private def cfgC7 (entries : Array Value) : Array Value := #[tup ((params 18).set! 14 (tup entries))]

/-- The unpacked config `c7[0][14]` of 255 and 256 entries (`get_unpacked_config_tuple`,
tonops.cpp:131-142: `as_tuple_range(255)`; `UNPACKEDCONFIGTUPLE` is `get_param(14)` and pushes it). -/
private def cfgLongC7Pool : Array (String × Array Value) :=
  #[ ("cfg-255", c7WithLong 14 255 #[sl (storagePrices 1 500 1000 500000), sl (natToBits (2 ^ 32 - 239) 32),
        sl (gasFlat 100 1000000 (gasDe 655360000)), sl (gasFlat 100 40000 (gasDe 26214400)),
        sl (fwdPrices 10000000 655360000 65536000000), sl (fwdPrices 400000 26214400 2621440000), .null]),
     ("cfg-256", c7WithLong 14 256 #[sl (storagePrices 1 500 1000 500000), sl (natToBits (2 ^ 32 - 239) 32),
        sl (gasFlat 100 1000000 (gasDe 655360000)), sl (gasFlat 100 40000 (gasDe 26214400)),
        sl (fwdPrices 10000000 655360000 65536000000), sl (fwdPrices 400000 26214400 2621440000), .null]) ]

def cfgC7Pool : Array (String × Array Value) :=
  cfgLongC7Pool ++
  #[ ("cfg-flat", cfgC7 #[sl (storagePrices 1 500 1000 500000), sl (natToBits (2 ^ 32 - 239) 32),
        sl (gasFlat 100 1000000 (gasDe 655360000)), sl (gasFlat 100 40000 (gasDe 26214400)),
        sl (fwdPrices 10000000 655360000 65536000000), sl (fwdPrices 400000 26214400 2621440000), .null]),
     ("cfg-dd", cfgC7 #[sl (storagePrices 7 11 13 17), sl (natToBits 5 32), sl (gasDd 65536000), sl (gasDd 26214400),
        sl (fwdPrices 1 2 3), sl (fwdPrices 4 5 6), .null]),
     ("cfg-de", cfgC7 #[sl (storagePrices 0 0 0 0), sl (natToBits 0x7fffffff 32), sl (gasDe 1), sl (gasDe 65536),
        sl (fwdPrices 0 0 0), sl (fwdPrices 1 0 0), .null]),
     ("cfg-wrong-tag", cfgC7 #[sl (natToBits 0xcd 8 ++ (storagePrices 1 2 3 4).extract 8 296), sl (natToBits 3 31),
        sl (natToBits 0xdc 8 ++ (gasDd 1).extract 8 392), sl (natToBits 0xd2 8 ++ (gasDd 1).extract 8 392),
        sl (natToBits 0xeb 8 ++ (fwdPrices 1 2 3).extract 8 328), sl (natToBits 0xeb 8), .null]),
     ("cfg-cut", cfgC7 #[sl ((storagePrices 1 2 3 4).extract 0 100), sl (natToBits 1 16),
        sl ((gasFlat 100 1 (gasDd 1)).extract 0 200), sl ((gasDd 1).extract 0 300),
        sl ((fwdPrices 1 2 3).extract 0 200), sl ((fwdPrices 1 2 3).extract 0 300), .null]),
     ("cfg-trailing", cfgC7 #[sl (storagePrices 1 2 3 4 ++ natToBits 5 3), sl (natToBits 0x80000001 40),
        sl (gasDd 3 ++ #[true]), sl (gasDe 3 ++ #[true]), sl (fwdPrices 1 2 3 ++ #[true]), sl (fwdPrices 4 5 6 ++ #[true]), .null]),
     -- entries that are not slices (`as_slice()` null: no storage prices; type_chk for the gas and
     -- forwarding prices, `util::get_{gas,msg}_prices`; the global id)
     ("cfg-ints", cfgC7 #[iv 1, iv 2, iv 3, iv 4, iv 5, iv 6, iv 7]),
     ("cfg-nulls", cfgC7 #[.null, .null, .null, .null, .null, .null, .null]),
     ("cfg-cells", cfgC7 (Array.replicate 7 (.cell (Cell.mkOrdinary (fwdPrices 1 2 3) #[])))),
     -- flat gas prices of 2^63 or more, which `compute_gas_price` adds as `long long` above the flat
     -- limit (mc-config.h:363-367) and returns whole within it; gas prices of 2^63 or more (whole)
     ("cfg-flat-high", cfgC7 #[sl (storagePrices 1 500 1000 500000), sl (natToBits 5 32),
        sl (gasFlat 100 (2 ^ 63 + 5) (gasDe 655360000)), sl (gasFlat 100 (2 ^ 64 - 1) (gasDe 26214400)),
        sl (fwdPrices 1 2 3), sl (fwdPrices 4 5 6), .null]),
     ("cfg-flat-max", cfgC7 #[sl (storagePrices 1 500 1000 500000), sl (natToBits 5 32),
        sl (gasFlat 1000000 (2 ^ 63 - 1) (gasDe 655360000)), sl (gasFlat 0 (2 ^ 63) (gasDe 26214400)),
        sl (fwdPrices 1 2 3), sl (fwdPrices 4 5 6), .null]),
     ("cfg-price-high", cfgC7 #[sl (storagePrices 1 500 1000 500000), sl (natToBits 5 32),
        sl (gasFlat 100 (2 ^ 64 - 1) (gasDe (2 ^ 64 - 1))), sl (gasDd (2 ^ 63 + 1)),
        sl (fwdPrices 1 2 3), sl (fwdPrices 4 5 6), .null]),
     -- storage prices of 2^63 or more, which `calculate_storage_fee` multiplies by as `long long`
     -- (tonops.cpp:2621-2638); forwarding prices of 2^63 or more, whole in `compute_fwd_fees256` and
     -- the other fee instructions
     ("cfg-storage-high", cfgC7 #[sl (storagePrices (2 ^ 64 - 1) (2 ^ 40) (2 ^ 63 + 5) (2 ^ 63 - 1)), sl (natToBits 5 32),
        sl (gasFlat 100 1000000 (gasDe 655360000)), sl (gasFlat 100 40000 (gasDe 26214400)),
        sl (fwdPrices (2 ^ 64 - 1) (2 ^ 64 - 1) (2 ^ 63)), sl (fwdPrices (2 ^ 63) 1 (2 ^ 64 - 1)), .null]) ]

/-- Random seeds `c7[0][6]` that are not integers, negative (range_chk: no TVM integer reaches 2^256),
the largest, and a parameter tuple without
slot 6 (`tuple_index`: range_chk for RAND, RANDU256 and ADDRAND; SETRAND extends it). -/
def seedC7Pool : Array (String × Array Value) :=
  #[ ("seed-null", #[tup ((params 18).set! 6 .null)]),
     ("seed-tuple", #[tup ((params 18).set! 6 (tup #[]))]),
     ("seed-neg", #[tup ((params 18).set! 6 (iv (-1)))]),
     ("seed-max", #[tup ((params 18).set! 6 (iv (2 ^ 256 - 1)))]),
     ("params6", #[tup (params 6)]) ]

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  let one (o : TonEnvInstr) : Array OracleCase := cross suite #[(suite, env o)] c7Pool noArgs
  match suite with
  | "NOW" => one .now
  | "BLOCKLT" => one .blockLt
  | "LTIME" => one .lTime
  | "RANDSEED" => one .randSeed
  | "BALANCE" => one .balance
  | "MYADDR" => one .myAddr
  | "CONFIGROOT" => one .configRoot
  | "MYCODE" => one .myCode
  | "INCOMINGVALUE" => one .incomingValue
  | "STORAGEFEES" => one .storageFees
  | "PREVBLOCKSINFOTUPLE" => cross suite #[(suite, env .prevBlocksInfoTuple)] (c7Pool ++ prevC7Pool) noArgs
  | "PREVMCBLOCKS" => cross suite #[(suite, env .prevMcBlocks)] (c7Pool ++ prevC7Pool) noArgs
  | "PREVKEYBLOCK" => cross suite #[(suite, env .prevKeyBlock)] (c7Pool ++ prevC7Pool) noArgs
  | "PREVMCBLOCKS_100" => cross suite #[(suite, env .prevMcBlocks100)] (c7Pool ++ prevC7Pool) noArgs
  | "UNPACKEDCONFIGTUPLE" => cross suite #[(suite, env .unpackedConfigTuple)] (c7Pool ++ cfgLongC7Pool) noArgs
  | "DUEPAYMENT" => one .duePayment
  | "GETPRECOMPILEDGAS" => one .getPrecompiledGas
  | "GLOBALID" => cross suite #[("globalid", env .globalId)] (c7Pool ++ cfgC7Pool) noArgs
  | "GASCONSUMED" => one .gasConsumed
  | "ACCEPT" => one .accept
  | "COMMIT" => one .commit
  | "INMSGPARAMS" => cross suite #[("idx17", env (.getParam 17))] (c7Pool ++ inMsgC7Pool) noArgs
  | "GETPARAM" => cross suite (#[0, 1, 3, 6, 9, 15].map (fun k => (s!"k{k}", env (.getParam k)))) c7Pool noArgs
  | "GETPARAMLONG" => cross suite (#[16, 17, 18, 19, 20, 100].map (fun k => (s!"k{k}", env (.getParam k)))) c7Pool noArgs
  | "GETPARAMLONG2" => cross suite (#[127, 128, 200, 254].map (fun k => (s!"k{k}", env (.getParam k)))) c7Pool noArgs
  | "INMSG_BOUNCE" => cross suite #[(suite, env (.inMsgParam 0))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSG_BOUNCED" => cross suite #[(suite, env (.inMsgParam 1))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSG_SRC" => cross suite #[(suite, env (.inMsgParam 2))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSG_FWDFEE" => cross suite #[(suite, env (.inMsgParam 3))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSG_LT" => cross suite #[(suite, env (.inMsgParam 4))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSG_UTIME" => cross suite #[(suite, env (.inMsgParam 5))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSG_ORIGVALUE" => cross suite #[(suite, env (.inMsgParam 6))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSG_VALUE" => cross suite #[(suite, env (.inMsgParam 7))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSG_VALUEEXTRA" => cross suite #[(suite, env (.inMsgParam 8))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSG_STATEINIT" => cross suite #[(suite, env (.inMsgParam 9))] (c7Pool ++ inMsgC7Pool) noArgs
  | "INMSGPARAM" => cross suite (#[10, 11, 15].map (fun k => (s!"k{k}", env (.inMsgParam k)))) (c7Pool ++ inMsgC7Pool) noArgs
  | "GETGLOB" => cross suite (#[1, 2, 3, 5, 31].map (fun k => (s!"k{k}", env (.getGlob k)))) c7Pool noArgs
  | "SETGLOB" => cross suite (#[1, 2, 5, 31].map (fun k => (s!"k{k}", env (.setGlob k)))) c7Pool
      #[#[iv 42], #[tup #[iv 1]], #[]]
  | "GETGLOBVAR" => cross suite #[("var", env .getGlobVar)] c7Pool (ints1 #[0, 1, 2, 3, 5, 31, 254, 255, -1])
  | "SETGLOBVAR" => cross suite #[("var", env .setGlobVar)] c7Pool
      ((#[0, 1, 2, 5, 31, 254, 255, -1] : Array Int).map (fun k => #[iv 42, iv k]) ++ #[#[iv 42], #[]])
  | "RANDU256" => cross suite #[("randu256", env .randu256)] (c7Pool ++ seedC7Pool) noArgs
  | "RAND" => cross suite #[("rand", env .rand)] (c7Pool ++ seedC7Pool) (ints1 #[0, 1, 1000, -5, 2 ^ 256 - 1])
  | "SETRAND" => cross suite #[("setrand", env (.setRand false))] (c7Pool ++ seedC7Pool) (ints1 #[0, 1, 2 ^ 256 - 1, -1, -(2 ^ 256)]) ++
      -- a parameter tuple shorter than 7 is extended (consume_tuple_gas(tpay)), then c7 is charged
      -- (consume_tuple_gas(tuple)): gas may run out at the first charge (exec_set_rand)
      ((Array.range 14).map fun k =>
        { name := s!"oracle/gas/short-params/limit{72 + k}", instr := { name := suite },
          program := #[.pushInt (.num (Int.ofNat (72 + k))), .tonEnvOp .setGasLimit, env (.setRand false)],
          initStack := #[iv 5], initC7 := #[tup #[iv 1, iv 2]] })
  | "ADDRAND" => cross suite #[("addrand", env (.setRand true))] (c7Pool ++ seedC7Pool) (ints1 #[0, 1, 2 ^ 256 - 1, -1, -(2 ^ 256)])
  | "SETGASLIMIT" => cross suite #[("setgaslimit", env .setGasLimit)] #[("default", #[])]
      (ints1 #[0, 1, 100, 1000000, -1, 2 ^ 63, 2 ^ 64])
  | "CONFIGDICT" => one .configDict
  | "CONFIGPARAM" => cross suite #[("param", env (.configParam false))] (c7Pool ++ configC7Pool)
      (ints1 #[0, 1, 8, 34, -1, 2 ^ 32, -(2 ^ 31), 2 ^ 31])
  | "CONFIGOPTPARAM" => cross suite #[("optparam", env (.configParam true))] (c7Pool ++ configC7Pool)
      (ints1 #[0, 1, 8, 34, -1, 2 ^ 32, -(2 ^ 31), 2 ^ 31])
  | "PARSEMSGADDR" => cross suite #[("parse", env (.parseMsgAddr false))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "PARSEMSGADDRQ" => cross suite #[("parseq", env (.parseMsgAddr true))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "REWRITESTDADDR" => cross suite #[("rw", env (.rewriteStdAddr false))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "REWRITESTDADDRQ" => cross suite #[("rwq", env (.rewriteStdAddr true))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "REWRITEVARADDR" => cross suite #[("rw", env (.rewriteVarAddr false))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "REWRITEVARADDRQ" => cross suite #[("rwq", env (.rewriteVarAddr true))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "GETGASFEE" => cross suite #[("fee", env .getGasFee)] (c7Pool ++ cfgC7Pool)
      ((#[0, 1, 1000, 1000000, -1, 2 ^ 63, 2 ^ 63 - 1] : Array Int).flatMap (fun g => #[#[iv g, iv 0], #[iv g, iv (-1)]]) ++ #[#[iv 1], #[]])
  | "GETGASFEESIMPLE" => cross suite #[("fee", env .getGasFeeSimple)] (c7Pool ++ cfgC7Pool)
      ((#[0, 1, 1000, 1000000, -1, 2 ^ 63, 2 ^ 63 - 1] : Array Int).flatMap (fun g => #[#[iv g, iv 0], #[iv g, iv (-1)]]) ++ #[#[iv 1], #[]])
  | "GETSTORAGEFEE" => cross suite #[("fee", env .getStorageFee)] (c7Pool ++ cfgC7Pool)
      #[#[iv 1, iv 100, iv 3600, iv 0], #[iv 10, iv 10000, iv 86400, iv (-1)], #[iv 0, iv 0, iv 0, iv 0],
        #[iv (-1), iv 1, iv 1, iv 0], #[iv (2 ^ 63), iv 1, iv 1, iv 0], #[iv 1, iv 1, iv 1], #[],
        #[iv (2 ^ 63 - 1), iv (2 ^ 63 - 1), iv (2 ^ 63 - 1), iv 0], #[iv 3, iv (2 ^ 63 - 1), iv 7, iv (-1)]]
  | "GETFORWARDFEE" => cross suite #[("fee", env .getForwardFee)] (c7Pool ++ cfgC7Pool)
      #[#[iv 1, iv 100, iv 0], #[iv 10, iv 10000, iv (-1)], #[iv 0, iv 0, iv 0], #[iv (-1), iv 1, iv 0],
        #[iv (2 ^ 63), iv 1, iv 0], #[iv 1, iv 1], #[]]
  | "GETFORWARDFEESIMPLE" => cross suite #[("fee", env .getForwardFeeSimple)] (c7Pool ++ cfgC7Pool)
      #[#[iv 1, iv 100, iv 0], #[iv 10, iv 10000, iv (-1)], #[iv 0, iv 0, iv 0], #[iv (-1), iv 1, iv 0],
        #[iv (2 ^ 63), iv 1, iv 0], #[iv 1, iv 1], #[]]
  | "GETORIGINALFWDFEE" => cross suite #[("fee", env .getOriginalFwdFee)] (c7Pool ++ cfgC7Pool)
      #[#[iv 0, iv 0], #[iv 1000, iv 0], #[iv 1000, iv (-1)], #[iv (-1), iv 0], #[iv (2 ^ 63), iv 0], #[iv 1], #[]]
  | "GETEXTRABALANCE" => cross suite #[("get", getExtraBalance)] ecC7Pool
      (ints1 #[7, 8, 0, 3, 1000, 0xdeadbeef, 2 ^ 32 - 1, 2 ^ 32, -1]) ++ ecSeqCases suite ++ ecLibCases suite
  | _ => #[]

end Tests.Gen.TonEnv

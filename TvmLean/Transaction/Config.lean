import TvmLean.Transaction.Tlb

/-!
# The configuration a transaction reads

C++ `block::Config` (`crypto/block/mc-config.cpp`) as the transaction emulator builds it
(`emulator/emulator-extern.cpp`, `decode_config`: modes `needWorkchainInfo | needSpecialSmc |
needCapabilities`), and the phase configurations `FetchConfigParams::fetch_config_params`
(`transaction.cpp`) takes from it.
-/

namespace TvmLean.Tx

/-- The entries of a `Hashmap n X` in ascending key order (C++ `check_for_each`), `none` for a
malformed dictionary. `fuel` bounds the depth (the key length suffices). -/
def dictEntriesAux : Nat → Cell → Nat → BitString → Option (Array (BitString × Slice))
  | 0, _, _, _ => none
  | fuel + 1, cell, n, pfx =>
      match parseDictLabel cell n with
      | .error _ => none
      | .ok lbl =>
          if lbl.len > n then none
          else
            let key := pfx ++ dictLabelBits lbl
            let rest := lbl.remainder.advanceBits lbl.storedBits
            if lbl.len = n then some #[(key, rest)]
            else if !rest.haveRefs 2 then none
            else do
              let l ← dictEntriesAux fuel rest.cell.refs[rest.refPos]! (n - lbl.len - 1) (key.push false)
              let r ← dictEntriesAux fuel rest.cell.refs[rest.refPos + 1]! (n - lbl.len - 1) (key.push true)
              return l ++ r

def dictEntries (root : Option Cell) (n : Nat) : Option (Array (BitString × Slice)) :=
  match root with
  | none => some #[]
  | some c => dictEntriesAux (n + 1) c n #[]

/-- The value under `key`, `none` if absent or the dictionary is malformed. -/
def dictGet (root : Option Cell) (key : BitString) : Option Slice :=
  match dictLookup root key with
  | .ok v => v
  | .error _ => none

/-- `storage_prices#cc utime_since:uint32 bit_price_ps:uint64 cell_price_ps:uint64
mc_bit_price_ps:uint64 mc_cell_price_ps:uint64`. -/
structure StoragePrices where
  validSince : Nat
  bitPrice : Nat
  cellPrice : Nat
  mcBitPrice : Nat
  mcCellPrice : Nat
  deriving Inhabited

/-- C++ `ComputePhaseConfig` gas fields with the due limits of `StoragePhaseConfig`
(`parse_GasLimitsPrices`): `gas_prices#dd`, `gas_prices_ext#de` (with `special_gas_limit`),
optionally under `gas_flat_pfx#d1`. -/
structure GasPrices where
  gasPrice : Nat
  gasLimit : Nat
  specialGasLimit : Nat
  gasCredit : Nat
  freezeDueLimit : Nat
  deleteDueLimit : Nat
  flatGasLimit : Nat := 0
  flatGasPrice : Nat := 0

/-- `msg_forward_prices#ea` (C++ `MsgPrices`). -/
structure MsgPrices where
  lumpPrice : Nat
  bitPrice : Nat
  cellPrice : Nat
  ihrPriceFactor : Nat
  firstFrac : Nat
  nextFrac : Nat

/-- C++ `SizeLimitsConfig` with its defaults (`mc-config.h`), used when parameter 43 is absent. -/
structure SizeLimits where
  maxMsgBits : Nat := 2 ^ 21
  maxMsgCells : Nat := 2 ^ 13
  maxLibraryCells : Nat := 1000
  maxVmDataDepth : Nat := 512
  maxExtMsgSize : Nat := 65535
  maxExtMsgDepth : Nat := 512
  maxAccStateCells : Nat := 2 ^ 16
  maxMcAccStateCells : Nat := 2 ^ 11
  maxAccPublicLibraries : Nat := 256
  deferOutQueueSizeLimit : Nat := 256
  maxMsgExtraCurrencies : Nat := 2
  maxAccFixedPrefixLength : Nat := 8
  accStateCellsForStorageDict : Nat := 26
  maxTransactionLibraryLoads : Option Nat := none
  maxTotalMsgBits : Nat := 2 ^ 21 * 5 / 2
  maxTotalMsgCells : Nat := 2 ^ 13 * 5 / 2

/-- The configuration: the dictionary and what C++ unpacks from it. -/
structure Config where
  root : Cell
  /-- parameter 0 -/
  configAddr : BitString
  /-- parameter 8 (`capabilities#c4`), 0 if absent -/
  globalVersion : Nat
  capabilities : Nat
  /-- parameter 31: the fundamental smart contracts (`HashmapE 256 True`) -/
  specialSmc : Option Cell
  /-- parameter 12 (`WorkchainDescr` dictionary), for the destinations of outbound messages -/
  workchains : Option Cell

namespace Config

/-- The cell of parameter `n` (C++ `get_config_param`: the reference stored in the dictionary). -/
def param (cfg : Config) (n : Nat) : Option Cell := do
  let v ← dictGet (some cfg.root) (natToBits n 32)
  if v.haveRefs 1 then some v.cell.refs[v.refPos]! else none

/-- `decode_config` and `Config::unpack` (`needWorkchainInfo | needSpecialSmc | needCapabilities`):
parameter 0 of 256 bits; parameter 8 read exactly if present. -/
def decode (root : Cell) : Option Config := do
  let base : Config := { root, configAddr := #[], globalVersion := 0, capabilities := 0, specialSmc := none,
                         workchains := none }
  let p0 ← base.param 0
  if p0.bits.size != 256 || p0.refs.size != 0 then none
  let (gv, caps) ←
    match base.param 8 with
    | none => some (0, 0)
    | some c =>
        Reader.runExact (do
          if (← Reader.uint 8) != 0xc4 then Reader.fail
          return (← Reader.uint 32, ← Reader.uint 64)) c
  let special := (base.param 31).bind fun c =>
    -- `vm::Dictionary(load_cell_slice_ref(param), 256)`: the HashmapE in the parameter's cell
    Reader.run Reader.hashmapE c |>.join
  let wcs := (base.param 12).bind fun c => Reader.run Reader.hashmapE c |>.join
  return { base with configAddr := p0.bits, globalVersion := gv, capabilities := caps, specialSmc := special,
                     workchains := wcs }

/-- `Config::get_storage_prices`: every entry of parameter 18 in key order, `utime_since` equal to
its key. -/
def storagePrices (cfg : Config) : Option (Array StoragePrices) := do
  let c ← cfg.param 18
  let entries ← dictEntries (some c) 32
  entries.mapM fun (key, s) => do
    let (p, _) ← (do
        if (← Reader.uint 8) != 0xcc then Reader.fail
        return ({ validSince := ← Reader.uint 32, bitPrice := ← Reader.uint 64, cellPrice := ← Reader.uint 64,
                  mcBitPrice := ← Reader.uint 64, mcCellPrice := ← Reader.uint 64 } : StoragePrices)) s
    if p.validSince != bitsToNat key then none
    return p

/-- `ComputePhaseConfig::parse_GasLimitsPrices` of parameter 20 (masterchain) or 21. -/
def gasPrices (cfg : Config) (mc : Bool) : Option GasPrices := do
  let c ← cfg.param (if mc then 20 else 21)
  let body (flatLimit flatPrice : Nat) : Reader GasPrices := do
    let tag ← Reader.uint 8
    if tag == 0xde then
      let gasPrice ← Reader.uint 64
      let gasLimit ← Reader.uint 64
      let special ← Reader.uint 64
      let credit ← Reader.uint 64
      let _ ← Reader.uint 64
      let freeze ← Reader.uint 64
      let delete ← Reader.uint 64
      return { gasPrice, gasLimit, specialGasLimit := special, gasCredit := credit, freezeDueLimit := freeze,
               deleteDueLimit := delete, flatGasLimit := flatLimit, flatGasPrice := flatPrice }
    else if tag == 0xdd then
      let gasPrice ← Reader.uint 64
      let gasLimit ← Reader.uint 64
      let credit ← Reader.uint 64
      let _ ← Reader.uint 64
      let freeze ← Reader.uint 64
      let delete ← Reader.uint 64
      return { gasPrice, gasLimit, specialGasLimit := gasLimit, gasCredit := credit, freezeDueLimit := freeze,
               deleteDueLimit := delete, flatGasLimit := flatLimit, flatGasPrice := flatPrice }
    else Reader.fail
  let flat : Reader GasPrices := do
    if (← Reader.uint 8) != 0xd1 then Reader.fail
    let fl ← Reader.uint 64
    let fp ← Reader.uint 64
    body fl fp
  -- C++ tries `gas_flat_pfx` first (csr_unpack, exact), then the record without it
  match Reader.runExact flat c with
  | some g => some g
  | none => Reader.runExact (body 0 0) c

/-- `MsgForwardPrices` of parameter 24 (masterchain) or 25 (`tlb::unpack_cell`, exact). -/
def msgPrices (cfg : Config) (mc : Bool) : Option MsgPrices := do
  let c ← cfg.param (if mc then 24 else 25)
  Reader.runExact (do
    if (← Reader.uint 8) != 0xea then Reader.fail
    return { lumpPrice := ← Reader.uint 64, bitPrice := ← Reader.uint 64, cellPrice := ← Reader.uint 64,
             ihrPriceFactor := ← Reader.uint 32, firstFrac := ← Reader.uint 16, nextFrac := ← Reader.uint 16 }) c

/-- `Config::get_size_limits_config` (parameter 43, `size_limits_config` v1, v2, v3; defaults if
absent; `none` if present and invalid). -/
def sizeLimits (cfg : Config) : Option SizeLimits :=
  match cfg.param 43 with
  | none => some {}
  | some c =>
      let v1 (l : SizeLimits) : Reader SizeLimits := do
        return { l with maxMsgBits := ← Reader.uint 32, maxMsgCells := ← Reader.uint 32,
                        maxLibraryCells := ← Reader.uint 32, maxVmDataDepth := ← Reader.uint 16,
                        maxExtMsgSize := ← Reader.uint 32, maxExtMsgDepth := ← Reader.uint 16 }
      let v2 (l : SizeLimits) : Reader SizeLimits := do
        let l ← v1 l
        return { l with maxAccStateCells := ← Reader.uint 32, maxMcAccStateCells := ← Reader.uint 32,
                        maxAccPublicLibraries := ← Reader.uint 32, deferOutQueueSizeLimit := ← Reader.uint 32,
                        maxMsgExtraCurrencies := ← Reader.uint 32, maxAccFixedPrefixLength := ← Reader.uint 8,
                        accStateCellsForStorageDict := ← Reader.uint 32,
                        maxTransactionLibraryLoads := ← Reader.maybe (Reader.uint 32) }
      let tagged (t : Nat) (r : Reader SizeLimits) : Reader SizeLimits := do
        if (← Reader.uint 8) != t then Reader.fail
        r
      match Reader.runExact (tagged 1 (v1 {})) c with
      | some l => some l
      | none =>
          match Reader.runExact (tagged 2 (v2 {})) c with
          | some l => some l
          | none => Reader.runExact (tagged 3 (do
              let l ← v2 {}
              return { l with maxTotalMsgBits := ← Reader.uint 32, maxTotalMsgCells := ← Reader.uint 32 })) c

/-- `Config::get_suspended_addresses`: the dictionary (`HashmapE 288 Unit`) of parameter 44 while
`suspended_until > now`. -/
def suspendedAddresses (cfg : Config) (now : Nat) : Option Cell := do
  let c ← cfg.param 44
  let (addrs, untilTime) ← Reader.runExact (do
    if (← Reader.uint 8) != 0 then Reader.fail
    return (← Reader.hashmapE, ← Reader.uint 32)) c
  if untilTime ≤ now then none else addrs

/-- `Config::get_burning_config().blackhole_addr` (parameter 5). -/
def blackholeAddr (cfg : Config) : Option BitString := do
  let c ← cfg.param 5
  let (addr, _) ← Reader.runExact (do
    if (← Reader.uint 8) != 1 then Reader.fail
    let a ← Reader.maybe (Reader.bits 256)
    let num ← Reader.uint 32
    let denom ← Reader.uint 32
    if num > denom ∨ denom < 1 then Reader.fail
    return (a, num)) c
  addr

/-- `Config::get_precompiled_contracts_config().list` (parameter 45). -/
def precompiledList (cfg : Config) : Option Cell := do
  let c ← cfg.param 45
  let l ← Reader.runExact (do
    if (← Reader.uint 8) != 0xc0 then Reader.fail
    Reader.hashmapE) c
  l

/-- `Config::is_special_smartcontract`: in parameter 31 or the configuration address. -/
def isSpecialSmc (cfg : Config) (addr : BitString) : Bool :=
  (dictGet cfg.specialSmc addr).isSome || addr == cfg.configAddr

/-- `Config::has_capability`. -/
def hasCapability (cfg : Config) (cap : Nat) : Bool := cfg.capabilities &&& cap != 0

end Config

end TvmLean.Tx

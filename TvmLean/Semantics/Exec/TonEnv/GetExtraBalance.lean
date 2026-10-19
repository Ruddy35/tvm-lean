import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.TonEnv.GetParamAliases

namespace TvmLean

/-- A cell load of a cheap GETEXTRABALANCE call (C++ `LocalVmState` in
`exec_get_extra_currency_balance`): the cell is registered as loaded (`register_cell_load_free`),
its price (new 100, reloaded 25) is charged up to what is left of the call's cap `remaining`, and
once the cap is used up the rest is counted as free gas (`consume_free_gas`). Returns the new
`remaining`. -/
def VM.registerCellLoadCheap (c : Cell) (remaining : Int) : VM Int := do
  let st ← get
  let h : Array UInt8 := Cell.hashBytes c
  let seen : Bool := st.loadedCells.any (fun x => x == h)
  if !seen then
    set { st with loadedCells := st.loadedCells.push h }
  let gas : Int := if seen then cellReloadGasPrice else cellLoadGasPrice
  let consumed : Int := min gas remaining
  VM.consumeGas consumed
  let remaining' := remaining - consumed
  if remaining' = 0 then
    modify fun st => { st with freeGasConsumed := st.freeGasConsumed + (gas - consumed) }
  return remaining'

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetExtraBalance (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getExtraBalance =>
      -- Mirrors C++ `exec_get_extra_currency_balance` (tonops.cpp).
      let id : Nat ← VM.popNatUpTo ((1 <<< 32) - 1)

      -- Balance tuple `c7[0][7]`; `tuple_index` raises range_chk for a missing entry.
      VM.pushC7Param 7
      let balanceVal ← VM.pop
      let balanceTuple : Array Value ←
        match balanceVal with
        | .tuple t => pure t
        | _ => throw .typeChk

      -- dict_root := balance[1]
      let dictRootVal : Value ←
        if 1 < balanceTuple.size then pure balanceTuple[1]! else throw .rangeChk
      let dictRoot? : Option Cell ←
        match dictRootVal with
        | .cell c => pure (some c)
        | .null => pure none
        | _ => throw .typeChk

      -- `register_get_extra_balance_call`: the first `get_extra_balance_cheap_count` calls are cheap.
      modify fun st => { st with getExtraBalanceCounter := st.getExtraBalanceCounter + 1 }
      let cheap : Bool := (← get).getExtraBalanceCounter ≤ getExtraBalanceCheapCount
      let chargeLoads (cells : Array Cell) : VM Unit := do
        if cheap then
          let mut remaining : Int := getExtraBalanceCheapMaxGasPrice
          for c in cells do
            remaining ← VM.registerCellLoadCheap c remaining
        else
          for c in cells do
            VM.registerCellLoad c

      let keyBits : BitString := natToBits id 32
      match dictLookupWithCells dictRoot? keyBits with
      | .error e =>
          -- the cells loaded before the error are charged
          chargeLoads (dictLookupVisitedCells dictRoot? keyBits)
          throw e
      | .ok (none, loaded) =>
          chargeLoads loaded
          VM.pushSmallInt 0
      | .ok (some cs, loaded) =>
          chargeLoads loaded
          -- Parse `VarUInteger 32`-like: len_bits=5, unsigned, quiet=false.
          let (lenBytes, s1) ← cs.takeBitsAsNatCellUnd 5
          let dataBits : Nat := lenBytes * 8
          let (n, _s2) ← s1.takeBitsAsNatCellUnd dataBits
          VM.pushIntQuiet (.num (Int.ofNat n)) false
  | _ => next

end TvmLean

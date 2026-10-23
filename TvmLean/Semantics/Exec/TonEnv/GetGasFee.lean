import TvmLean.Semantics.Exec.Common

namespace TvmLean

/-- C++ `operator+(RefInt256 x, long long y)` (refint.cpp:36-39) on a normalized `x` (its 52-bit digits
in [-2^51, 2^51)): `add_tiny` adds `y` to the lowest digit `d0` in `long long` (bigint.hpp:518-521),
then `normalize` carries from it, adding 2^51 to it again in `long long` (bigint.hpp:706-730). Both
wrap around (`int64Wrap`): the sum is exact unless `d0 + y` or that plus 2^51 leaves 64 bits, e.g. a
`y` near 2^63 and a positive `d0`, where it is 2^64 less. `x - y` (`operator-`, 51-54) is `x + (-y)`,
the negation in `long long`. -/
def refIntAddLong (x y : Int) : Int :=
  let d0 : Int := (x + 2 ^ 51) % 2 ^ 52 - 2 ^ 51
  x - d0 + int64Wrap (int64Wrap (d0 + y) + 2 ^ 51) - 2 ^ 51

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetGasFee (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getGasFee =>
      -- Matches C++ `exec_get_gas_fee` / `GasLimitsPrices::compute_gas_price` (tonops.cpp, mc-config.h).
      -- Stack: ... gas_used is_masterchain -- ... gas_fee
      -- C++: `check_underflow(global_version >= 9 ? 2 : 0)` before any operand is popped
      if (← get).globalVersion ≥ 9 then
        VM.checkUnderflow 2
      let isMasterchain ← VM.popBool
      let max63 : Nat := (1 <<< 63) - 1
      let gasUsed ← VM.popNatUpTo max63
      let (gasPrice, flatGasLimit, flatGasPrice) ← VM.getGasPrices isMasterchain
      -- `compute_gas_price` (mc-config.h:363-367): within the flat limit the flat price whole
      -- (`td::make_refint`); above it plus the flat price as `long long` (negative from 2^63 on), by
      -- `operator+(RefInt256, long long)` (`refIntAddLong`)
      let fee : Int :=
        if gasUsed ≤ flatGasLimit then
          Int.ofNat flatGasPrice
        else
          let varPart : Int := Int.ofNat gasPrice * Int.ofNat (gasUsed - flatGasLimit);
          refIntAddLong (ceilDivPow2 varPart 16) (int64Wrap (Int.ofNat flatGasPrice))
      VM.pushIntQuiet (.num fee) false
  | _ => next

end TvmLean

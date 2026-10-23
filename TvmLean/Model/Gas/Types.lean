import TvmLean.Model.Stack.Stack
import TvmLean.Model.Cell.Cell

namespace TvmLean

structure CallFrame where
  savedStack : Stack
  retArgs : Int
  deriving Repr

def CallFrame.identity : CallFrame := { savedStack := #[], retArgs := -1 }

structure GasLimits where
  gasMax : Int
  gasLimit : Int
  gasCredit : Int
  gasRemaining : Int
  gasBase : Int
  deriving Repr

def GasLimits.infty : Int := (Int.ofNat (1 <<< 63)) - 1

def GasLimits.default : GasLimits :=
  { gasMax := GasLimits.infty
    gasLimit := GasLimits.infty
    gasCredit := 0
    gasRemaining := GasLimits.infty
    gasBase := GasLimits.infty }

def GasLimits.ofLimit (limit : Int) : GasLimits :=
  { gasMax := GasLimits.infty
    gasLimit := limit
    gasCredit := 0
    gasRemaining := limit
    gasBase := limit }

def GasLimits.ofLimits (limit max credit : Int) : GasLimits :=
  let base : Int := limit + credit
  { gasMax := max
    gasLimit := limit
    gasCredit := credit
    gasRemaining := base
    gasBase := base }

/-- C++ `long long` of an integer: two's complement, the integer modulo 2^64 in [-2^63, 2^63). -/
def int64Wrap (x : Int) : Int := (x + 2 ^ 63) % 2 ^ 64 - 2 ^ 63

/-! C++ keeps the gas in `long long` (`GasLimits`, crypto/vm/vm.h:34-80): the constructor adds the limit
and the credit (vm.h:43), `consume` and `try_consume` subtract (57, 61), `change_base` adds the
difference of the bases (51), `gas_consumed` subtracts (47). Under limits of 2^63 or so (a
configuration's gas limits as `long long`, transaction.cpp:1938, 1955) these leave the range of
`long long`, which C++ does not check (signed overflow; the reference build wraps around). The model
keeps the exact sums in `gasRemaining` and `gasBase`, which C++ holds modulo 2^64 (`gas_base` is set
only to values in range), and reads them as C++ does: `GasLimits.remaining` (`gas_remaining`, which
every gas check compares with 0) and `GasLimits.gasConsumed`. -/

/-- C++ `gas_remaining` (`long long`): the exact gas left, `int64Wrap`. -/
def GasLimits.remaining (g : GasLimits) : Int :=
  int64Wrap g.gasRemaining

/-- C++ `gas_consumed()` (vm.h:46-48): `gas_base - gas_remaining` in `long long`. -/
def GasLimits.gasConsumed (g : GasLimits) : Int :=
  int64Wrap (g.gasBase - g.gasRemaining)

def GasLimits.changeBase (g : GasLimits) (newBase : Int) : GasLimits :=
  { g with gasRemaining := g.gasRemaining + (newBase - g.gasBase), gasBase := newBase }

def GasLimits.changeLimit (g : GasLimits) (newLimit : Int) : GasLimits :=
  let limit0 : Int := if newLimit < 0 then 0 else newLimit
  let limit : Int := if limit0 > g.gasMax then g.gasMax else limit0
  let g' : GasLimits := { g with gasCredit := 0, gasLimit := limit }
  g'.changeBase limit

def GasLimits.consume (g : GasLimits) (amount : Int) : GasLimits :=
  { g with gasRemaining := g.gasRemaining - amount }

structure CommittedState where
  c4 : Cell
  c5 : Cell
  committed : Bool
  deriving Repr

def CommittedState.empty : CommittedState :=
  { c4 := Cell.empty, c5 := Cell.empty, committed := false }

end TvmLean

import TvmLean.Proofs.Fast.Hash
import TvmLean.Proofs.Fast.Sha512
import TvmLean.Proofs.Fast.Dispatch
import TvmLean.Semantics

/-!
# The fast twins of the VM

The flattened instruction dispatch (`execInstrFast`, `TvmLean/Proofs/Fast/Dispatch.lean`) and the
twins of `VmState.run` and `VmState.step` with every fast form of `TvmLean/Proofs/Fast/` (bits,
bytes, SHA-256, SHA-512, the cell hash, the dispatch), compiled once here: `fast_decide` on a goal
about a run finds them instead of making them again.

`VmState.run_eq_fast : VmState.run = TvmLean.Fast.Twin.TvmLean.VmState.run` (the twin's equality
under a readable name).
-/

namespace TvmLean

set_option Elab.async false

fast_dispatch TvmLean.execInstr

fast_twin TvmLean.VmState.run TvmLean.VmState.step

/-- The twin of `VmState.run`: the same function, evaluated with the fast forms. -/
theorem VmState.run_eq_fast : @VmState.run = @TvmLean.Fast.Twin.TvmLean.VmState.run :=
  TvmLean.Fast.Twin.TvmLean.VmState.run.eq_twin

end TvmLean

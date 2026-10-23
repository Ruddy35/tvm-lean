import Lean

/-!
# Checking an invariant over all transactions: the `simp` sets others add to

The attributes of the `simp` lemmas that `ran_case` (TvmLean/Proofs/Check/Tactic.lean) uses besides
its own, which modules imported after it and invariants' files add to:

* `check_close`: lemmas and definitions to unfold when the data a path leaves is checked against the
  invariant, not during the run (an invariant's file, `tools/contract-check`'s `Inv.lean`: e.g. the
  definition that writes the data as a cell, `Data.encode`, whose reads the run takes from lemmas
  about it, unfolded at the end so that the cell the code built is compared with it);
* `check_run_simp`: lemmas of every step of the run (`check_step`, `check_step_simp`), e.g.
  TvmLean/Proofs/Check/Framed.lean's exception that ends the run, kept under a name.
-/

register_simp_attr check_close

register_simp_attr check_run_simp

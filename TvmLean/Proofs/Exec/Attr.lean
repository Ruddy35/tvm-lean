import Lean

/-!
# Simp sets of symbolic execution

Declared in a module of their own, as attributes must be, so that the lemma modules of
`Proofs/Exec` can tag their lemmas.

* `vm_run`: the runs of the VM monad and of its primitives on a state (`Proofs/Exec/VM.lean`),
  and the lemmas that compute with the stack (`Array.push` forms).
* `vm_spec`: the specifications of instructions, `(execInstr i).run st = ...`
  (`Proofs/Exec/Spec/*.lean`).
-/

/-- The runs of the VM monad and of its primitives on a state (`Proofs/Exec/VM.lean`). -/
register_simp_attr vm_run

/-- The specifications of instructions (`Proofs/Exec/Spec/*.lean`). -/
register_simp_attr vm_spec

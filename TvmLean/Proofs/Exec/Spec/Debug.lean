import TvmLean.Proofs.Exec.Eval

/-!
# Specifications: the debug instructions

In the format of `Proofs/Exec/Spec/Stack.lean`. `DUMPSTK`, `STRDUMP`, `DUMP`, `DEBUG`, `DEBUG_1`,
`DEBUG_2`, `DEBUGSTR` (C++ debugops.cpp:36-164: `exec_dummy_debug`, `exec_dummy_debug_str`, and
`exec_dump_stack`, `exec_dump_value`, `exec_dump_string`, which only log, when the VM's debug output
is on) change nothing.
-/

namespace TvmLean.Spec

/-- The debug instructions (C++ debugops.cpp) change nothing. -/
@[vm_spec] theorem debugOp (st : VmState) (op : DebugInstr) :
    ExceptT.run (execInstr (.debugOp op)) st = (.ok (), st) := by
  cases op <;> vm_simp

end TvmLean.Spec

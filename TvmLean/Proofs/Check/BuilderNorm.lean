import TvmLean.Proofs.Check.Framed

/-!
# Checking an invariant over all transactions: builders as structure instances

The specifications of the store instructions leave a builder in two forms: `b.storeBits bs` (`STU`,
`STGRAMS`, ...) and `{ bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }` (`STSLICE`, `STREF`,
`STB`, ...). On a builder of both, simp reduces the projections of the structure instances and not
those of `storeBits`, and a congruence of an `if` it rewrites is checked by unification between the
two forms of the same builder, which unfolds the bits the builder stores (`natToBits` as
`Array.ofFn`): in the jetton wallet the step of `STSLICER` after `STGRAMS` did not end within any
budget (`check.stepHeartbeats` 400000 or 1600000; with the profiler, the unification of the
congruence's hypothesis took the whole budget). The lemmas here, steps of every run
(`check_run_simp`), write every builder as a structure instance: `storeBits` and `Builder.empty`
unfolded, so that the projections reduce and both sides of such a unification are the same term.
At the end of a path the references a run pushed are written as an array literal (`#[a].push b` as
`#[a, b]`, `check_close`), the form of the references of an invariant's data.
-/

namespace TvmLean.Check

/-- `storeBits` as the structure instance it builds. -/
@[check_run_simp] theorem storeBits_mk (b : Builder) (bs : BitString) :
    b.storeBits bs = { bits := b.bits ++ bs, refs := b.refs } := rfl

/-- The empty builder as a structure instance. -/
@[check_run_simp] theorem builderEmpty_mk : Builder.empty = { bits := #[], refs := #[] } := rfl

-- the references a run pushed onto a builder, at the end of a path an array literal
-- (`#[a].push b = #[a, b]`), as the invariant writes the references of the data
attribute [check_close] List.push_toArray List.cons_append List.nil_append

end TvmLean.Check

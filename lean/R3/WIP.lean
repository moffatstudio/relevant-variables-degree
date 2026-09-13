import Mathlib
/-!
Scratch file.  **NOT imported by R3.lean**, so `lake build` never checks it.
Park unfinished proofs here with a comment saying exactly what failed, so the imported tree
is never left with an unproved placeholder.

Currently empty: everything attempted in task 18 landed in R3/Octahedron.lean and
R3/Final.lean.  The next job (PLAN_F11.md Step 0.2 and Step 1) starts from scratch here.

Benchmark result kept from this run, because it is counter-intuitive and cost an hour:
for an iff between two 8-fold disjunctions of equalities, e.g.
  `Edge p q r s u t ↔ Edge q p s r u t`
`tauto` closes it in seconds while `omega` exceeds 1000000 heartbeats.  Use `tauto` for the
two dihedral generators and `Iff.trans` for everything else; use `omega` only to *consume*
such disjunctions, after `clear * - <the few facts it needs>`.
-/
namespace R3WIP

end R3WIP

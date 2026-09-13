# Toolchain notes — delta = 0 lane (task 23, 2026-09-13)

* Nothing new broke this run; `R3/DeltaZero.lean` compiled first try (75 s) and again after
  each addition.  The general notes in `TOOLCHAIN_NOTES.md` all still hold.
* **Localising a global hypothesis is cheaper than refactoring the file that owns it.**
  `octahedron_closure_gen` takes `hall4 : ∀ w < n, mass n N w = 4`, which is false in
  delta = 0.  Rather than touch `Octahedron.lean` (owned by another lane), the body was
  copied into `DeltaZero.lean` with `hall4 w hw` replaced by six local `have m4_ : mass … = 4`
  facts, each supplied by a `Near` proof.  The copy needed no other change, so the two proofs
  stay in sync by inspection.
* The reason this works: every vertex whose mass the closure proof reads is within distance
  two of `v` in the support hypergraph, and the sixth vertex `e` (produced inside the proof by
  `link_sixth`) is a neighbour of `a`, itself a neighbour of `v`.  A predicate `Near` phrased
  on the *solution* rather than on the six internal vertices is what makes the statement
  usable from outside.
* `mem_tri_iff.mpr (Or.inl rfl)` etc. are the cheapest way to get `(tri x y z).testBit x`;
  a `by simp [mem_tri_iff]` costs heartbeats every time.
* Writing Lean files from a Bash heredoc halves backslashes; this run edited via a small
  `python -` script writing UTF-8 with explicit `\uXXXX` escapes for the Unicode tokens,
  which is reliable (see the `bash-heredoc-backslashes` note in the campaign memory).

## Rotation 2

* **`omega` in a large context costs ~20k heartbeats per call.**  `octa_v_triple` has five
  branches, each needing eight trivial `≠` side conditions; written as `(by omega)` with the
  five `LinkIs` hypotheses and an `Edge` in context, the theorem blew through 800000
  heartbeats.  Replacing every `by omega` by the explicit `Ne` term (`d4`, `Ne.symm d11`, …)
  from a destructured `Dist6` brought the whole file back to 70 s.  Rule for this lane:
  inside a proof with more than a handful of hypotheses, never call `omega` for a goal that
  a named hypothesis proves; keep `omega` for the genuinely combinatorial `Edge` case splits
  and put those in tiny standalone lemmas that start with `clear * - …`.
* `exact absurd h (by simp)` where `h : False` is a heartbeat sink (elaborates `absurd` with
  a metavariable); use `h.elim`.
* `rcases (h : x = a) with rfl` substitutes **`a := x`** here (the later-bound variable
  survives), so after the `rcases` refer to `x`, not to `a`.

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
* A python heredoc longer than ~100 lines fails in this shell ("unexpected EOF while looking
  for matching `''"), even with a quoted delimiter.  Write the Lean chunk to `C:\tmp\x.lean`
  with the Write tool, then splice it:
  `grep -v '^end R3$' R3/DeltaZero.lean > /c/tmp/dz.tmp && cat /c/tmp/x.lean >> /c/tmp/dz.tmp && cp /c/tmp/dz.tmp R3/DeltaZero.lean`
  (keep the chunk file ending in `end R3`, and `cp R3/DeltaZero.lean /c/tmp/dz.bak` first).
* `Finset.sum_nbij' i j hi hj left_inv right_inv h` leaves *unbeta-reduced* goals like
  `(fun S => S ^^^ U) ((fun S => S ^^^ U) S) = S`; open each with `show … ` before rewriting.
* `linear_combination h` is the cheap way to match a `mass_four` coefficient product against
  a differently-associated product of the same factors.

## Rotation 3

* **Refactor a `theorem` into a weaker-hypothesis version by editing only its header.**
  `octa_kill` destructured `Octa` into five links but used only four (`hLb'` was dead).
  Replacing the header and the `obtain`/`clear` lines turned it into `octa_kill4` with no
  change to the 150-line body, and `octa_kill` became a wrapper.  Cheap, and the diff is
  reviewable.  Grep the body for the dropped hypothesis first.
* **`rcases h with rfl` when both sides are theorem parameters is a trap.**  Which variable
  survives is not predictable from the source; `h ▸ hF` (rewriting the one hypothesis that
  mentions it) is shorter and always right.
* `Bool.eq_false_or_eq_true b : b = true ∨ b = false` — the *true* branch is first.  Prefer
  `by_cases hb : S.testBit v = true` and `simp only [Bool.not_eq_true] at hb` for the
  negative branch.
* To `#print axioms` a module that is not built (no `.olean`), append the `#print axioms`
  lines to a **copy** of the source placed in `R3/` and run `lake env lean` on the copy.
  Avoids `lake build` and its RAM.
* `rw [show tri a b c = tri d e f from by rw [h]; exact tri_ext (fun _ => by omega)]` is the
  cheap idiom for reordering a triple under a vertex equation `h`, and avoids `subst`.
* Symmetry-by-instantiation beats symmetry lemmas: `linkIs_rot` / `linkIs_rev` plus a
  permuted `Dist6` let the mirror of a kill be a one-line `exact`, with no new proof.

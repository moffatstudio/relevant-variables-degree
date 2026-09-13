# HANDOFF — Lean F(11), delta = 2 lane (task 27, rotation 2, 2026-09-13)

## State: `eleven_delta_two` is PROVED and GATED.  The case `delta = 2` is machine-checked.

`bash gate.sh` on 2026-09-13 reports **GATE: PASS**: `lake build` exit 0, laundering scan
clean, and all 153 listed theorems (including `R3.eleven_delta_two`) depend only on
`[propext, Classical.choice, Quot.sound]`.  `R3/LinkSix.lean` is unchanged from rotation 1.

## The shape of the finished proof

`eleven_delta_two` splits on whether a support set of size at most 1 exists.

* **No low set** -> `eleven_delta_two_quad` (rotation 1, already gated).
* **A low set** -> `delta_two_linear` makes it a single linear term `2 ^ l` with every other
  support set a triple.  Two sub-cases, both new in this rotation:
  * `l` different from `v` -> `eleven_delta_two_lin_four`;
  * `l = v` -> `eleven_delta_two_lin_six`.

## New shared infrastructure in `R3/DeltaTwo.lean`

- `one_linear_no_quad`, `one_linear_no_const`, `cubicAt_of_one_linear` — the one-linear-term
  analogues of the delta = 4 lane's `two_linear_*` lemmas.  Note that `CubicAt 11 N u` holds
  at every `u` other than `l`, which is what makes the whole `Octahedron` primed API usable
  in this case.
- `tri_link_absurd` — a triangle in the link of a cubic mass-4 vertex is impossible
  (a thin wrapper on `no_triangle_at'`).
- `common_sixth` — **the workhorse.**  If `o` carries the three faces of a triangle `a b c`
  and `a`, `b` are cubic mass-4 vertices, the 4-cycle links at `a` and at `b` are completed by
  the *same* sixth vertex `w`, and `w` then carries the whole triangle `a b c`.
- `tri_apex_common` — `common_sixth` plus `tri_link_absurd`: that `w` must be `v` or `l`.
- `supp_tri`, `tri_of_bit`, `tri_ne_of`, `tri_ne_bit`, `two_pow_ne_tri`, `tri_degen`,
  `pair_tri_xor` — bitmask bookkeeping.
- `other_nbr` — **degree two in the link of `v`.**  A cubic mass-4 vertex `u` carrying one
  face through `v` carries exactly one other.  Proved by `link_struct'` at `u` plus
  `edge_nbr`, with a `gen` helper applied to the four rotations of the 4-cycle via
  `edge_rot`, so the four cases are not written out four times.

## `eleven_delta_two_lin_four` (the linear vertex has mass 4)

`link_L4_of_linear` (reused from `R3/DeltaFour.lean`, hence the new `import R3.DeltaFour`)
gives `l` a triangle link `a b c`.  If `v` is one of `a b c` the case dies immediately from
`tri_apex_common`.  Otherwise the common sixth vertex is forced to be `v`, so the link of `v`
contains the triangle `abc`; the remaining three of its six link sets are shown to be pairs
xoring to zero (`mass_six`, `xor_two_pow_cancel6`, `pair_tri_xor`), hence a second triangle
`x y z` (`three_pairs_triangle`); `link_nbrs_of_v` shows `x y z` avoid `a b c` and `l`;
`tri_apex_common` on `x y z` then forces its sixth vertex to be `l`, contradicting the
triangle link of `l`.

## `eleven_delta_two_lin_six` (the linear vertex is `v`)

The link of `v` is the empty set plus five faces.  Start from any face at `v`; `other_nbr`
gives each of its two endpoints a second neighbour; `link_sixth'` at both endpoints produces
the same sixth vertex `w` (the `common_sixth` argument).  If the two second neighbours
coincide, the link at `w` has a triangle (`tri_link_absurd`).  Otherwise
`link_of_three_faces'` makes the link at `w` a 4-cycle, whence a fourth face at `v`.  Those
four faces live on four vertices; the fifth face must avoid all four, and then `other_nbr` at
one of its endpoints produces a second face through that endpoint with nowhere to go.
This replaces the hand proof's `five_pairs_cycle`: the 5-cycle is never built, and degree two
in the link comes straight from `other_nbr`.

## Files

- `R3/DeltaTwo.lean` — all of the above, now about 1100 lines.  Its imports gained
  `R3.DeltaFour`; `R3.lean` already lists `DeltaFour` before `DeltaTwo`, so `R3.lean` needed
  no edit.
- Two declarations in `R3/DeltaTwo.lean` were renamed to `pair_lt_dtwo` and
  `card_quad_eq_dtwo`.  The delta = 0 lane added declarations of the original names to
  `R3/DeltaZero.lean`, and `R3.lean` imports both files, which broke the build.  Neither name
  was in the gate list, so nothing else changed.
- `R3/LinkSix.lean` — unchanged.
- `R3/WIP_delta2.lean` — still contains no proofs.
- `gate.sh` — the rotation-1 names plus the 18 new ones, listed in `INTEGRATE_delta2.md`.

## Next step for whoever picks this up

Nothing is outstanding in this lane.  The remaining work for R3 = 10 is the delta = 0 lane
and the top-level assembly, which can consume

```
theorem eleven_delta_two {N : ℕ → ℤ} (hsol : IsSol 11 N) {v : ℕ} (hv : v < 11)
    (h6 : mass 11 N v = 6) (hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4) : False
```

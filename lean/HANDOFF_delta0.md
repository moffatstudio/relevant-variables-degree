# HANDOFF — delta = 0 lane (task 23, rotation 1, 2026-09-13)

## State: GREEN but PARTIAL.  `eleven_delta_zero` is NOT proved.

All of `lean/R3/DeltaZero.lean` is accepted by `lake env lean R3/DeltaZero.lean` (clean,
~75 s, no `sorry`, no `native_decide`).  It is not yet imported by `R3.lean` — see
`INTEGRATE_delta0.md`.

## Proved this run

1. **Distance in the support hypergraph.**  `Nbr n N v w` (v, w lie in a common support set),
   `Near n N v w` (distance at most two), `near_self`, `nbr_tri_snd`, `nbr_tri_thd`.
2. **`closure_near`** — the localisation of `octahedron_closure_gen`.  The global hypothesis
   `∀ w < n, mass n N w = 4`, which is unusable at delta = 0 (the masses are (8,4^10) or
   (6,6,4^9)), is replaced by `∀ w < n, Near n N v w → mass n N w = 4`.  This works because
   the proof of `octahedron_closure_gen` reads the mass only at `v`, at the four link-cycle
   vertices `a b c d` (neighbours of `v`) and at the sixth vertex `e` (a neighbour of `a`).
   The body is the body of `octahedron_closure_gen` with six explicit `mass … = 4` facts.
3. **`closure_kills`** — step (a) of the captain's plan: `IsSol n N`, `Cubic n N`, `6 < n`,
   and everything within distance two of some `v` of mass 4 gives `False`
   (`closure_near` + `no_crossing_split`, the `F_twelve` tail pattern with `range n`).
4. **`delta_zero_residual`** / **`eleven_delta_zero_residual`** — the contrapositive: in a
   cubic solution with `n > 6` **every** vertex has an exceptional vertex (mass ≠ 4) within
   distance two.  At `n = 11` there are at most two exceptional vertices
   (`card_mass_ne_four_le_two`), so the whole support sits in their distance-2 neighbourhood.
5. **Pseudo-manifold counting** (step (c) groundwork): `edge_second`, `edge_not_three` (a
   4-cycle vertex has a second neighbour, and never three), and their solution-level forms
   **`pair_second`** and **`pair_not_three`**: if `mass x = 4` then the pair `{x, v}` lies in
   exactly 0 or 2 support triples.  Note the consequence worth exploiting: at n = 11,
   delta = 0, the ONLY pair that can fail "0 or 2" is the pair of the two mass-6 vertices,
   because every other pair has a mass-4 endpoint.  In the (8,4^10) sub-case every pair is
   0-or-2, so `link(v)` at the mass-8 vertex is 2-regular — the hand proof's first step,
   now available in Lean.

## In progress / not started

`eleven_delta_zero : IsSol 11 N → Cubic 11 N → False`.  Nothing of it is written.
The residual after step (a) is exactly the hand proof's sub-cases; `R3_equals_10.md` kills
them with Euler characteristic (Fact T), which the plan forbids formalising.

## Next three steps (recommended, in order)

1. **Degree bookkeeping in Lean.**  Prove at n = 11 under `Cubic`: `∑_v mass v = 48`
   (`sum_mass` with every support set of card 3) and hence the mass multiset is `(8,4^10)`
   or `(6,6,4^9)`.  `bookkeeping`, `mass_cases`, `card_mass_ne_four_le_two` already give
   most of it; what is missing is the explicit two-way split.  Cheap, ~2-3 h, and every
   later step branches on it.
2. **(8,4^10): 2-regularity and the C_4 ∪ C_4 forcing.**  With `pair_not_three` the link of
   the mass-8 vertex `u` is 2-regular on its 8 edges.  Then classify: C_8, C_3 ∪ C_5,
   C_4 ∪ C_4.  This is the m = 8 analogue of `four_pairs_cycle`; reuse `card_sum_even` and
   the `four_cover` trick of `DeltaFour.lean` rather than a raw case split.  Expensive
   (10-15 h) and it is the gateway to the whole sub-case.
3. **Kill C_4 ∪ C_4 by a finite sign check.**  Once the 16-triple structure is forced up to
   relabelling, the contradiction is `CondII` at a well-chosen `U`; see
   `referee/check_glued_octahedra.py` for which `U` suffice.  Keep the `decide` instance
   tiny — evaluate `CondII` at ONE `U` per sign pattern rather than enumerating 2^16.
   Completeness of the structure list must come from step 2, never from `search/`.

## Honest estimate
30-40 agent-hours remain for `eleven_delta_zero`, and the C_8 and (6,6,4^9) branches still
have no topology-free paper proof.  Ask the referee lane for those two before spending Lean
time on them; the C_4 ∪ C_4 branch is the only one with a ready non-topological argument.

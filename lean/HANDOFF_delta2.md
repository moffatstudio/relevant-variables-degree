# HANDOFF — Lean F(11), delta = 2 lane (task 22, rotation 1, 2026-09-13)

## State: partial.  Two of the three pieces of the case are machine-checked.

`eleven_delta_two` is NOT proved.  Everything below was accepted by
`lake env lean R3/<file>.lean` in this run (no `sorry`, no `native_decide`).
Integration lines for `R3.lean` and `gate.sh` are in `INTEGRATE_delta2.md`.
A full `lake build` / `gate.sh` has NOT been run by this lane (the captain owns those).

## Proved this run

### `R3/LinkSix.lean` — Lemma 2(b), the mass-6 link
- `mass_six_pm` — **no ±2 coefficient at a mass-6 vertex.**  This is the "Lemma 1, second
  half" step the referee brute force (`round2b_out_lemma1.txt`) confirms.  Proof: a `{±2,±1,±1}`
  link forces the two unit terms to agree at every point, so `chi_{T1 Δ T2} ≡ 1`, so `T1 = T2`.
- `mass_six_card` — the support at a mass-6 vertex has exactly six sets.
- `mass_six` — the six sets xor to `0` and their coefficients have product `-1`.
- `mass_six_link` — the packaged form (mirrors `mass_four_link`): six distinct sets, each
  `±1`, size ≤ 3, containing `v`, with link sets of size ≤ 2 avoiding `v` and xor `0`.
- Reusable helpers: `card_eq_six`, `six_pm_sum`, `two_one_one_agree`, `xor_two_pow_cancel6`,
  `sq_ne_two`, `sq_eq_one_of`.

### `R3/DeltaTwo.lean` — the case itself
- `delta_two_weight` — from `bookkeeping`: one vertex of mass 6 and ten of mass 4 forces the
  lower-order weight `∑_S (3 - |S|) n_S²` to be exactly `2`.
- `three_quadratics_absurd` — three distinct size-2 support sets already weigh `3 > 2`.
- `two_quadratics_at` — **the L3 step.**  With no linear or constant term, a mass-4 vertex
  on a quadratic lies on two distinct quadratics.  (`link_types` is used here for the first
  time in the project: L1/L4 die because a singleton is not a pair, L2 dies because it would
  need a linear term, L3 supplies the two singletons.)
- `exists_quadratic`, `quad_three_of`.
- **`eleven_delta_two_quad`** — the "two unit quadratics" branch of `delta = 2` is impossible.
- `delta_two_linear` — in the other branch the lower-order term is a single **linear** term
  `L` of size 1 with coefficient `±1`, and every other support set is a cubic.
- General helper `four_distinct_exhaust` (four distinct values drawn from a four-element list
  exhaust it; proved by `Finset.eq_of_subset_of_card_le`, not by a 256-way `rcases`).

## What remains: the "one linear term" branch

The top-level theorem should be assembled as

```
theorem eleven_delta_two {N : ℕ → ℤ} (hsol : IsSol 11 N) {v : ℕ} (hv : v < 11)
    (h6 : mass 11 N v = 6) (hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4) : False
```

by `by_cases hlow : ∃ S, S < 2 ^ 11 ∧ N S ≠ 0 ∧ card 11 S ≤ 1`.
* `hlow` false gives exactly the hypothesis `hnolin` of `eleven_delta_two_quad` — **done**.
* `hlow` true gives `delta_two_linear`, i.e. the linear term `L = 2 ^ l` — **outstanding**.

Hand proof (R3_equals_10.md, "Case delta = 2", first bullet) for the outstanding branch:
1. if `m_l = 4` its link is L4 (`∅` plus a triangle `abc`); two sub-cases (`v ∉ {a,b,c}` and
   `v = a`) each end in a mass-4 vertex whose C_4 link contains a triangle;
2. otherwise `l = v`, the mass-6 vertex, and `link(v) = ∅` plus **five pairs** with even
   degrees, i.e. a 5-cycle `a_1..a_5`; completing the C_4 link at each `a_k` gives a common
   sixth vertex `w` lying in five cubics, so `m_w = 5`, contradicting `mass_cases`.

### BLOCKER the captain must decide on (it affects the delta = 4 lane too)

The octahedron chain (`link_cycle`, `link_struct`, `link_sixth`, `link_of_three_faces`,
`no_triangle_at`, `closure_of_links`) takes the **global** hypothesis `Cubic n N`
(*every* support set has size 3).  That hypothesis is FALSE in both `delta = 2` and
`delta = 4`: there is always at least one lower-order term.  Two observations:

* `link_cycle` / `link_struct` / `link_sixth` / `link_of_three_faces` / `no_triangle_at` use
  cubicity only through `cubic_link_card_two hcub hv hS` with `hS ∈ supp n N v`, i.e. only for
  support sets **containing the vertex being read**.  They generalise verbatim to a per-vertex
  `CubicAt n N v := ∀ S, S < 2^n → N S ≠ 0 → S.testBit v = true → card n S = 3`.
* `closure_of_links` genuinely quantifies over *all* support sets (it calls
  `exists_tri_of_card_three` on an arbitrary `S`), so it needs either global cubicity or the
  weaker "every non-cubic support set avoids `A`".

Recommendation: the captain (or whoever owns `R3/Octahedron.lean`) replaces `Cubic n N` by
`CubicAt n N w` in the five link lemmas and adds the "non-cubic sets avoid `A`" variant of
`closure_of_links`.  It is a mechanical edit of one file, it unblocks *both* remaining cases,
and it cannot be done from this lane (I do not own `Octahedron.lean`).

## Next three steps for this lane
1. Get the `CubicAt` generalisation of the link chain (above) from the captain.
2. Prove `five_pairs_cycle`: five distinct pairs with xor `0` form a C_5.  Same technique as
   `four_pairs_cycle` in `R3/Cycle.lean` (`EvenDeg` + `cnt` + small `omega`s with
   `clear * -`); budget 5-8 h, it is the largest single piece left.  What supplies its xor
   hypothesis is `mass_six` at `v` (the six link sets are `∅` and the five pairs).
3. Assemble the two sub-cases of the linear branch and then `eleven_delta_two`.

Remaining-hours estimate for the linear branch: 10-14 h, of which 5-8 h is `five_pairs_cycle`
and 2 h is blocked on the `CubicAt` refactor.

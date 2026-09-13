# INTEGRATE — delta = 0 lane (task 26, rotation 2, 2026-09-13)

## File
`lean/R3/DeltaZero.lean` (971 lines, owned by the delta = 0 lane).  Imports `R3.Final` and
`R3.LinkTypes` only.  **No `sorry`, no `native_decide`, no `set_option maxHeartbeats`.**
Verified with `lake env lean R3/DeltaZero.lean` (clean, 70 s, warnings only: six unused
variables).  Nothing in `R3.lean` or `gate.sh` depends on it yet, so merging cannot break the
existing `F_twelve` gate.

## Line for `R3.lean`

    import R3.DeltaZero

## Headline results (new this rotation)

* `eleven_delta_zero_eight : IsSol 11 N → Cubic 11 N → v < 11 →
    (∀ w, w < 11 → w ≠ v → mass 11 N w = 4) → False`
  — the `(8, 4^10)` sub-case of `delta = 0` is **closed**.  (The mass of `v` is never used:
  the hypothesis is only "at most one exceptional vertex".)
* `eleven_delta_zero_reduce : IsSol 11 N → Cubic 11 N →
    ∃ v w, v < 11 ∧ w < 11 ∧ v ≠ w ∧ mass 11 N v = 6 ∧ mass 11 N w = 6 ∧
      ∀ z, z < 11 → z ≠ v → z ≠ w → mass 11 N z = 4`
  — `delta = 0` at `n = 11` forces the degree sequence `(6, 6, 4^9)`.  This is the residual
  goal for the next rotation; `eleven_delta_zero` follows from it alone.
* `octa_kill` — the engine.  Any octahedron `v, a, b, a', b', y` whose rim vertices
  `a, b, a'` and antipode `y` have mass 4 contradicts condition (ii) at the pair `{v, y}`.
  Replaces "Lemma A" of `DELTA0_TOPOLOGY_FREE.md` and is much stronger: no second
  octahedron, no fifth triple at `v`, and no hypothesis on `mass v` are needed.

## `#print axioms` list for `gate.sh` (all of them; the earlier nine are unchanged)

    R3.near_self            R3.closure_near          R3.closure_kills
    R3.delta_zero_residual  R3.edge_second           R3.edge_not_three
    R3.pair_second          R3.pair_not_three        R3.eleven_delta_zero_residual
    R3.supp_eq_quad         R3.no_fifth_supp         R3.tri_distinct
    R3.second_v_triple      R3.octa_half             R3.exists_fifth_supp
    R3.supp_tri_of_mem      R3.octa_eight            R3.octa_eight'
    R3.cubic_sum_mass       R3.eleven_degree_split   R3.octa_v_triple
    R3.condII_corr          R3.corr_bit_half         R3.tri_xor_pair
    R3.octa_kill            R3.eleven_delta_zero_eight
    R3.eleven_delta_zero_reduce

(`Nbr`, `Near`, `Octa`, `Dist6` are definitions, not theorems.)

## Name clashes to re-check at merge time
New top-level names in namespace `R3`: `Octa`, `Dist6`, `octa_half`, `octa_eight`,
`octa_eight'`, `octa_v_triple`, `octa_kill`, `linkIs_rot`, `link_v_nbrs`, `link_not_mem`,
`condII_corr`, `corr_bit_half`, `pair_eq_tri`, `pair_lt`, `tri_xor_pair`, `tri_ne_of_mem`,
`tri_mem_supp`, `tri_mem_supp2`, `tri_mem_supp3`, `tri_swap23`, `tri_distinct`, `sq_cases`,
`four_vals_ne_eight`, `pm_mul`, `eps_kill`, `card_quad_eq`, `card_pair_le`, `card_tri_le`,
`card_supp_le_mass`, `ne_of_testBit`, `tri_testBit_false`, `cubic_sum_mass`,
`eleven_degree_split`, `exists_fifth_supp`, `supp_tri_of_mem`, `supp_eq_quad`,
`no_fifth_supp`, `second_v_triple`.  None of these existed in `lean/R3/` at the start of the
run, but the delta = 2 and delta = 4 lanes edit in parallel — re-grep before merging.

## Note for the paper / referee lane
`octa_kill` is a **new and shorter argument than Lemma A** of `DELTA0_TOPOLOGY_FREE.md`, and
it should replace both Lemma A and the `(8, 4^10)` case analysis in the hand proof:

> Let `v-a-b-a'-b'-y` be an octahedron (the four triples `v a b, v a b', v a' b, v a' b'` and
> the four `y a b, y a b', y a' b, y a' b'`) inside a solution, with `a, b, a', y` of mass 4.
> Put `e_i = n_{v P_i} n_{y P_i}` for the four equatorial pairs `P_i`.  Condition (ii) at
> `U = {v, y}` reads `sum_i e_i = 0` (all other pairs `(S, S Δ U)` have a factor 0, because
> every support set containing `y` is one of the four `y`-triples).  But mass 4 at `a`, at
> `b` and at `a'` says the four coefficients at each of them multiply to `+1`, i.e.
> `e_1 e_2 = e_1 e_4 = e_3 e_4 = 1`, so all four `e_i` are equal and the sum is `±4`.

Any surface/Euler-characteristic step is gone from the `(8, 4^10)` branch.

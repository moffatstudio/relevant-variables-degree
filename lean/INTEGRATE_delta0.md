# INTEGRATE — delta = 0 lane (task 28, rotation 3, 2026-09-13)

## File
`lean/R3/DeltaZero.lean` (1388 lines, owned by the delta = 0 lane).  Imports `R3.Final` and
`R3.LinkTypes` only.  **No `sorry`, no `native_decide`, no `set_option maxHeartbeats`.**
Verified with `lake env lean R3/DeltaZero.lean` (clean, ~80 s, warnings only: six unused
variables).  Nothing in `R3.lean` or `gate.sh` depends on it yet, so merging cannot break the
existing `F_twelve` gate.

## Line for `R3.lean`

    import R3.DeltaZero

## Headline result

    theorem eleven_delta_zero {N : ℕ → ℤ} (hsol : IsSol 11 N) (hcub : Cubic 11 N) : False

**The `δ = 0` case of `F(11)` is closed**, both sub-cases.  `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`.

Supporting headline theorems (rotation 3):

* `apex_other` — a support triple `{v, a, b}` with `a, b` ordinary has the *other*
  exceptional vertex as its `octa_half` apex; returns both 4-cycle links.
* `no_exc_pair` — no support triple contains both exceptional vertices.
* `apex_gen` — the same at an arbitrary apex `x`: one of `{v,a,b}`, `{w,a,b}`, `{v,b,x}`,
  `{w,b,x}` is a support triple.
* `kill_pair` — a pair `{s, t}` lying in a triple with an exceptional vertex lies in exactly
  two triples, both through exceptional vertices.
* `kill_free_triple` — no support triple has all three vertices ordinary.
* `exists_free_set` — disjoint mass-6 supports use only 12 of the weight 16, so some support
  set avoids both exceptional vertices.
* `octa_kill4` / `Octa4` — `octa_kill` restated on four links (the link of `b'` is never
  used); `octa_kill` is now a wrapper.  `octa_kill4'` is its `a ↔ b` mirror.

## Full `#print axioms` list for `gate.sh`

    R3.near_self            R3.closure_near          R3.closure_kills
    R3.delta_zero_residual  R3.edge_second           R3.edge_not_three
    R3.pair_second          R3.pair_not_three        R3.eleven_delta_zero_residual
    R3.supp_eq_quad         R3.no_fifth_supp         R3.tri_distinct
    R3.second_v_triple      R3.octa_half             R3.exists_fifth_supp
    R3.supp_tri_of_mem      R3.octa_eight            R3.octa_eight'
    R3.cubic_sum_mass       R3.eleven_degree_split   R3.octa_v_triple
    R3.condII_corr          R3.corr_bit_half         R3.tri_xor_pair
    R3.corr_supp            R3.octa_kill4            R3.octa_kill
    R3.octa_kill4'          R3.linkIs_rev            R3.dist6_swap
    R3.eleven_delta_zero_eight                       R3.eleven_delta_zero_reduce
    R3.apex_other           R3.no_exc_pair           R3.apex_gen
    R3.kill_pair            R3.kill_free_triple      R3.exists_free_set
    R3.eleven_delta_zero

(`Nbr`, `Near`, `Octa`, `Octa4`, `Dist6` are definitions, not theorems.)

## Name clashes to re-check at merge time
New top-level names in namespace `R3` added this rotation: `Octa4`, `octa_kill4`,
`octa_kill4'`, `linkIs_rev`, `dist6_swap`, `apex_other`, `no_exc_pair`, `apex_gen`,
`kill_pair`, `kill_free_triple`, `exists_free_set`, `eleven_delta_zero`.  Earlier rotations
added `Octa`, `Dist6`, `octa_half`, `octa_eight`, `octa_eight'`, `octa_v_triple`, `octa_kill`,
`linkIs_rot`, `link_v_nbrs`, `link_not_mem`, `condII_corr`, `corr_bit_half`, `corr_supp`,
`pair_eq_tri`, `pair_lt`, `tri_xor_pair`, `tri_ne_of_mem`, `tri_mem_supp{,2,3}`, `tri_swap23`,
`tri_distinct`, `sq_cases`, `four_vals_ne_eight`, `pm_mul`, `eps_kill`, `card_quad_eq`,
`card_pair_le`, `card_tri_le`, `card_supp_le_mass`, `ne_of_testBit`, `tri_testBit_false`,
`cubic_sum_mass`, `eleven_degree_split`, `exists_fifth_supp`, `supp_tri_of_mem`,
`supp_eq_quad`, `no_fifth_supp`, `second_v_triple`.  The delta = 2 and delta = 4 lanes edit
in parallel — re-grep before merging.

## Note for the paper / referee lane
The `(6, 6, 4^9)` section of `DELTA0_TOPOLOGY_FREE.md` is superseded: see the numbered route
in `HANDOFF_delta0.md`.  No cycle classification, no bowtie case, no 8-set closure, no Euler
characteristic.  The referee's bowtie finding no longer applies, and the new argument has not
been refereed.

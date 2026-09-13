# HANDOFF — delta = 0 lane (task 26, rotation 2, 2026-09-13)

## State: GREEN.  `(8, 4^10)` is CLOSED.  Only `(6, 6, 4^9)` is left.

`lean/R3/DeltaZero.lean` is accepted by `lake env lean R3/DeltaZero.lean` (70 s, no `sorry`,
no `native_decide`, no raised heartbeat limit).  See `INTEGRATE_delta0.md` for the import
line, the theorem list and the `#print axioms` list.

`eleven_delta_zero` is NOT yet proved.  What remains is exactly:

    IsSol 11 N → Cubic 11 N → v, w the two mass-6 vertices, all other masses 4 → False

and `eleven_delta_zero_reduce` already hands you that hypothesis in that shape.

## Proved in rotation 2

1. **Mass-4 exhaustion toolkit** — `supp_eq_quad`, `no_fifth_supp`, `tri_distinct`,
   `second_v_triple`, `tri_mem_supp{,2,3}`, `tri_ne_of_mem`.
2. **`octa_half`** — Lemma Y in its local form: a support triple `{v, a, b}` with
   `mass a = mass b = 4` has a *shared apex* `y`, i.e. the links of `a` and of `b` are the
   4-cycles `b-v-b'-y` and `a-v-a'-y` with the same `y`.  (Proof: the pair `{a, b}` would
   otherwise lie in three triples, contradicting `pair_not_three`.)
3. **`octa_eight` / `octa_eight'`** — the half-octahedron closure.  From a support triple at
   `v` in a cubic solution where every vertex except possibly `v` has mass 4, the whole
   octahedron `v, a, b, a', b', y` is forced: six distinct vertices (`Dist6`) and the five
   links other than `v`'s (`Octa`, stated with the existing `LinkIs`).  Note this never uses
   `mass v`.
4. **`cubic_sum_mass`, `eleven_degree_split`** — `∑ mass = 48` under `Cubic`, hence the
   degree sequence is `(8, 4^10)` or `(6, 6, 4^9)`.
5. **`octa_v_triple`** — in an octahedron, a support triple `{v, x, z}` with `x` on the
   equator or at the antipode is one of the four equatorial triples at `v`.  (Not used by
   the final proof; kept because the `(6,6)` case will want it.)
6. **Condition (ii) in correlation form** — `condII_corr`:
   `∀ U ≠ 0, ∑_S n_S n_{S Δ U} = 0`; and `corr_bit_half`: the half of that sum over the `S`
   containing a fixed vertex `y` of `U` is itself `0` (the map `S ↦ S Δ U` is an involution
   exchanging the halves).  Plus the bitmask identity `tri_xor_pair`:
   `{y,p,q} Δ {v,y} = {v,p,q}`.
7. **`octa_kill`** — the kill.  An octahedron whose rim `a, b, a'` and antipode `y` have
   mass 4 contradicts condition (ii) at `U = {v, y}`.  See `INTEGRATE_delta0.md` for the
   three-line mathematical statement; it is shorter and stronger than "Lemma A" of
   `DELTA0_TOPOLOGY_FREE.md`, which can be deleted from the plan.
8. **`eleven_delta_zero_eight`** and **`eleven_delta_zero_reduce`** — the `(8, 4^10)`
   sub-case is closed and `delta = 0` is reduced to `(6, 6, 4^9)`.

## Next three steps (in order)

1. **The mass-6 link is 2-regular.**  Let `v, w` be the two mass-6 vertices.  Every pair
   `{v, x}` with `x ≠ w` has a mass-4 endpoint, so `pair_second`/`pair_not_three` give it
   degree exactly 0 or 2 in `link(v)`; `mass_six_card` gives `|supp v| = 6`, so `link(v)` is
   a 2-regular graph with six edges, and the degree sum forces `deg(w) ∈ {0, 2}` inside it.
   Needed Lean object: the analogue of `four_pairs_cycle` for six pairs, i.e. `C_6` or
   `C_3 + C_3`.  This is the one genuinely expensive step left (estimate 10-15 h); do it as
   a standalone file-local development in `WIP_delta0.lean` first, and reuse `card_sum_even`
   and the `four_cover` trick of `DeltaFour.lean` rather than a raw case split.
2. **Kill the `C_3` components with `octa_half`.**  A triangle component `z1 z2 z3` of
   `link(v)` all of whose vertices have mass 4 gives, by `octa_half` applied to the triple
   `{v, z1, z2}`, an apex `y` with `link(y)` containing the edge `z1 z2` and likewise for the
   other edges; `Corollary Y'` (link of a mass-4 vertex is a 4-cycle) then forces `k = 4`,
   contradiction.  `octa_half` already gives the shared apex, so this should be a short
   argument once step 1 exists.
3. **`C_6`: `link(w) = link(v)` and the six-fold `octa_kill`.**  The captain's third bullet
   derives `link(w) = link(v) = L` (six edges, same vertices).  Then repeat the `octa_kill`
   computation **verbatim with a 6-cycle instead of a 4-cycle**: condition (ii) at
   `U = {v, w}` gives `∑_{i=1}^{6} n_{v e_i} n_{w e_i} = 0`, while mass 4 at each of the six
   cycle vertices gives `e_i e_{i+1} = 1`, so all six agree and the sum is `±6`.  The
   generic machinery for this (`condII_corr`, `corr_bit_half`, `tri_xor_pair`,
   `supp_eq_quad`, `mass_four`) is already in the file — only the six-term bookkeeping and a
   `eps_kill6` are new.  Budget 4-6 h once step 1 is in.

Honest estimate for `eleven_delta_zero`: 15-25 agent-hours, almost all of it step 1.

## Gotchas
See `TOOLCHAIN_NOTES_delta0.md` — in particular: never write `by omega` for a trivial `≠`
side condition inside a big proof (it cost this lane two failed 3-minute compiles); destructure
`Dist6` and pass the named `Ne` or `Ne.symm` term instead.

# Lean certificate plan for F(11)  (task 14c, 2026-09-13)

## Assessment of the routes

The hand proof (R3_equals_10.md) ends in a closed-surface / Euler-characteristic argument
(delta = 0 case, and the C_4-link closure in R3_upper_bound.md Step 3).  Mathlib has no
classification of closed surfaces; the "topology-free" closure arguments are finite but each
one is a multi-page case analysis on bitmask hypergraphs.  The independent search that
confirms F(11) is a CDCL SAT search (CaDiCaL, ~500-1000 s per sub-case): far beyond kernel
`decide`, and a `native_decide` re-implementation would still need a (large) formal proof
that the search is exhaustive.  Route (A) is therefore not a one-run job.

Route chosen: (B).  Certify, sorry-free and kernel-checked (no native_decide), the strongest
structural theorems on the road to F(12) and F(11), all stated for an arbitrary solution of
the frozen `IsSol n N`.

## Module map (lean/R3/, all built by `lake build`, all gate-clean)

| file | content | status |
|---|---|---|
| Statement.lean | FROZEN finite statement F(n) | untouched |
| Basic.lean | chi, evalF, evalF_sq (f_N^2 = 16), linkVal_mem (E1), two_dvd_mass, four_le_mass (E2 weak), sum_mass_le, mass_four_pm, mass_four_card, mass_four (xor 0 + sign product 1) | PROVED (fixed 9 compile errors this run) |
| Mass.lean | mass_le_eight, **mass_cases** (n >= 11: mass in {4,6,8} = Lemma 1), **nine_mass_four** (n = 11: >= 9 vertices of mass 4), exists_mass_four, **bookkeeping** (e + delta = 48 - 4n) | PROVED |
| Link.lean | card_xor_two_pow, **mass_four_link** (Lemma 2(a) first half: four distinct link sets of size <= 2, xor 0, coefficients ±1 with product 1), **mass_four_even_degree** (every j lies in 0/2/4 of the four sets) | PROVED |
| Twelve.lean | **twelve_mass_four**, **twelve_card_three** (n = 12: all masses 4, all terms cubic = Step 1 of R3_upper_bound.md), twelve_coeff_pm, twelve_link_card_two, twelve_link | PROVED |
| Cycle.lean | pair bitmasks, exists_pair_of_card_two, **four_pairs_cycle** (four distinct pairs with xor 0 form a 4-cycle), **twelve_link_cycle** (n = 12: every vertex link is a 4-cycle = Step 2 of R3_upper_bound.md) | PROVED |
| Octahedron.lean | tri bitmasks, `Edge`/`Cyc`/`LinkIs`, twelve_link_struct, the 4-cycle combinatorics (edge_nbr, edge_no_triangle, edge_through, edge_rot/rev), link_sixth, link_of_three_faces, no_triangle_at, closure_of_links, **octahedron_closure** (Step 3 of R3_upper_bound.md, topology-free) | PROVED |
| Final.lean | xor_cancel_left, **F_twelve : F 12** (Step 4: the disjoint-sum contradiction). R_3 <= 11 machine-checked from the frozen statement. | PROVED |

Top certified theorem: **`R3.F_twelve : F 12`** — there is no coefficient vector satisfying the
frozen finite statement on 12 variables, i.e. no degree-3 Boolean function has 12 relevant
variables, i.e. **R_3 <= 11**.  Axioms: [propext, Classical.choice, Quot.sound].

## Not proved (planned, in order)

**F(12) is DONE (2026-09-13).**  Items 1 and 2 below are superseded; they are kept only to
record that the delivered Step 3 proves *less* than "two disjoint octahedra" on purpose:
`octahedron_closure` exports only the non-crossing property of the six-vertex set, which is
all Step 4 needs and is much cheaper.  For F(11) see **PLAN_F11.md**.

1. ~~**F(12) Step 3 (closure to two octahedra)**~~, topology-free version: from `twelve_link_cycle`
   at v with cycle a-b-c-d, show link(a) = b-v-d-x with x ≠ c and that the closure forces the
   octahedron {v,a,b,c,d,x} (8 triples), then that the remaining 8 triples form a second
   octahedron on the other 6 vertices.  Next lemma to attack:
   `twelve_pair_in_two`: for n = 12 and v < 12, every pair {v,x} lies in exactly 0 or 2
   support sets (immediate from `twelve_link_cycle` + `pair_eq_iff`), then
   `octahedron_closure`.  Estimate 6-10 agent-hours (bitmask bookkeeping dominates).
2. ~~**F(12) Step 4 (disjoint sum)**~~: with the support known to be two vertex-disjoint octahedra,
   CondII at U = S ∪ T (S in oct_1, T in oct_2) has exactly the two terms (S,T),(T,S), giving
   2 n_S n_T = 0, contradiction.  Needs a lemma computing the U-sum from an explicit support.
   Estimate 4-6 agent-hours.  Together 1+2 give **F(12)**, i.e. R_3 <= 11 machine-checked.
3. **F(11)**: see PLAN_F11.md for the current, detailed route.  Sketch: the hand proof's delta = 4, 2, 0 case split.  delta = 0 again needs closed-surface
   reasoning (chi = 3 / chi = 4 with a singular vertex): a topology-free replacement must be
   found first (likely: a bounded closure search from a mass-4 vertex, certified by `decide` on
   a canonical structure list, with the completeness argument done by hand).  Not attempted.
   Estimate 30+ agent-hours after F(12).

## Gate
`bash lean/gate.sh` — lake build, laundering grep (sorry/admit/axiom/native_decide/unsafe/
implemented_by/extern) over R3/, `#print axioms` for all 30 listed theorems; writes GATE.txt
and AXIOMS.txt.  Last result: see GATE.txt.

## Status 2026-09-13 (task 25, rotation 3)
Module map addition: `R3/Octahedron.lean` now also exports the per-vertex `CubicAt` API
(`cubicAt_of_cubic`, `cubicAt_link_card_two`, `link_cycle'`, `link_struct'`, `link_sixth'`,
`link_of_three_faces'`, `no_triangle_at'`, `closure_of_links'`, `octahedron_closure_gen'`);
the global-`Cubic` names are corollaries.  `R3.lean` imports `R3.LinkSix` and `R3.DeltaTwo`.
`R3/DeltaFour.lean` closes the whole `δ = 4` case with `eleven_delta_four`.
gate.sh: 97 theorems, GATE: PASS.

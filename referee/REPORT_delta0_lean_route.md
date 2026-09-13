# Referee report: proofs/DELTA0_LEAN_ROUTE.md (prose of the Lean delta = 0 route)

Referee pass, 2026-09-13, adversarial, by the author of the prose acting against himself.
Read in full: lean/R3/DeltaZero.lean (1388 lines), lean/R3/Statement.lean,
lean/R3/Octahedron.lean (LinkIs, Edge, link_sixth, link_of_three_faces, no_triangle_at),
lean/R3/Basic.lean (mass, supp, mass_four_pm, mass_four, mass_four_card),
lean/R3/Mass.lean (mass_cases, card_mass_ne_four_le_two), lean/INTEGRATE_delta0.md,
lean/HANDOFF_delta0.md, R3_upper_bound.md, R3_equals_10.md, referee/REPORT_delta0.md.
`lake` was not run (RAM); the Lean file's acceptance is taken from the lane's own record,
and this report checks **prose against Lean statements**, not Lean against Lean.

## Verdict: PASS

The prose proves exactly what Lean proves, with no step stronger than its Lean
counterpart, and no Lean hypothesis silently dropped. Findings 4 to 8 are remarks and
one-line improvements already folded into the prose; none changes the mathematics.

## Findings

### 1. (checked, no issue) Every prose lemma matches its Lean hypothesis list

- **Lemma H / `octa_half`**: Lean needs hsol, hcub, v, a, b < n, mass a = 4, mass b = 4,
  a != v, b != v, a != b, N(tri a v b) != 0. The prose asserts exactly these and claims
  exactly the returned distinctness list (a', b' each distinct from a, b, v, y; y distinct
  from a, b, v). The prose explicitly does **not** claim a' != b', which Lean does not
  return. Correct.
- **Lemma K / `octa_kill4`**: Lean needs hsol (so (i), (ii), (iii)) but **not** hcub, six
  vertices < n, Dist6 (all 15 distinctness facts), Octa4 (four links), and mass 4 at
  a, b, a', y. The prose lists precisely these and states that the mass of v, the mass of
  b' and the link of b' are unused. Verified by reading the proof term: no h4b' occurs,
  Octa4 has no b' link, and no mass of v appears. The prose does not claim Cubic is
  needed here; Lean does not take it. Correct.
- **Lemma C / octa_eight (and octa_eight')**: hexc : forall w < n, w != v -> mass w = 4.
  The prose says "every vertex other than v is ordinary". Correct.
- **Proposition 1 / `eleven_delta_zero_eight`**: same hexc; the claim that mass v = 8 is
  never used is confirmed (it is absent from the statement, and the mass-8 component of
  eleven_degree_split is discarded in eleven_delta_zero_reduce).
- **D1 / `apex_other`**: hexc at v and w, a != v, a != w, b != v, b != w, a != b, and the
  three bounds v, a, b < n. Lean requires **neither** w < n **nor** v != w. Prose says so.
- **D2 / `no_exc_pair`**: adds hw : w < n, hvw : v != w, u != v, u != w. Prose matches.
- **D3 / `apex_gen`**: a, b not in {v, w}, a != b, a != x, b != x, x < n; no mass and no
  bound hypothesis on v or w. Prose matches, including the asymmetry of the conclusion in
  a and b ({v,b,x} and {w,b,x}, not {v,a,x}).
- **D4 / `kill_pair`**: hvw : v != w is required, plus s, t, u ordinary and pairwise
  distinct. Prose matches (this requirement was implicit in the first draft; now stated).
- **D5 / `kill_free_triple`**: inherits hvw. Prose now states it.
- **D6 / `exists_free_set`**: takes hsol, hdisj, mass v = 6, mass w = 6, and **not** hcub,
  not v < n, not w < n, not v != w. Prose says "condition (i) only"; accurate (only
  condition (i) out of the solution package is used).
- **Theorem / `eleven_delta_zero`**: matches.

### 2. (checked, no issue) The sign argument in Lemma K is faithfully rendered

The prose chain is: supp(y) is exactly the four y-faces [supp_eq_quad with mass y = 4];
condition (ii) at U = {v,y} restricts to supp(y) because S -> S xor U is a bijection
between the sets containing y and those not, so the two halves of the autocorrelation are
equal and each is zero [condII_corr, corr_bit_half, corr_supp]; the translate of {y,p,q}
is {v,p,q} [tri_xor_pair]; the four terms e1..e4 are each +-1 [mass_four_pm, pm_mul]; the
mass-4 products at a, b, a' give e1 e2 = e1 e4 = e3 e4 = 1 [mass_four]; four equal signs
cannot sum to zero [eps_kill]. The three supports quoted in the prose,
supp(a) = {vab, vab', yab', yab}, supp(b) = {vab, va'b, ya'b, yab},
supp(a') = {va'b', va'b, ya'b, ya'b'}, are exactly Lean's hsa, hsb, hsa'. Correct.

Machine check: referee/delta0_lean_signs.py. Of the 256 sign patterns on the eight faces,
32 satisfy the three mass-4 relations at a, b, a'; **all 32 have correlation +-4 at
{v, y}, none has 0**. It also records that the relation at b' is implied by the three used
(which is why dropping the b' link costs nothing; the prose does not need or claim this).

### 3. (checked, no issue) Nothing in the prose is stronger than Lean

Three places where the prose could have overclaimed and does not:

- It never claims link(v) is anything. Lean never determines it; Steps 3 and 9 say so.
- "Exactly two triples through a pair" is claimed only for pairs through an **ordinary**
  vertex, which is what pair_second plus pair_not_three give (both need mass 4 at one end).
- Proposition 1 is stated as "at most one exceptional vertex", which is what Lean proves,
  not as the weaker "(8, 4^10) is impossible".

(M1)'s "lies in exactly four support sets" is mass_four_card in Basic.lean, and is cited.

### 4. (remark) n = 11 enters in exactly two places

Step 1 (degree split, via card_mass_ne_four_le_two and the mass sum 48) and Step 7
(6 + 6 < 16). Steps 2 to 6 are theorems about any n with at most two exceptional vertices.
Section 8 of the prose records this; it is the strongest statement the route supports.

### 5. (remark) The mass-8 case is closed without using the mass

eleven_delta_zero_eight needs only "all other vertices have mass 4", so the (8, 4^10)
branch is not a mass-8 argument at all. The paper should not present it as one.

### 6. (remark) D6 does not use Cubic

exists_free_set is a pure weight count under condition (i); Cubic is used only afterwards,
to turn the free support set into a triple (exists_tri_of_card_three).

### 7. (remark) Where distinctness of a' and b' comes from

Lemma H does not supply it; it is re-derived three times (in octa_eight, apex_other,
apex_gen) from "a 4-cycle has no triangle" at the ordinary apex y [no_triangle_at]. A
referee reading only Lemma H would think it missing. The prose flags this at the end of
Step 2; keep that sentence in the paper.

### 8. (remark) The apex y is never assumed ordinary in D1 and D3

Both split on y in {v, w} versus y ordinary, and only the second branch uses Lemma K. That
is what lets the argument run without knowing anything about the exceptional vertices.

## The 630 completions

No contradiction; Section 9 of the prose is correct. The seeded search
(REPORT_delta0.md, finding 8) found that in the (8, 4^10) branch only C_4 + C_4 admits
completions, 630 of them, all two octahedra glued at v, and that nothing combinatorial
excludes them: they die only to Lemma A's sign argument. octa_kill4 **is** that sign
argument, localised to one octahedron: condition (ii) at the pair {apex, antipode}, with
the four equatorial sign products forced equal by the three mass-4 sign relations. Lemma A
computes the global identity sum over a of P'(a)^2 = 64 on the whole glued configuration;
Lemma K computes a four-term sum over supp(y) only. Both say "the signs cannot cancel".
The 630 configurations are exactly the ones Lemma K kills, so they confirm the route.

Two asymmetries worth stating in the paper:

- The Lean route enumerates nothing and needs only one support triple with two mass-4
  ends, so it never meets C_8, C_3 + C_5 or the bowtie. The bowtie gap that sank
  DELTA0_TOPOLOGY_FREE.md (finding 1 of REPORT_delta0.md) is not patched here; it is
  bypassed, because no link of an exceptional vertex is ever classified.
- "(6, 6, 4^9) admits zero completions from all 15 link shapes" is a stronger
  combinatorial statement than the route uses, and is independent evidence for the same
  conclusion.

## Verified by hand

Lemma H (the y1 = y2 step and the exact distinctness list), Lemma K's eight faces, four
supports and three sign relations, Lemma C's three forced links, Proposition 1, D1 in both
branches (a' = w and a' != w), D2's use of link_v_nbrs on the 4-cycle d - v - b' - w, D3's
four alternatives, D4's rotation of link(s), D5's four case-splits against D4 with the
correct (s, t, u) in each, D6's weight count, and the assembly in eleven_delta_zero
(including that the third vertex of a {v, w}-triple is ordinary).

## Verified by computation

- referee/delta0_lean_signs.py: 256 sign patterns on the octahedron's eight faces; 32
  satisfy the mass-4 relations at a, b, a'; none of the 32 has vanishing correlation at
  {v, y} (all +-4). Also: the relation at b' is implied by those at a, b, a'.

## Bottom line

PASS. proofs/DELTA0_LEAN_ROUTE.md is a faithful, self-contained prose rendering of
eleven_delta_zero, checkable without Lean. It should replace the topological
"Case delta = 0" of R3_equals_10.md and all of lean/DELTA0_TOPOLOGY_FREE.md.

# Topology-free proof of the delta = 0 case (n = 11, all terms cubic)

(Referee 2026-09-13 21:25, referee/REPORT_delta0.md: PASS-with-fixes. Finding 1 (bowtie, deg(w) = 4) and finding 2 (y' ∉ {a_i}) patched below. Findings 3-5 are wording: in Lemma Y, y ∉ C because y is the fourth vertex of the 4-cycle link(z_i), distinct from z_{i-1}, z_i, z_{i+1}, and y ≠ z_j for other j since z_j z_{j+1} y would be a 3-set containing y twice for j = the index with y = z_j; the chain of equalities runs along the path of mass-4 vertices z_1..z_{k-1}, and both edges at w are covered by their mass-4 endpoints; k ≥ 3 throughout.)

(Fable, 2026-09-13 19:00. Replaces every Euler-characteristic / closed-surface step of "Case delta = 0" in
R3_equals_10.md by one combinatorial lemma plus one algebraic lemma. Written for the Lean lane; every step is
finite bookkeeping on bitmasks.)

Setting. n = 11, IsSol, Cubic (every support set has card 3). All coefficients are ±1 (Lemma 2(d): a ±2 would need
three vertices of mass 8), so mass m_v = number of support triples containing v, sum m_v = 48, and the degree
sequence is (8, 4^10) or (6, 6, 4^9) (masses in {4,6,8}, at most two exceptional vertices).
Available: `link_cycle` (mass 4 ⇒ link is a 4-cycle a-b-c-d, i.e. the four triples at v are vab, vbc, vcd, vda),
`pair_not_three` (a pair with a mass-4 endpoint lies in 0 or 2 triples), `no_crossing_split`.

## Lemma Y (the cycle lemma)
Let v be any vertex and let C = (z_1, ..., z_k), k >= 3, be a cycle component of link(v) (so vz_iz_{i+1} is a
support triple for all i, indices mod k, and these are the only triples at v meeting C). Suppose every z_i with
at most one exception z_0 = z_k =: w has mass 4. Then there is a vertex y ∉ {v, z_1, ..., z_k} such that
z_i z_{i+1} y is a support triple for every i (all k of them); hence m_y >= k and link(y) contains the cycle C.

Proof. For a mass-4 vertex z_i, link(z_i) is a 4-cycle containing the path z_{i-1} - v - z_{i+1} (from the triples
vz_{i-1}z_i and vz_iz_{i+1}), so link(z_i) = z_{i-1} - v - z_{i+1} - y_i - z_{i-1} for a vertex y_i ∉ {v, z_{i-1}, z_i,
z_{i+1}}; thus z_iz_{i+1}y_i and z_{i-1}z_iy_i are support triples. Now take consecutive z_i, z_{i+1} with z_i of
mass 4 (if z_{i+1} = w this is still fine). The pair {z_i, z_{i+1}} has a mass-4 endpoint, so by pair_not_three it
lies in exactly two triples: vz_iz_{i+1} and one other. If z_{i+1} also has mass 4, that other triple is both
z_iz_{i+1}y_i and z_{i+1}z_iy_{i+1}, so y_i = y_{i+1}. Walking around the cycle through the mass-4 vertices gives a
single y = y_i for all mass-4 z_i; the triples z_iz_{i+1}y for every edge of C follow (an edge with the exceptional
endpoint w is covered by the mass-4 endpoint's link). y ∉ C: if y = z_j then z_jz_{j+1}y is not a 3-set (or
z_{j-1}z_jy), contradiction; y ≠ v by construction. QED.

Corollary Y'. If in Lemma Y the vertex y has mass 4, then link(y) is a 4-cycle containing the k-cycle C, so k = 4
and link(y) = C exactly (the four triples at y are z_iz_{i+1}y).

## Lemma A (algebraic kill of the glued octahedra)
Let a_1..a_4, b_1..b_4, v, y, y' be the 11 vertices and suppose the 16 support triples are exactly
v a_i a_{i+1}, y a_i a_{i+1}, v b_j b_{j+1}, y' b_j b_{j+1} (i, j mod 4), coefficients ±1. Then IsSol fails.
Proof. Write P(a) = sum_i c_i a_i a_{i+1}, P'(a) = sum_i c'_i a_i a_{i+1}, Q(b), Q'(b) likewise (all c's ±1), so
4 f = x_v (P(a) + Q(b)) + x_y P'(a) + x_{y'} Q'(b). Fix a, b and put α = P(a)+Q(b), β = P'(a), γ = Q'(b) (integers).
Since (±α ± β ± γ)^2 = 16 for all eight sign choices: subtracting pairs gives α(β+γ) = β(α+γ) = γ(α+β) = 0, and
averaging gives α^2 + β^2 + γ^2 = 16. If β ≠ 0 and γ ≠ 0 then α = -γ = -β, so 3β^2 = 16, impossible. Hence for every
a, b: at most one of β = P'(a), γ = Q'(b) is nonzero. But P' is a nonzero polynomial with four distinct monomials,
so P'(a_0) ≠ 0 for some a_0, and likewise Q'(b_0) ≠ 0 for some b_0; the pair (a_0, b_0) contradicts. QED.
(For Lean: the sign-choice identities are a 3-variable integer fact, `omega`/`nlinarith` after `decide` on the
eight cases; "a quadratic with a nonzero coefficient is nonzero somewhere" is Parseval or the explicit point
a = (1,1,1,1) vs a flipped coordinate: P'(1,1,1,1) - P'(-1,1,1,1) = 2(c'_1 + c'_4) — pick the argument that
fits; simplest: sum over a of P'(a)^2 = 16 · 4 > 0.)

## The case analysis

### (8, 4^10). Let v be the mass-8 vertex; all others have mass 4.
Every pair {v, x} has a mass-4 endpoint, so it lies in 0 or 2 triples: link(v) is 2-regular with 8 edges, i.e. a
disjoint union of cycles of lengths summing to 8 (each of length >= 3): C_8, C_3 + C_5, or C_4 + C_4. All cycle
vertices have mass 4.
* A component of length k ∈ {3, 5, 8} gives (Lemma Y) a vertex y ≠ v with link(y) ⊇ C_k. Since y ≠ v, m_y = 4,
  and Corollary Y' forces k = 4. Contradiction. So link(v) = C_4 + C_4 on a_1..a_4 and b_1..b_4.
* C_4 + C_4: Lemma Y on each 4-cycle gives y (with the four triples y a_i a_{i+1}) and y' (with y' b_j b_{j+1}).
  m_y = 4, so those are all of y's triples; y ∉ {b_j} (b_j already has its two v-triples and would exceed mass 4);
  y ≠ y' (y is exhausted); symmetrically y' ∉ {a_i} (each a_i is exhausted by its four triples with v and y).
  So v, a's, b's, y, y' are 11 distinct vertices and 8 + 8 = 16 triples are accounted for:
  the support is exactly the configuration of Lemma A. Contradiction.

### (6, 6, 4^9). Let v, w be the mass-6 vertices.
Every pair {v, x} with x ≠ w has a mass-4 endpoint, so λ_{vx} ∈ {0, 2}: every vertex of link(v) other than w has
degree 2. With 6 edges, deg(w) + 2t = 12, so deg(w) is even. deg(w) = 6 is impossible (all six edges at w leave the
other link vertices of degree 1). If deg(w) = 4 then, by the edge count, link(v) is the bowtie: w adjacent to
a_1..a_4 plus a perfect matching on the a_i. Then λ_{vw} = 4, so v has degree 4 in link(w); link(w) has 6 edges and
all its vertices except v have degree 2, so by the same count link(w) is a bowtie centred at v on the same a_1..a_4
(the vertices of the four triples v w a_k). Say v pairs (a_1a_2)(a_3a_4), giving triples v a_1 a_2 and v a_3 a_4.
 - Same pairing at w: link(a_1) contains {v,w} (from v w a_1), {v,a_2} (from v a_1 a_2) and {w,a_2} (from w a_1 a_2),
   a triangle; but m_{a_1} = 4, so link(a_1) is a 4-cycle, which has no triangle. Contradiction.
 - Different pairing, say w pairs (a_1a_3)(a_2a_4) (the pairing (a_1a_4)(a_2a_3) is the same after relabelling):
   link(a_1) contains the path a_2 - v - w - a_3, so its fourth edge closes the 4-cycle, {a_2,a_3}, i.e. a_1 a_2 a_3
   is a support triple. Then link(a_2) contains {v,w}, {v,a_1}, {w,a_4}, {a_1,a_3}, in which a_3 and a_4 have
   degree 1, so it is not a 4-cycle. Contradiction.
Hence deg(w) ∈ {0, 2}: link(v) is 2-regular with 6 edges, C_6 or C_3 + C_3, and each component contains at most the
one exceptional vertex w.
* A component C of length k containing w (k = 3 or 6): Lemma Y (with the exception w) gives y ∉ C ∪ {v} with
  link(y) ⊇ C; y ≠ w since w ∈ C. Then y has mass 4 (the only vertices of mass ≠ 4 are v, w), and Corollary Y'
  forces k = 4. Contradiction. So w ∉ link(v).
* A component C of length k ∈ {3, 6} not containing w: Lemma Y gives y with link(y) ⊇ C_k, k ≠ 4, so m_y ≠ 4, so
  y = w. Hence link(w) ⊇ link(v) as edge sets on the same vertices, and both have 6 edges: link(w) = link(v) =: L
  (two triangles or a hexagon), and the 12 triples v e, w e (e ∈ L) exhaust v, w (mass 6 each) and every cycle
  vertex z (mass 4: two triples with v, two with w).
* So the 8-set A = {v, w} ∪ V(L) is closed: no support triple crosses A (every vertex of A is exhausted by triples
  inside A). The remaining 16 - 12 = 4 support triples lie in the complement, which has 11 - 8 = 3 vertices and
  therefore only one 3-subset: contradiction (support sets are distinct). (Alternatively `no_crossing_split`.)

All sub-cases of delta = 0 are closed. No surfaces, no Euler characteristic, no Fact T.

## Remarks for the hand proof and the paper
This argument is shorter than the topological one and should replace "Case delta = 0" in R3_equals_10.md and in
paper/main.tex (Appendix A) once the Lean lane confirms the formal version. Lemma Y also gives a two-line proof of
Part I Step 3 (n = 12: link(v) is a 4-cycle for every v; Lemma Y at v gives the sixth vertex y with mass 4 and
link(y) = link(v), the octahedron; iterate). It needs a referee pass before it enters the paper (queue: referee
lane, after the Lean lane's confirmation).

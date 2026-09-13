# Theorem. R_3 = 10: a Boolean function of degree 3 has at most 10 relevant variables, and 10 is attained.

(Fable, 2026-09-12; revised the same day after referee round 1: added link type L4 and the three cases depending on it, plus topology clarifications. Tier: proof, pending referee round 2. Part I (no 12) is R3_upper_bound.md; this file proves
"no 11" and hence R_3 = 10, the lower bound being the CHS function Xi_3 with 10 variables.)

Notation as in R3_upper_bound.md. f : {-1,1}^11 -> {-1,1}, deg f <= 3, all 11 variables relevant. Write
f = sum_S c_S chi_S, n_S := 4 c_S in Z (granularity), sum_S n_S^2 = 16 (Parseval). For a vertex i put
m_i := sum_{S ∋ i} n_S^2 = 16 Inf_i(f) = 16 Pr[D_i f ≠ 0].

## Lemma 1 (values of m_i). m_i in {4, 6, 8}, and sum_i m_i = sum_S |S| n_S^2 <= 48.
Proof. D_i f = sum_{S ∋ i} (n_S/4) chi_{S \ i} is {-1,0,1}-valued (f is Boolean) of degree <= 2, so
4 D_i f = sum_j n_j chi_{T_j} takes values in {0, ±4} with the T_j distinct sets of size <= 2 and sum n_j^2 = m_i.
Since a relevant variable has Inf_i >= 1/4 (Nisan–Szegedy), m_i >= 4. sum_i m_i = sum_S |S| n_S^2 <= 3 sum n_S^2 = 48,
so with 11 vertices each >= 4 we get m_i <= 48 - 40 = 8 for every i. Now exclude m_i = 5, 7:
 - any pattern with an odd number of odd n_j has odd value sum, never in {0, ±4}: this kills five ±1's, seven ±1's,
   {±2, ±1} and {±2, ±1, ±1, ±1};
 - pattern {±2, ±1, ±1} (m = 6): 2u_0 + u_1 + u_2 in {0, ±4} forces u_1 = u_2 for every x, i.e. chi_{T_1} ≡ ± chi_{T_2},
   impossible for distinct T_1 ≠ T_2. So m_i = 6 occurs only as six ±1's.
Hence m_i in {4, 6, 8}. QED.

## Lemma 2 (link structure). Let the *link* of i be the family {T_j} = {S \ i : n_S ≠ 0, S ∋ i} with signs.
 (a) m_i = 4: four ±1 terms; needed and sufficient: T_1 Δ T_2 Δ T_3 Δ T_4 = ∅ and prod eps_j = +1
     (sum of four ±1's avoids ±2 iff the number of -1's is even iff prod u_j ≡ 1). Four distinct sets of size <= 2
     with every element in an even number of them are exactly: (L1) a 4-cycle of pairs on 4 vertices;
     (L2) {∅, {a}, {b}, {a,b}}; (L3) {{a}, {b}, {a,c}, {b,c}}; (L4) {∅, {a,b}, {b,c}, {a,c}}.
     (Enumeration, verified by computer in referee/check_links.py: without ∅, four pairs with all degrees even form
     a C_4, and singletons come in pairs {a},{b} needing {a,b} plus a fourth set — ∅ gives L2 — or {a,c},{b,c} giving L3;
     with ∅ the other three sets have Δ = ∅: three pairs forming a triangle (L4) or {a},{b},{a,b} (L2).)
     Interpretation: L1 = i lies in four cubic terms only; L2 = linear term {i}, quadratics {i,a},{i,b}, cubic {i,a,b};
     L3 = quadratics {i,a},{i,b} and cubics {i,a,c},{i,b,c}; L4 = linear term {i} and cubics {i,a,b},{i,b,c},{i,a,c}.
     Note: a link containing a singleton is L2 or L3; a link containing ∅ is L2 or L4; a link containing a triangle
     of pairs is L4 (a C_4 has no triangle).
 (b) m_i = 6: six ±1 terms with T_1 Δ ... Δ T_6 = ∅ and prod eps_j = -1 (six ±1's avoid ±2, ±6 iff #(-1) is odd).
 (c) m_i = 8: either two ±2 terms (any two distinct sets), or {±2, ±1 x4} with the four unit sets having Δ = ∅ and
     sign product -1, or eight ±1 terms with Δ = ∅, sign product +1, and never all eight agreeing.
 (d) A vertex whose only term has |n_S| = 2 is impossible (D_i f = ±chi/2 is not {-1,0,1}-valued). Consequently a
     term with |n_S| = 2 forces every vertex of S to have m in {8} (m = 6 cannot contain a ±2 by Lemma 1's proof).
 (e) In a link that consists of pairs only (no lower-order terms at i), lambda_{ix} := #{S ∋ i, x} equals the degree
     of x in the link graph; for L1 it is 2 for the four link vertices and 0 otherwise.

## Bookkeeping. Let delta := sum_S (3 - |S|) n_S^2 (weight below the top level, weighted) and e := sum_i (m_i - 4).
Then e + delta = 48 - 44 = 4, e >= 0, delta >= 0. Contributions to delta: quadratic ±1 term -> 1, quadratic ±2 -> 4,
linear ±1 -> 2, constant ±1 -> 3 (linear/constant ±2 give 8, 12 > 4, impossible).
By Lemma 1, e in {0, 2, 4} with e = 0 (all m_i = 4), e = 2 (one m_i = 6), e = 4 (two m_i = 6 or one m_i = 8).

## Case delta = 4 (all m_i = 4). Every link is L1, L2, L3 or L4. Lower-order weight 4 = one of {1,1,1,1}, {4}, {2,1,1},
{2,2}, {3,1}.
 - {4}: a quadratic ±2 term; by Lemma 2(d) its endpoints need m = 8, contradiction.
 - {2,2}: two linear terms {i}, {j}, no quadratics. i's link contains ∅ and there are no quadratics, so it is L4:
   cubics {i,a,b},{i,b,c},{i,a,c}; likewise j is L4. If j ∈ {a,b,c}, say j = a, then a's link (∅ plus a triangle
   containing {i,b},{i,c}) forces the cubic {a,b,c}, and link(b) ⊇ {i,a},{i,c},{a,c} is a triangle although b has no
   lower-order term and m_b = 4 (so link(b) must be a C_4). Hence j ∉ {a,b,c}, and a, b, c are L1: link(a) ⊇ {i,b},{i,c}
   completes to the 4-cycle i-b-w-c, giving cubics {a,b,w},{a,c,w}; the same at b and c gives {a,b,w'},{b,c,w'} and
   {a,c,w''},{b,c,w''}, and the shared cubics force w = w' = w''. Then link(w) contains the triangle {a,b},{a,c},{b,c},
   so w is L4, so w = j. The terms {i},{j},{i,a,b},{i,b,c},{i,a,c},{j,a,b},{j,b,c},{j,a,c} exhaust the vertices
   i,j,a,b,c (m = 4 each) and carry weight 8; the remaining weight 8 lives on the other 6 variables, so f is a sum of two
   non-constant functions on disjoint variable sets — impossible by the disjoint-sum lemma. ✗
 - {3,1}: a constant and one quadratic {i,a}; i's link contains {a}, so is L2 or L3; L2 needs a linear term, L3 needs
   two quadratics at i. ✗
 - {2,1,1}: one linear {i}, two quadratics. i's link contains ∅, so it is L2 or L4.
   L2 = {∅,{a},{b},{a,b}}: the two quadratics are {i,a},{i,b} and {i,a,b} is a cubic. a's link contains {i} (from {i,a}),
   so a is L2 or L3; L2 needs a linear term {a} (only {i} exists), L3 = {{p},{q},{p,r},{q,r}} with {i} = {p} and the pair
   {i,b} (from {i,a,b}) = {p,r}, so r = b and the fourth quadratic {a,q} must exist with q ≠ i; but only {i,a},{i,b}
   exist. ✗  L4: no quadratic touches i, so every endpoint u of a quadratic has u ≠ i, a singleton in its link, no
   linear term of its own, hence is L3 and lies on exactly two quadratics; the two quadratics would form a 2-regular
   graph with 2 edges, impossible. ✗
 - {1,1,1,1}: four unit quadratics Q, no linear or constant term. Every endpoint u of a quadratic has a singleton in its
   link, hence is L3, hence lies on exactly two quadratics: Q is a 2-regular graph with 4 edges, i.e. a 4-cycle
   i-a-j-b-i. L3 at each of i,a,j,b: the two cubics at i are {i,a,c_i},{i,b,c_i}, etc. Let S_0 = {i,a,j,b} and N the
   cubics meeting S_0 (each meets S_0 in 2 or 3 vertices, since it contains one of i,a,j,b together with a Q-neighbour).
   Each of i,a,j,b lies in exactly 2 cubics, so sum_{T in N} |T ∩ S_0| = 8. The 7 vertices outside S_0 all have m = 4,
   hence 28 = sum_{T in N} |T \ S_0| + 3 M with M the number of cubics disjoint from S_0, while 16 = 4 + |N| + M.
   Writing k = #{T in N : |T \ S_0| = 1}: 3(12 - |N|) = 28 - k, so k = 3|N| - 8 <= |N|, forcing |N| in {3, 4}.
   * |N| = 4: all four cubics of N have exactly two vertices in S_0 and one outside. Take {i,a,c}. c has an L1 link
     containing the pair {i,a}, so the 4-cycle in link(c) is i-a-y-z-i, giving cubics {c,a,y},{c,y,z},{c,z,i}. a's only
     other cubic is {a,j,c_a}, so y = j and c_a = c; i's only other cubic is {i,b,c_i}, so z = b, c_i = c; and {c,j,b}
     is a cubic. Thus N = {cai, caj, cjb, cbi}, m_c = 4 is exhausted, and i, a, j, b are exhausted too (two quadratics and two
     cubics each), so no other term meets {i,a,j,b,c} and f = g(x_i,x_a,x_j,x_b,x_c) + h(other 6 vars)
     with both parts non-constant — impossible by the disjoint-sum lemma (R3_upper_bound.md Step 4). ✗
   * |N| = 3: two cubics inside S_0 and one meeting it in an edge. Two 3-subsets of the 4-cycle vertex set share two
     vertices; up to symmetry they are {i,a,j},{i,a,b} (sharing the Q-edge {i,a}) or {i,a,j},{j,b,i} (sharing the
     diagonal {i,j}). First: link(i) = {{a},{b},{a,j},{a,b}} is not of the form {{p},{q},{p,r},{q,r}}. Second: link(a)
     contains the pair {i,j} (from the cubic {i,j,a}), but an L3 link at a has the form {{p},{q},{p,r},{q,r}} with
     r ∉ {p,q} = {i,j}, so {i,j} = {i,r} would force r = j. Both ✗.
 So delta = 4 is impossible.

## Case delta = 2 (one vertex v with m_v = 6, ten with m = 4). Lower-order weight 2 = one linear ±1 term, or two
unit quadratics.
 - One linear term {l}: l's link contains ∅. There are no quadratics, so every vertex other than l has a link made of
   pairs only: C_4 if m = 4, and C_6 / two triangles / bowtie if m = 6.
   If m_l = 4 the link is L4: cubics {l,a,b},{l,b,c},{l,a,c}. Suppose first v ∉ {a,b,c}. Then a,b,c have C_4 links;
   link(a) ⊇ {l,b},{l,c} completes to l-b-w-c giving {a,b,w},{a,c,w}, and similarly at b, c, with the shared cubics
   forcing a common w and the cubics {a,b,w},{a,c,w},{b,c,w}. So link(w) contains the triangle abc, hence is not a C_4,
   hence w = v (w ≠ l since l's link is exhausted), and link(v) ⊇ triangle abc with m_v = 6: link(v) is two triangles
   abc ∪ xyz or a bowtie; a bowtie containing abc has its centre in {a,b,c}, say a, giving lambda_{va} = 4 and a vertex of
   degree 4 in link(a), not a C_4. So link(v) = abc ∪ xyz with cubics {v,x,y},{v,y,z},{v,x,z}; x,y,z have C_4 links, and
   the same completion argument yields cubics {x,y,t},{x,z,t},{y,z,t} for a common t, so link(t) contains a triangle;
   t ∉ {v, l} since both links are exhausted, so t has a C_4 link containing a triangle. ✗
   If v ∈ {a,b,c}, say v = a: b and c have C_4 links, link(b) ⊇ {l,a},{l,c} gives {a,b,w},{b,c,w} and link(c) ⊇ {l,a},{l,b}
   gives {a,c,w'},{b,c,w'}; the shared cubic {b,c,·} forces w = w', so link(w) ⊇ triangle abc; w ∉ {l, a} ({l,a,b} would be
   repeated, and {a,a,b} is not a set), so w has a C_4 link containing a triangle. ✗
   Hence m_l = 6, i.e. l = v, and v's link is ∅ plus five pairs with even degrees everywhere: a 5-cycle a_1 ... a_5. Cubics {v,a_k,a_{k+1}}. Each a_k has an L1 link
   containing {v,a_{k-1}},{v,a_{k+1}}, completed to a 4-cycle v-a_{k+1}-w_k-a_{k-1}-v by cubics {a_k,a_{k±1},w_k}.
   If w_k were another a_m, some a's link would contain a triangle (e.g. w_1 = a_3 gives link(a_2) ⊇ {v,a_1},{v,a_3},
   {a_1,a_3}), impossible in a C_4. So w_k is outside {v, a's}. The cubic {a_k,a_{k+1},w_k} is one of a_{k+1}'s two
   non-v cubics, so w_{k+1} = w_k; hence all w_k = w and w lies in 5 cubics: m_w = 5, contradicting Lemma 1. ✗
 - Two quadratics: an endpoint u with m_u = 4 is L3 and needs both quadratics at u: {u,p},{u,q}. Then p ≠ v would need
   two quadratics at p, impossible, so p = v, and likewise q = v, contradicting p ≠ q. If no m = 4 vertex is an endpoint,
   each quadratic has both endpoints equal to v. ✗
 So delta = 2 is impossible.

Fact T (surfaces of non-positive Euler characteristic). In a closed connected triangulated surface with V' vertices,
E' edges, F' faces and Euler characteristic chi', 3F' = 2E' and V' - E' + F' = chi' give degree sum 2E' = 6V' - 6chi'.
Hence chi' <= 0 forces average degree >= 6. In every complex below all degrees are 4 except at most two vertices of
degree <= 8, so the average degree is <= 4 + 8/V' < 6 as soon as V' >= 5, and V' >= 5 holds because some vertex has
degree >= 4 (a closed triangulated surface has no vertex of degree < 3, and V' >= deg + 1). So every component is a
sphere (degree sum 6V' - 12) or a projective plane (degree sum 6V' - 6, and at least 6 vertices, Part I Step 3).
(Checked: referee/round2c_out_check.txt section D lists V' = 3chi' + c/2 for every degree pattern used; every
chi' <= 0 row gives V' <= 2.)

## Case delta = 0 (homogeneous cubic). f = (1/4) sum_S n_S chi_S over triples, sum n_S^2 = 16; degree sequence
(m_i) is (8, 4^10) or (6, 6, 4^9). No |n_S| = 2 occurs: by Lemma 2(d) its three vertices would all need m = 8. So F is a
3-uniform hypergraph with 16 triples; links are C_4 (m = 4, Lemma 2(a)); for m = 6 a simple graph with 6 edges and all
degrees even: C_6, two disjoint triangles, or a bowtie (two triangles sharing a vertex); for m = 8 a simple graph with
8 edges and all degrees even.
 Sub-case (8, 4^10). Let v have m_v = 8. If some x has lambda_{vx} = 4, then v has degree 4 in link(x), so link(x) is
 not a C_4, contradicting m_x = 4 (x ≠ v since x is a vertex of link(v)). Hence link(v) is 2-regular: C_8, C_3 ∪ C_5, or C_4 ∪ C_4, and every pair lies in 0 or 2 triples.
 So |F| is a closed pseudo-manifold; all links are single cycles except possibly at v.
  * C_8: closed surface, V = 11, E = 24, F = 16, chi = 3. Components: a closed surface with all degrees 4 except at
    most one vertex of degree 8 has sum deg = 4V' + 4[v in it]; sphere needs 6V' - 12, giving V' = 6 (octahedron, v
    absent) or 6V' - 12 = 4V' + 4, V' = 8 (a sphere on 8 vertices with degrees (8, 4^7): impossible, v would have 8
    neighbours among 7 vertices); projective plane needs 6V' - 6, V' = 3 or 5 (< 6 vertices, impossible); chi' <= 0 is
    excluded by Fact T. So chi = 3 cannot be realised. ✗
  * C_4 ∪ C_4: split v into v_1, v_2 (each of degree 4). We get a closed surface with 12 vertices all of degree 4:
    chi = 12 - 24 + 16 = 4 and, as in Part I, it is two octahedra. If v_1, v_2 lie in the same octahedron (this sub-case is in fact empty, since the
    two C_4's of link(v) are vertex-disjoint while two vertices of an octahedron share two or four neighbours), the other
    octahedron uses 6 variables disjoint from everything else and f is a disjoint sum, impossible by the disjoint-sum
    lemma. Otherwise the two octahedra are glued at the identified vertex v. Write
    f = g_1(x_v, y) + g_2(x_v, z), y, z disjoint 5-sets. Fixing x_v = 1: g_1(1, y) + g_2(1, z) in {±1} for all y, z,
    so by the disjoint-sum lemma one of them is constant; but g_1(1, y) = (1/4) sum of the 8 face-characters of the
    first octahedron with x_v = 1, which are 8 distinct non-constant monomials in y (four quadratic, four cubic), so
    it is not constant; same for g_2. ✗
  * C_3 ∪ C_5: split v into v_1 (degree 3) and v_2 (degree 5): closed surface with 12 vertices, degrees (3, 5, 4^10),
    chi = 4. Components with chi <= 1 are excluded by degree counts: chi' <= 0 is excluded by Fact T; a
    projective plane needs degree sum 6V' - 6, which with all degrees <= 5 forces V' <= 6 (and a triangulated
    projective plane has at least 6 vertices, Part I Step 3), and the only 6-vertex projective plane has all six
    degrees equal to 5 while we have a single degree-5 vertex. Hence two spheres. A sphere with degree sum 6V' - 12 using degrees from {3, 5, 4}: containing both 3 and 5
    gives 8 + 4a = 6(a + 2) - 12, a = 4, a 6-vertex sphere with degrees (5, 4, 4, 4, 4, 3): the degree-5 vertex is
    adjacent to all others, its link is a 5-cycle, and the remaining 3 faces triangulate that pentagon with two
    diagonals; any two diagonals of a pentagon share a vertex or cross, so some vertex gets diagonal-degree 2 or the
    triangulation is invalid, and the degree pattern (4,4,4,4,3) on the pentagon (diagonal degrees (1,1,1,1,0)) cannot
    occur. Containing 3 but not 5: 3 + 4a = 6(a+1) - 12, a = 4.5. Containing 5 but not 3: 5 + 4a = 6(a+1) - 12,
    a = 5.5. ✗
 Sub-case (6, 6, 4^9). Let v, v' have m = 6.
  * If some link is a bowtie, say at v with centre w, then lambda_{vw} = 4, so v has degree 4 in link(w), forcing
    w = v', and symmetrically link(v') is a bowtie centred at v. The four common triples are {v,v',a_k}, k = 1..4.
    The bowtie at v adds {v,a_1,a_2},{v,a_3,a_4} (some pairing), the one at v' adds {v',a_i,a_j},{v',a_k,a_l}.
    If the pairings coincide, link(a_1) ⊇ {v,v'},{v,a_2},{v',a_2}, a triangle, not a C_4. Otherwise, say v pairs
    (a_1a_2)(a_3a_4) and v' pairs (a_1a_3)(a_2a_4): link(a_1) ⊇ {v,v'},{v,a_2},{v',a_3} forces the fourth triple
    {a_1,a_2,a_3}; then link(a_2) = {v,v'},{v,a_1},{v',a_4},{a_1,a_3} has degree-1 vertices a_3, a_4, not a C_4. ✗
  * Otherwise all pairs lie in 0 or 2 triples and |F| is a closed pseudo-manifold, singular only at v or v' when the
    link is two triangles. If both links are cycles: closed surface with chi = 11 - 24 + 16 = 3. Components: degree
    sums 4V' + 2[v in] + 2[v' in]. Spheres: V' = 6 (neither), (V'-1)/3 = 2 i.e. V' = 7 with degrees (6, 4^6) (one of
    them): the degree-6 vertex is adjacent to all 6 others, its link is a hexagon and the remaining 4 faces triangulate
    the hexagon with 3 diagonals; the six rim vertices then have degrees 3 + d_i with sum d_i = 6, and all-degree-4 needs
    d_i = 1 for all i, a perfect matching of the hexagon by non-crossing diagonals, which does not exist (every
    hexagon triangulation has an ear). Both v, v' in one sphere: (V'-2)/3 = 2, V' = 8, degree sum 36, with two degree-6
    vertices and six degree-4 vertices: v is adjacent to 6 of the 7 others; fine so far, but then the other components
    must be octahedra on the remaining 3 vertices, impossible; and V' = 11 alone gives chi = 3 ≠ 2. Projective planes:
    6V' - 6 = 4V' + 2s (s = 0,1,2) gives V' = 3, 4, 5 < 6. chi' <= 0 is excluded by Fact T. So chi = 3 ✗.
    If link(v) is two triangles, split v into v_1, v_2 of degree 3: 12 vertices, chi = 4, degrees (3, 3, 6, 4^9) if
    link(v') is a cycle — and then two spheres, since chi' <= 0 is excluded by Fact T and a projective plane needs
    6V' - 6 <= 6 + 4(V' - 1), i.e. V' <= 4 < 6 — or (3,3,3,3,4^9) with chi = 5 (odd, impossible with spheres; projective
    planes with degrees <= 4 need 6V' - 6 <= 4V', V' <= 3; chi' <= 0 excluded by Fact T) if both split. For (3,3,6,4^9): the sphere containing v'
    has 6 + 3a + 4b = 6(1+a+b) - 12, i.e. 3a + 2b = 12 with a <= 2: (a,b) = (2,3) gives 6 vertices with v' of degree 6
    (impossible, only 5 others), (0,6) gives the (6,4^6) sphere excluded above. ✗
 So delta = 0 is impossible.

All cases are exhausted: no Boolean function of degree 3 has 11 relevant variables. With Part I and Xi_3, R_3 = 10. QED.

## Remarks
- The proof shows more: any degree-3 Boolean function with all influences equal to 1/4 must be... (nothing: none exist
  beyond 10 variables). The Nisan–Szegedy bound d 2^{d-1} is tight for d = 1, 2 and off by 2 at d = 3.
- Numerical cross-check: tools/r3_search.py gen11 (CP-SAT, 11 variables, general degree <= 3 with Lemma 1's constraints)
  should return INFEASIBLE.
- Open: R_4 in [22, 32]; the CHS recursion gives R_d >= 2 R_{d-1} + 2. Conjecture (natural in view of this result):
  R_d = 3 * 2^{d-1} - 2 for all d, i.e. C44 = 3/2.

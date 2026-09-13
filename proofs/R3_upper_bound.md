# Theorem. No Boolean function of degree 3 has 12 relevant variables: R_3 <= 11.

(Fable, 2026-09-12. Tier: proof; refereed PASS by an independent Fable instance 2026-09-12 (referee/REPORT_r3.md), wording fixes applied. Numerical cross-check: CP-SAT `tools/r3_search.py hom12`.)

Setting. f : {-1,1}^n -> {-1,1}, real multilinear (Fourier) degree deg f <= 3. A variable is relevant if f depends on it.
R_d := max number of relevant variables of a degree-d Boolean function. Nisan-Szegedy: R_d <= d 2^{d-1}, so R_3 <= 12.
The CHS construction Xi_3 has 10 relevant variables, so 10 <= R_3 <= 12.

## Facts used
(NS1) Granularity: if deg f <= d then every Fourier coefficient f^(S) is an integer multiple of 2^{1-d}.
(NS2) If x_i is relevant then Inf_i(f) >= 2^{1-d}. (D_i f = (f(x^{i->1}) - f(x^{i->-1}))/2 is a nonzero {-1,0,1}-valued
      function of degree <= d-1, and a nonzero function of degree <= k on the cube is nonzero on >= 2^{-k} of the points.)
(NS3) Total influence sum_i Inf_i(f) = sum_S |S| f^(S)^2 <= deg f.

## Step 1: 12 relevant variables force a homogeneous cubic with 16 terms +-1/4, 4-regular.
With 12 relevant variables, NS2+NS3 give 3 >= sum_i Inf_i >= 12 * 1/4 = 3. Hence every Inf_i = 1/4 exactly and
sum_S |S| f^(S)^2 = 3 = 3 sum_S f^(S)^2, so all Fourier weight sits on level 3: f = sum_{|S|=3} c_S chi_S.
By NS1, n_S := 4 c_S is an integer, sum_S n_S^2 = 16 (Parseval), and Inf_i = sum_{S ∋ i} c_S^2 = 1/4 gives
sum_{S ∋ i} n_S^2 = 4 for every vertex i. So at each vertex either one term with |n_S| = 2 or four terms with |n_S| = 1.
If some S has |n_S| = 2, its three vertices lie in no other term, so f = ±chi_S/2 + g with g on the other 9 variables.
Then f^2 = 1/4 + g^2 ± chi_S g = 1; the monomials of chi_S g all contain S while those of 3/4 - g^2 avoid S, so
chi_S g = 0, i.e. g = 0, contradicting sum g^^2 = 3/4. Hence all n_S = ±1: f = (1/4) sum_{S in F} eps_S chi_S with
F a 3-uniform hypergraph on the 12 vertices, |F| = 16, every vertex in exactly 4 triples.

## Step 2: every vertex link is a 4-cycle.
Fix a vertex i. D_i f = sum_{S ∋ i} c_S chi_{S \ i} = (1/4) sum_{j=1}^4 eps_j chi_{T_j}, T_j = S_j \ {i} four distinct pairs.
D_i f takes values in {-1,0,1}. Writing u_j = eps_j chi_{T_j}(x) = ±1, we need sum_j u_j in {0, ±4} for all x,
i.e. never ±2, i.e. the number of j with u_j = -1 is always even, i.e. prod_j u_j = 1 identically:
(prod eps_j) chi_{T_1 Δ T_2 Δ T_3 Δ T_4} ≡ 1. Hence T_1 Δ T_2 Δ T_3 Δ T_4 = ∅ and prod eps_j = +1.
Four distinct pairs with empty symmetric difference: each vertex lies in an even number of them; 8 incidences;
a vertex in all four would leave the other four endpoints in one pair each; so exactly four vertices each in exactly
two pairs, i.e. the pairs form the 2-regular simple graph on 4 vertices: a 4-cycle a-b-c-d-a.
Consequently the four triples at i are {i,a,b},{i,b,c},{i,c,d},{i,d,a}: the link of i in F is C_4, and every pair
{i,x} lies in exactly 2 triples (x in {a,b,c,d}) or 0 triples (otherwise).

## Step 3: F is a closed triangulated surface with all vertex degrees 4, hence two disjoint octahedra.
Step 2 says the pure 2-complex |F| has every edge in exactly two triangles and every vertex link a single cycle (C_4),
so it is a closed 2-manifold (possibly disconnected), triangulated with V = 12 vertices, F = 16 faces, and
E = (3 * 16)/2 = 24 edges. Euler characteristic V - E + F = 12 - 24 + 16 = 4. A connected closed surface has chi <= 2,
so there are at least two components; each component is a closed surface in which every vertex has degree 4, so with
V', E' = 2V', F' = 4V'/3 it has chi = V'/3 in {1, 2}; chi = 1 would need V' = 3, impossible for a vertex of degree 4
(a projective plane needs >= 6 vertices anyway), so chi = 2 and V' = 6: the octahedron (the unique 4-regular
triangulated sphere: the complement of a 4-regular graph on 6 vertices is a perfect matching, so the graph is K_{2,2,2}
and all 8 faces are forced). Topology-free alternative: if link(i) = a-b-c-d then link(a) = b-i-d-x with x ≠ c (else
link(b) would contain a 3-cycle, impossible in a C_4), and the closure forces the octahedron on
{i,a,b,c,d,x}; checked exhaustively by the referee (referee/REPORT_r3.md). Two octahedra use all 12 vertices. Hence F = faces of two vertex-disjoint octahedra and
f = f_1(x_1..x_6) + f_2(x_7..x_12), f_1, f_2 each with 8 terms ±1/4 on disjoint variable sets, neither constant.

## Step 4: a sum of two non-constant functions on disjoint variable sets is never Boolean.
If f_1(x) + f_2(y) in {±1} for all x, y and f_1 takes two values u ≠ u', then f_2(y) in {±1-u} ∩ {±1-u'} for all y.
Two distinct two-element sets meet in at most one point, so f_2 is constant, contradicting f_2 non-constant
(it has Fourier weight 1/2 on non-constant characters). Equivalently and more directly: for disjoint triples
S ⊂ oct_1, T ⊂ oct_2 the coefficient of chi_{S ∪ T} in f^2 is 2 eps_S eps_T / 16 ≠ 0, since no other pair of triples
has that union; but f^2 ≡ 1.

Therefore no degree-3 Boolean function has 12 relevant variables. QED.

## Consequences / what is left
- R_3 in {10, 11}. The Nisan-Szegedy bound d 2^{d-1} is tight for d = 1, 2 and NOT tight for d = 3.
- For d = 4 the same start applies to 32 relevant variables (all Inf_i = 1/8, homogeneous quartic, 64 terms ±1/8 or
  structured heavier terms, each vertex link a degree-3 {0,±1}-valued function with 8 terms). Not yet analysed.
- The 11-variable case: influences >= 1/4 with sum <= 3 leaves total slack 1/4; see tools/r3_search.py gen11
  (CP-SAT with these constraints) for the decision.

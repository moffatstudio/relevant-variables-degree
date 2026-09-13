# Theorem. For every d >= 3, no Boolean function of degree d has d 2^{d-1} relevant variables: R_d <= d 2^{d-1} - 1.

(Fable, 2026-09-12. Tier: proof; refereed PASS by an independent Fable instance 2026-09-13 (referee/REPORT_ns.md), presentational fixes applied. Generalises R3_upper_bound.md (d = 3).)

Setting. f : {-1,1}^n -> {-1,1}, deg f <= d, all n variables relevant. Fourier coefficients f^(S) are integer multiples of
2^{1-d} (granularity; Nisan–Szegedy 1994, see also O'Donnell, Analysis of Boolean Functions, Ex. 1.11). For a relevant variable i, D_i f := (f(x^{i->1}) - f(x^{i->-1}))/2 is a nonzero {-1,0,1}-valued function of
degree <= d-1 with D_i f = sum_{S ∋ i} f^(S) chi_{S \ i}, and Inf_i(f) = Pr[D_i f ≠ 0] = sum_{S ∋ i} f^(S)^2 >= 2^{1-d}
(a nonzero function of degree <= k is nonzero on at least 2^{-k} of the cube: restrict to a subcube where a top monomial survives and induct; this is the standard Schwartz–Zippel-type bound used by Nisan–Szegedy 1994).
Total influence sum_i Inf_i = sum_S |S| f^(S)^2 <= d.
Write m := d - 1 and N := 2^m.

## Lemma A (minimal support forces an affine cube of unit terms).
Let q = 2^{-m} sum_{j=1}^{J} n_j chi_{T_j} with distinct sets T_j, integers n_j ≠ 0, sum_j n_j^2 = N, and suppose q is
{-1,0,1}-valued and not identically 0. Then all n_j = ±1, J = N, the family {T_j} is an affine subspace of dimension m
of F_2^n (subsets identified with 0/1 vectors), and n_j n_k n_l n_r = +1 whenever T_j Δ T_k Δ T_l Δ T_r = ∅.

Proof. Put s := 2^m q = sum_j n_j chi_{T_j}, so s takes values in {0, ±N} and E[s^2] = sum n_j^2 = N (Parseval), hence
Pr[s ≠ 0] = 1/N and E[s^4] = N^2 E[s^2] = N^3. Expanding,
   E[s^4] = sum_{(j,k,l,r): T_j Δ T_k Δ T_l Δ T_r = ∅} n_j n_k n_l n_r.
For each ordered triple (j,k,l) there is at most one r with T_r = T_j Δ T_k Δ T_l (the T's are distinct); call the set of
triples having such an r "Dom" and the index r(j,k,l). Then
   N^3 = E[s^4] <= sum_{(j,k,l) in Dom} |n_j n_k n_l| |n_{r(jkl)}|
       <= sum_{(j,k,l) in Dom} n_j^2 n_k^2 |n_l| |n_{r(jkl)}|                                      (|n| >= 1 for nonzero integers)
       <= ( sum_{Dom} n_j^2 n_k^2 n_l^2 )^{1/2} ( sum_{Dom} n_j^2 n_k^2 n_{r(jkl)}^2 )^{1/2}        (Cauchy–Schwarz)
       <= ( N^3 )^{1/2} ( N^3 )^{1/2} = N^3,
where the last step uses sum_{Dom} n_j^2 n_k^2 n_l^2 <= (sum n^2)^3 = N^3 and, for fixed (j,k), the map l -> r(j,k,l) is
injective on Dom (l is recovered from r), so sum_{l} n_{r(jkl)}^2 <= N. Equality throughout forces:
 (i) Dom = all triples: the family {T_j} is closed under (x,y,z) -> x Δ y Δ z, i.e. it is an affine subspace, of some
     dimension k with J = 2^k;
 (ii) equality in the second line forces |n_j n_k| = 1 whenever the triple contributes, and Cauchy–Schwarz equality gives
     |n_{r(jkl)}| = λ |n_l| for all j,k,l; taking j = k gives r = l and λ = 1, and for fixed k, l the map j -> r(j,k,l)
     is onto, so all |n_j| are equal to a common c (in fact c = 1 already from the second line; the argument below
     is kept because it also handles the count J);
 (iii) all products n_j n_k n_l n_{r(jkl)} are positive.
From (ii), 2^k c^2 = N = 2^m, so c = 2^t with k = m - 2t. If t >= 1 then |s| <= c 2^k = 2^{m-t} < N, so s in {0, ±N}
forces s ≡ 0, contradicting q ≠ 0. Hence c = 1, k = m, J = N. QED.

Remark. (iii) says eps_j := n_j is an affine character on the cube {T_j}: eps_{T_0 Δ A} = eps_0 psi(A) for a homomorphism
psi : L -> {±1}, where {T_j} = T_0 Δ L. Consequently q = ± chi_{T_0} prod_{i=1}^m (1 + psi(D_i) chi_{D_i})/2 for a basis
D_1..D_m of L: a minimal-support derivative is a character times the indicator of an affine subspace of codimension m.

## Lemma B (equal sizes force a cross-polytope).
Let {T_p} = T_0 Δ L be an affine subspace of dimension m of subsets, all of size exactly m. Then there are m disjoint
pairs {t_i, t_i'} with T_0 = {t_1, ..., t_m} and {T_p} = { {u_1, ..., u_m} : u_i in {t_i, t_i'} }, i.e. the facets of an
m-dimensional cross-polytope on the 2m vertices t_i, t_i'.

Proof. For A in L \ {∅} and any p: |T_p Δ A| = m = |T_p| gives |A| = 2 |A ∩ T_p|. Applying this with T_p = T_0 Δ B
(B in L): |A|/2 = |(T_0 Δ B) ∩ A| = |T_0 ∩ A| + |B ∩ A| - 2|T_0 ∩ A ∩ B|, so |A ∩ B| = 2 |T_0 ∩ A ∩ B| for all A, B in L.
The F_2-linear map L -> 2^{T_0}, A -> A ∩ T_0, is injective (A ∩ T_0 = ∅ forces |A| = 0), and both spaces have dimension m,
so it is a bijection. For t in T_0 let A_t in L have A_t ∩ T_0 = {t}; then |A_t| = 2, A_t = {t, t'} with t' ∉ T_0. For
t ≠ s, |A_t ∩ A_s| = 2|T_0 ∩ A_t ∩ A_s| = 0, so the t' are distinct. The A_t form a basis of L, and
T_0 Δ (Δ_{t in P} A_t) = (T_0 \ P) ∪ {t' : t in P}. QED.

## Lemma C (disjoint sums). If g(x) + h(y) in {±1} for all x, y (disjoint variable sets) and g is not constant, then h is
constant. Proof: h(y) lies in {±1 - u} ∩ {±1 - u'} for two distinct values u, u' of g, a set of size <= 1.

Fact (cross-polytopes). The facet family of an m-dimensional cross-polytope determines its antipodal pairs: two vertices are
antipodal iff they never occur in a common facet (every non-antipodal pair lies in a common facet). We use this to read off
the pairs of a link from its facets.

## Proof of the Theorem.
Suppose deg f <= d and f has n = d 2^{d-1} relevant variables. Then d >= deg f >= sum_i Inf_i >= n 2^{1-d} = d, so
deg f = d exactly, every Inf_i = 2^{1-d}, and all Fourier weight lies on level d: f is a homogeneous degree-d polynomial,
f = sum_{|S| = d} c_S chi_S.
Fix a relevant variable i and write D_i f = 2^{-m} sum_{S ∋ i} n_S chi_{S \ i} with n_S := 2^m c_S in Z (granularity).
Then sum_{S ∋ i} n_S^2 = 2^{2m} Inf_i = 2^m = N, D_i f is {-1,0,1}-valued and nonzero, and the sets S \ i (i fixed) are
distinct. Lemma A gives: every n_S with S ∋ i equals ±1 — hence every coefficient of f is ±2^{-m} and f has exactly
2^{2m} terms, forming a d-uniform hypergraph F in which every vertex lies in exactly N = 2^{d-1} terms — and the link
lk(i) := {S \ i : S in F, S ∋ i} is an affine m-dimensional subspace of m-sets. By Lemma B, lk(i) is the facet set of an
m-dimensional cross-polytope: there are m disjoint pairs P_1(i), ..., P_m(i) of vertices ("antipodal pairs at i") and
the terms at i are exactly {i} ∪ {one vertex from each P_k(i)}. In particular two antipodal vertices at i never lie in a
common term with i, and i has exactly 2m neighbours.

Closure. Fix v with pairs P_k = {t_k, t_k'}, k = 1..m (m >= 2 since d >= 3). Let a := t_1. The terms at v containing a
are {v, a} ∪ (one from each P_2, ..., P_m); removing a, these are 2^{m-1} facets of the cross-polytope lk(a), all
containing v, so by the Fact the pairs of lk(a) are P_2, ..., P_m together with a pair {v, w} for a unique vertex w
("antipode of v at a"). w ∉ {v} ∪ P_2 ∪ ... ∪ P_m, and w ≠ t_1' : otherwise the term {a, t_1', t_2, t_3(or t_3'), ...} exists, and
removing t_2 it is a facet of lk(t_2) containing both a = t_1 and t_1', which are antipodal at t_2 (the terms at v
containing t_2 show that P_1 is a pair of lk(t_2)) — impossible. So w is a new vertex. The terms at a are
{a} ∪ {v or w} ∪ (one from each P_2..P_m); in particular {a, w, t_2, u_3, ..., u_m} is a term, so removing t_2 gives a
facet of lk(t_2) containing a and w; the pairs of lk(t_2) are P_1, P_3, ..., P_m and {v, w_2} (w_2 the antipode of v at
t_2), so w = w_2. Symmetrically the antipode of v at every t_k and t_k' equals w, hence w is adjacent to all 2m vertices
of P_1 ∪ ... ∪ P_m; these exhaust the 2m neighbours of w and the terms at w are {w} ∪ (one from each P_k). Therefore the
component of v in F is exactly the boundary of the d-dimensional cross-polytope on {v, w} ∪ P_1 ∪ ... ∪ P_m: 2d vertices,
2^d facets, and no other term touches these vertices (every vertex's 2^{d-1} terms are accounted for).

Hence F is a disjoint union of 2^{2m}/2^d = 2^{d-2} >= 2 cross-polytope boundaries on disjoint vertex sets, and
f = f_1 + g with f_1 = 2^{-m} sum_{facets of the first cross-polytope} ± chi_S on its 2d variables and g on the rest.
Both are non-constant (each carries positive Fourier weight on non-constant characters), contradicting Lemma C.
Therefore no degree-d Boolean function has d 2^{d-1} relevant variables. QED.

## Remarks
- d = 2 is the exception (2^{d-2} = 1 component): the square's four edges with signs (+,+,+,-) give the 4-variable
  degree-2 function (x_1x_2 + x_1x_3 + x_2x_4 - x_3x_4)/2, so R_2 = 4 = d 2^{d-1}.
- Together with R3_equals_10.md: R_3 = 10, and R_d <= d 2^{d-1} - 1 for all d >= 3.
- Lemma A applies to any variable of minimal influence 2^{1-d} in any degree-d Boolean function (no homogeneity needed):
  its derivative is a character times the indicator of an affine subspace of codimension d-1 (Remark after Lemma A).
  This is the structural handle for pushing the upper bound further.

# Referee report - R3_equals_10.md, round 2c (prose), independent Fable instance, 2026-09-13

Target: R3_equals_10.md (post round-1 patches). Read first: R3_upper_bound.md (PASS), REPORT_r3_full.md (round 1).
Scripts: referee/round2c_check.py -> referee/round2c_out_check.txt.

## Verdict: PASS-with-fixes

No fatal error and no counter-configuration found. The case tree (delta in {4,2,0}, sub-cases by lower-order weight
partition, link shapes L1-L4, and the topological sub-cases) is complete and every branch closes. The round-1 bug
("link contains EMPTY => L2") is gone: every occurrence of EMPTY in a link (lines 31, 49, 60, 88-90, 101) now branches
on L2 vs L4 or uses "no quadratics => L4". The fixes below are one minor gap (Euler characteristic <= -1 components
are never named) and presentational items.

## Findings

1. [gap, minor] Line 119-123 (C_8 case): "sphere needs ... projective plane needs ... torus/Klein bottle need 6V',
   V' = 0 or 2. So chi = 3 cannot be realised." Components with chi' <= -1 are not excluded, and 2 + 2 + (-1) = 3 is
   a formally open decomposition. The same omission is at line 157-158 ("Torus/Klein: 6V' = 4V' + 2s gives V' <= 2")
   and, by wording, at lines 133 and 160 ("a torus needs average degree 6" names chi' = 0 only) and 161-162
   ((3,3,3,3,4^9): only spheres and projective planes are discussed).
   Patch (insert once before "## Case delta = 0", then cite it in the four places):
   "Fact T. In a closed connected triangulated surface with V' vertices, E' edges, F' faces and Euler characteristic
   chi', 3F' = 2E' and V' - E' + F' = chi' give degree sum 2E' = 6V' - 6chi'. Hence chi' <= 0 forces average degree
   >= 6. In every complex below all degrees are 4 except at most two vertices of degree <= 8, so the average degree
   is <= 4 + 8/V' < 6 as soon as V' >= 5, and V' >= 5 holds because some vertex has degree >= 4. So every component
   is a sphere (degree sum 6V' - 12) or a projective plane (degree sum 6V' - 6, and at least 6 vertices)."
   Then replace "torus/Klein bottle need 6V', V' = 0 or 2" (line 123), "Torus/Klein: ... V' <= 2" (line 158),
   "a torus or Klein bottle needs average degree 6" (line 133), "a torus needs average degree 6" (line 160) by
   "chi' <= 0 is excluded by Fact T", and add "; chi' <= 0 excluded by Fact T" after "projective planes with degrees
   <= 4 need 6V' - 6 <= 4V', V' <= 3" (line 162). Verified: round2c_out_check.txt section D lists V' = 3chi' + c/2
   for every degree pattern used; all chi' <= 0 rows give V' <= 2.

2. [presentational] Line 116-117: "If some x has lambda_{vx} = 4, then v has degree 4 in link(x), so link(x) is not
   a C_4, so x = v." x is a vertex of link(v), hence x != v; the conclusion is a contradiction, not "x = v".
   Patch: "... so link(x) is not a C_4, contradicting m_x = 4 (x != v). Hence link(v) is 2-regular: ..."

3. [presentational] Line 133-135 (C_3 u C_5): "a projective plane needs degree sum 6V' - 6, which with all degrees
   <= 5 forces V' <= 6, and the only 6-vertex projective plane has all six degrees equal to 5". V' < 6 is excluded
   only by the unstated fact that a triangulated projective plane has >= 6 vertices (it is stated in Part I, Step 3).
   Patch: append "(and a triangulated projective plane has at least 6 vertices, Part I Step 3)". Also the sharper
   count 6V' - 6 <= 4V' + 1 gives V' <= 3 directly, if preferred.

4. [presentational] Line 79-83 (|N| = 3, second case): "the third cubic is {a,b,c}" is asserted without the reason
   (i and j already carry their two cubics {i,j,a},{i,j,b}, so the third cubic contains neither; a and b each need a
   second cubic, so it is {a,b,c}). In fact the case dies one step earlier: link(a) contains {i,j} from {i,j,a}, but
   L3 at a is {{i},{j},{i,c_a},{j,c_a}}, so {i,j} = {i,c_a} forces c_a = j, not a 3-set. Patch: replace "Second: then
   a and b each lie in one inside cubic and the third cubic is {a,b,c}; link(a) = ..." by "Second: link(a) contains
   the pair {i,j} (from {i,j,a}), but L3 at a has pairs {i,c_a},{j,c_a} with c_a notin {i,j}. X" (the existing
   argument is also valid once the reason for {a,b,c} is added).

5. [presentational] Line 124-127 (C_4 u C_4): the sub-case "v_1, v_2 lie in the same octahedron" is vacuous: the two
   C_4's of link(v) are vertex-disjoint, so v_1, v_2 have disjoint neighbourhoods, whereas two vertices of an
   octahedron are adjacent (impossible: no triple contains v twice) or antipodal (sharing all four neighbours). The
   given disjoint-sum argument is nevertheless correct; optionally add "(this sub-case is in fact empty, since the
   two C_4's are vertex-disjoint)".

6. [presentational] Lines 55-57 and 77-78 (disjoint-sum conclusions): the reader must supply "each of the five
   vertices has m = 4 and its four listed terms exhaust it, so no other term meets {i,j,a,b,c}". Stated in the {2,2}
   case ("exhaust the vertices"); in |N| = 4 only m_c is said to be exhausted. Patch: after "m_c = 4 is exhausted"
   add "and i,a,j,b are exhausted (two quadratics and two cubics each)".

7. [presentational, optional] Line 14-18, Lemma 1: the case list is complete (m <= 8 forces |n_j| <= 2; m = 5 is
   {2,1} or five 1's, m = 7 is {2,1,1,1} or seven 1's, m = 6 is {2,1,1} or six 1's). A one-line remark "m_i is even:
   4 D_i f is {0,+-4}-valued and sum n_j = sum n_j^2 = m_i (mod 2)" would replace the four-pattern parity list.

## Interpretation of referee/round2b_out_lemma1.txt against Lemma 1
Weights (2,): 0 realisable = Lemma 2(d) (a lone +-2 is never {0,+-4}-valued). (2,1): 0 = no m = 5 with a +-2.
(2,1,1): 0 = m = 6 never contains a +-2 (the proof's u_1 = u_2 argument). (2,1,1,1): 0 = no m = 7 with a +-2.
(2,2): 1848 = C(22,2) * 2 * 4 = every ordered/signed pair of distinct sets, i.e. all realisable = Lemma 2(c) first
alternative. The all-+-1 patterns for m = 5, 7 are excluded by parity (odd sum), not by the brute force. The
(2,1,1,1,1) line is absent from the output file (script did not finish), which is harmless: the proof never uses
that pattern (a +-2 cubic needs m = 8 at three vertices; delta = 0 has at most one m = 8 vertex). Together with
lean/R3/Mass.lean (mass in {4,6,8}, >= 9 mass-4 vertices) Lemma 1 is certified. Supports the lemma.

## Link classification against round2b_out_links.txt / round2_out_links.txt / round2c_out_check.txt
k = 4: exactly 4 shapes = L1 (C_4), L2 ({},{a},{b},{a,b}), L3 ({a},{b},{a,c},{b,c}), L4 ({} + triangle). Complete.
k = 6, EMPTY and no singletons: only EMPTY + C_5 (line 101). k = 6 pairs only: bowtie (4,2,2,2,2), C_3+C_3, C_6
(lines 89, 113-114). k = 8 pairs only: 7 classes, of which 2-regular: C_8, C_3+C_5, C_4+C_4, and 4 with a
degree-4 vertex (line 116-117). All match the proof.

## Consistency of the case tree with the structure searches (not redone)
round2_out_search.txt / round2b_out_search.txt find exactly three isomorphism classes of link-consistent 16-term
supports on 11 vertices: the delta = 4 {2,2}-L4 + octahedron, the delta = 4 {1,1,1,1} |N| = 4 + octahedron, and the
glued octahedra (delta = 0, C_4 u C_4). These are precisely the three branches the proof closes with the disjoint-sum
lemma; every other branch is closed at the link level in the proof and reported INFEASIBLE by the SAT search. The
exhaustive F(11) search (search/log2_n11_s*.txt, 0 solutions) is independent confirmation of the theorem.

## Verified by hand
Lemma 1 case list and parity; Lemma 2(a)-(e) (value-set arguments for 4, 6, 8 terms; 2(d) and its consequence);
bookkeeping e + delta = 4 and e in {0,2,4}; the five weight partitions of delta = 4 and each branch ({4}, {2,2}
including the j in {a,b,c} sub-branch and the w = w' = w'' argument, {3,1}, {2,1,1} both L2 and L4 branches,
{1,1,1,1} counting k = 3|N| - 8, |N| = 4 and both |N| = 3 symmetry classes); delta = 2 (linear term: m_l = 4 with
v notin {a,b,c} and v in {a,b,c}, m_l = 6 five-cycle; two quadratics); delta = 0 degree sequences, no +-2, link lists,
lambda argument, closed pseudo-manifold claims, C_8 / C_4uC_4 / C_3uC_5 Euler counts, glued-octahedra
non-constancy of g_1(1, y), bowtie pairing argument, (6,6) both-cycles sphere counts, split (3,3,6,4^9) and
(3,3,3,3,4^9) counts, pentagon and hexagon triangulation claims.

## Verified by computation (referee/round2c_check.py -> round2c_out_check.txt, 8 s)
A: link shapes k = 4 (4 shapes = L1..L4), k = 6 with EMPTY and no singletons (EMPTY + C_5 only), k = 6 pairs only
(bowtie, C_3+C_3, C_6). B: 5-cycle step, all 7^5 = 16807 choices of the fourth link vertices w_1..w_5 over 11
vertices: 0 completions with every a_k link a C_4 and every m <= 4. C: pentagon triangulations have diagonal
degrees (2,1,1,0,0) only, hexagon triangulations never a perfect matching. D: V' = 3chi' + c/2 table (Finding 1).

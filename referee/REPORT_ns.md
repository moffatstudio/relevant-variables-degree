# Referee report - NS never tight for d >= 3 (mgr-referee-ns2, independent Fable instance, 2026-09-13)
Transcribed by the captain (subagent report-file write was blocked). Scripts: referee/ns_lemmaA.py, referee/ns_crosspolytope.py,
output referee/out_ns_lemmaA.txt.

VERDICT: PASS. No false step, no missing case. Two presentational points, neither affecting validity.

Independent framing: extremal f must have every Inf_i = 2^{1-d}, be homogeneous of degree d, have coefficients in 2^{1-d} Z,
and each D_i f {-1,0,1}-valued with support density exactly 2^{1-d}. Failure modes looked for: a minimal-support lemma
mishandling non-unit coefficients or non-affine Fourier supports; no genuine link-to-global closure argument; an argument that
also kills d = 2. The proof matches this framing point for point and survives all three.

(a) Lemma A correct. The Cauchy-Schwarz display hides a step (|n_j n_k| <= n_j^2 n_k^2, or Sum_Dom n_r^2 <= J^2 N <= N^3 via
J <= N); both readings give the stated equality analysis. Sign statement and Remark correct; the Remark also gives the converse.
Lemma A uses no degree hypothesis (pure Fourier-sparsity statement).
(b) Lemma B correct in every step.
(c) Theorem correct. Closure steps w != t_1' and w = w_2 check; they need t_2 to exist (m >= 2). "Pairs of lk(a) are P_2..P_m
and {v,w}" relies on the (now stated) fact that a cross-polytope's antipodal pairs are recoverable from its facet family.
Component count 2^{d-2} >= 2 and Lemma C application fine.
(d) d = 2 not excluded: closure needs m >= 2 and 2^{d-2} = 1 leaves Lemma C inapplicable; d >= 3 enters exactly there.

Checks run: ns_lemmaA.py - exhaustive Lemma A for m = 2 (ground sets 3, 4) and m = 3 (ground set 4 full; 5 with WLOG T_1 = empty),
343M instances, 0 violations; valid counts 112, 1120, 480, 1240 match (affine flats) x (admissible signs) exactly (14x8, 30x16).
ns_crosspolytope.py - octahedron (2^8 signs, coefficient 1/4) and 16-cell (2^16 signs, coefficient 1/8) never Boolean; square
(+,+,+,-) with coefficient 1/2 Boolean; exhaustive d = 3 extension with all links C_4 completes only to the octahedron.

Novelty (referee's view): NS94 does not discuss tightness for d >= 3. CHS20 and Wellens beat d 2^{d-1} only for d >= 14 resp.
d >= 9, so for 3 <= d <= 8 this is a genuine improvement by one, and the non-attainment statement appears new. Lemma A
(minimal-influence derivative = character x indicator of a codim-(d-1) affine subspace, no homogeneity needed) is the reusable
content; check Wellens' small-d remarks and the Fourier-sparsity structure literature for overlap.

CORRECTION (2026-09-15, raised by the VibeMathed curator, verified against arXiv:1903.08214v2): Wellens' Table 2 bounds
W(f) <= 3.9375 at d = 8, so R_8 <= 1008 < 8 * 2^7; non-attainment was already known for every d >= 8. The genuinely new
range is 3 <= d <= 7. The paper's introduction and related-work section were corrected accordingly.

Presentational fixes requested (all applied 2026-09-13): rewrite the CS step; state the pairs-from-facets fact; cite granularity
and the 2^{-k} support bound; note deg f = d is forced.

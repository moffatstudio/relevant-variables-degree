# Referee report — R_3 <= 11 (Part I)
Referee: independent Fable instance (mgr-referee-r3), 2026-09-12. The subagent could not write this file itself; the captain
transcribed its returned report verbatim where available.

**Verdict: PASS.**

Independent analysis (written before reading the proof) reached the same route: support bound for degree<=2 derivatives gives
Inf_i >= 1/4; total influence <= 3 forces 12 variables to be a homogeneous cubic with every Inf_i = 1/4; granularity (all
coefficients in (1/4)Z, downward induction on |S|) gives per-vertex options "one ±1/2" or "four ±1/4"; the ±1/2 vertex is
killed by D_i f = ±chi_T/2; four ±1/4 pairs with {-1,0,1}-valued sum force empty symmetric difference, hence a C4 link;
C4 links everywhere force octahedral components (also provable without topology); a sum of two non-constant functions on
disjoint variables is never Boolean.

Findings: (a) OK (standard fact, cited). (b) OK, exact equivalence. (c) OK. (d) OK with omission: chi = V'/3 also allows
chi = 1, V' = 3, must be excluded explicitly (degree 4 needs >= 5 vertices); octahedron uniqueness true but unjustified
(complement of a 4-regular graph on 6 vertices is a perfect matching -> K_{2,2,2}). (e) Minor false sentence "for any other
pair it is empty" (u = 3/2, u' = -1/2 gives {-1/2}); conclusion survives since the intersection has <= 1 element; the
chi_{S∪T}-coefficient argument is fully correct and should be primary. (f) OK.
[Both (d) and (e) fixed in R3_upper_bound.md on 2026-09-12.]

Checks run by the referee (scripts in referee/, if the write succeeded): Step 2 brute force over all 20475 4-sets of distinct
pairs on 8 vertices x 16 signs: {-1,0,1}-valued <=> C4 and even sign product, 0 mismatches; Step 3 exhaustive growth search:
every complex with all links C4 has the octahedron as the component of any vertex; Step 4: all 65536 sign patterns on two
octahedra, none Boolean.

Novelty (referee's view): not known to them; Nisan-Szegedy, CHS (arXiv:1801.08564) and Wellens (arXiv:1903.08214, Table 2)
all give exactly 12 at d = 3; none mentions exact small-d values.

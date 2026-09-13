# Referee report: lean/DELTA0_TOPOLOGY_FREE.md (topology-free delta = 0)

Referee pass, 2026-09-13, adversarial. Background read: R3_upper_bound.md, R3_equals_10.md,
lean/R3/DeltaZero.lean (pair_second, pair_not_three, closure_kills), lean/R3/Octahedron.lean
(link_cycle, link_struct, LinkIs).

## Verdict: PASS-with-fixes  (round 1; confirmed and extended by round 2 below)

Lemma Y, Corollary Y' and Lemma A are correct as stated. One step of the (6,6,4^9) case
analysis is wrong as written and drops a configuration the old topological proof handled
(the bowtie). It is repairable without topology, but the note must not enter the paper or
Lean as it stands.

## Findings

### 1. (gap, must fix) (6,6,4^9): "the degree sum 12 forces deg(w) even: deg(w) in {0,2}"

Line 61. Invalid inference: deg(w) + 2t = 12 makes deg(w) even, which leaves {0,2,4,6}.

- deg(w) = 6 is impossible, but for another reason: all six edges at w leave every other
  link vertex of degree 1, not 2. Say so.
- deg(w) = 4 is not excluded by anything in the note, and is realisable: link(v) is the
  BOWTIE (w adjacent to a_1..a_4 plus a perfect matching on the a_i). Confirmed by
  exhaustive enumeration, referee/delta0_out_links.txt section (B): the shapes meeting
  exactly the stated constraints are C_6, C_3+C_3 (deg(w) in {0,2}) and the bowtie.

pair_not_three cannot be applied to the pair {v,w}: both endpoints have mass 6 and the Lean
lemma needs mass 4 at one endpoint. The rest of the (6,6,4^9) analysis assumes link(v) is
2-regular, so the bowtie is a real hole.

Not fatal: the bowtie is killed by the first bullet of the (6,6,4^9) sub-case of
R3_equals_10.md, which uses only link shapes. Proposed patch, before the current first
bullet:

> Every pair {v,x} with x != w has a mass-4 endpoint, so lambda_{vx} in {0,2}: every vertex
> of link(v) other than w has degree 2. With 6 edges, deg(w) + 2t = 12, so deg(w) is even.
> deg(w) = 6 is impossible (all six edges at w leave the other link vertices of degree 1).
> If deg(w) = 4 then, by the edge count, link(v) is the bowtie: w adjacent to a_1..a_4 plus
> a perfect matching on the a_i. Then lambda_{vw} = 4, so v has degree 4 in link(w); link(w)
> has 6 edges and all its vertices except v have degree 2, so by the same count link(w) is a
> bowtie centred at v on the same a_1..a_4 (the vertices of the four triples v w a_k). Say v
> pairs (a_1a_2)(a_3a_4), giving triples v a_1 a_2 and v a_3 a_4.
> - Same pairing at w: link(a_1) contains {v,w} (from v w a_1), {v,a_2} (from v a_1 a_2) and
>   {w,a_2} (from w a_1 a_2), a triangle; but m_{a_1} = 4, so link(a_1) is a 4-cycle, which
>   has no triangle. Contradiction.
> - Different pairing, say w pairs (a_1a_3)(a_2a_4): link(a_1) contains the path
>   a_2 - v - w - a_3, so its fourth edge closes the 4-cycle, {a_2,a_3}, i.e. a_1 a_2 a_3 is
>   a support triple. Then link(a_2) contains {v,w}, {v,a_1}, {w,a_4}, {a_1,a_3}, in which
>   a_3 and a_4 have degree 1, so it is not a 4-cycle. Contradiction.
> Hence deg(w) in {0,2} and link(v) is 2-regular with 6 edges.

The remaining pairing (a_1a_4)(a_2a_3) is the second case after relabelling.

### 2. (presentational) (8,4^10), C_4+C_4: y' not in {a_i} is not checked

Line 56 checks y not in {b_j} and y != y', but not the symmetric y' not in {a_i}, needed for
"11 distinct vertices". Patch: each a_i already lies in four triples (v a_{i-1} a_i,
v a_i a_{i+1}, y a_{i-1} a_i, y a_i a_{i+1}) and has mass 4, so it is exhausted; y' = a_i
would add the four triples y' b_j b_{j+1}, exceeding mass 4.

### 3. (presentational) Lemma Y: the proof that y not in C is loose

Line 26 argues "if y = z_j then z_j z_{j+1} y is not a 3-set". Airtight version: y = y_i for
a mass-4 z_i, and y_i is the fourth vertex of the 4-cycle link(z_i), so
y_i not in {v, z_{i-1}, z_i, z_{i+1}}. For an arbitrary z_m pick an edge of C at z_m whose
other endpoint has mass 4 (one exists, at most one vertex of C is exceptional); the y from
that endpoint's link avoids z_m.

### 4. (presentational) Lemma Y: spell out the chaining when w sits on C

The worry that y_i = y_{i+1} fails to close around w is unfounded. The mass-4 vertices of C
form a path (C minus the single exception w = z_j); every consecutive pair on that path gives
y_i = y_{i+1}, so all y_i with i != j coincide. The two edges at w are then covered by their
mass-4 endpoints' links (w is a neighbour of v and of y in each). Nothing has to close
through w, so the statement needs no weakening. Also, the notation z_0 = z_k =: w on line 16
is confusing; say "at most one z_i, call it w".

### 5. (presentational) k >= 3 is used silently

The step link(z_i) = z_{i-1} - v - z_{i+1} - y_i - z_{i-1} needs z_{i-1} != z_{i+1}, i.e.
k >= 3. True for cycle components of a simple graph, but record it as a hypothesis for Lean.

### 6. (checked, no issue) everything else

- Lemma A: the sign-difference identities and the "P' nonzero somewhere" step are correct.
- Corollary Y': correct. A 4-cycle contains a k-cycle as an edge subset only for k = 4
  (k = 3: three edges of C_4 form a path; k in {5,6,8}: too many edges), and then all four
  edges, so link(y) = C. The word "exactly" is not load-bearing anywhere: the C_4+C_4 bullet
  uses the mass count instead, so Y' could conclude just "k = 4".
- (8,4^10) 2-regularity of link(v): correct. x != v has mass 4, so lambda_{vx} in {0,2} by
  pair_second + pair_not_three; 8 edges since m_v = 8; a 2-regular simple graph is a disjoint
  union of cycles of length >= 3, and C_8, C_3+C_5, C_4+C_4 is the complete list (verified,
  delta0_out_links.txt section A; the 6-edge list C_6, C_3+C_3 is complete too, section C).
- (6,6,4^9) closing bullet: correct. A = {v,w} union V(L) has 8 vertices (w not in link(v) by
  the first bullet), all exhausted by the 12 triples v e, w e, so no triple crosses A; the
  remaining 4 triples live on 3 vertices, which admit a single 3-subset, while support sets
  are distinct.
- "y = w when k in {3,6}": correct; add the half-sentence "this degree sequence has no mass-8
  vertex, so m_y in {4,6}, and m_y != 4 leaves y in {v,w}; y != v by Lemma Y".
- Use of "all coefficients +-1": declared in the preamble, justified by Lemma 2(d) plus "at
  most one mass-8 vertex while a +-2 term needs three". Nothing beyond that is used. Lemma A
  does not even need +-1: any nonzero integer coefficients give sum_a P'(a)^2 > 0.
- Remark on Part I Step 3: correct as a remark.

## Verified by hand

Lemma Y (including the exceptional vertex on C), Corollary Y', "exactly two triples through
{z_i,z_{i+1}}", y not in C union {v}, the Lemma A identities, the 11-vertex / 16-triple
bookkeeping of the C_4+C_4 bullet, the closure ending (6,6,4^9), and the bowtie refutation
offered in finding 1.

## Verified by computation

- referee/delta0_lemmaA.py -> delta0_out_lemmaA.txt: over |alpha|,|beta|,|gamma| <= 20 the
  eight equations (+-alpha +-beta +-gamma)^2 = 16 have exactly six solutions, (+-4,0,0),
  (0,+-4,0), (0,0,+-4); all satisfy alpha(beta+gamma) = beta(alpha+gamma) = gamma(alpha+beta)
  = 0 and alpha^2+beta^2+gamma^2 = 16, and none has beta and gamma both nonzero. For every
  c' in {+-1}^4, P'(a) = sum c'_i a_i a_{i+1} is nonzero at 4 of the 16 points and
  sum_a P'(a)^2 = 64.
- referee/delta0_links.py -> delta0_out_links.txt: (A) 2-regular, 8 edges -> exactly
  {C_8, C_3+C_5, C_4+C_4}; (C) 2-regular, 6 edges -> exactly {C_6, C_3+C_3}; (B) 6 edges with
  one distinguished vertex w of free degree and all others of degree 2 -> deg(w) in {0,2,4},
  the 4 being the bowtie. That is finding 1.
- referee/delta0_search.py: RETRACTED by round 2. This script never ran to completion (it
  exceeds 15 minutes and emits no output); the claim it supported was unsupported. Round 2
  replaces it with referee/delta0_seeded.py, which terminates. See the round-2 section.

## Bottom line

Fix finding 1 (the bowtie) and the note is correct and complete; findings 2-5 are wording.
Warn the Lean lane that the (6,6,4^9) branch as written cannot be formalised: it needs the
extra bowtie lemma ("a mass-6 link with a degree-4 vertex is a bowtie") plus the two
link(a_i) contradictions.

---

# Round 2 (independent re-referee, 2026-09-13)

A second referee re-derived every step by hand from R3_upper_bound.md, R3_equals_10.md,
lean/R3/DeltaZero.lean (`pair_second`, `pair_not_three`, `closure_kills`) and
lean/R3/Octahedron.lean (`link_cycle`), and re-ran or replaced every computation.

## Verdict (round 2): PASS-with-fixes — finding 1 confirmed as the only real gap.

## Confirmations

- **Finding 1 (the bowtie) is real and is the only substantive defect.** Reproduced
  independently: `deg(w) + 2t = 12` gives only `deg(w)` even. `deg(w) = 6` forces every
  other link vertex to degree 1; `deg(w) = 4` forces a perfect matching on `w`'s four
  neighbours, i.e. the bowtie, which nothing in the note excludes. `pair_not_three` in
  DeltaZero.lean does require `mass x = 4` at an endpoint, so it cannot be applied to the
  pair `{v, w}`. Round 1's proposed patch text is correct and is confirmed computationally
  (below). It is the right fix; adopt it verbatim.
- Findings 2-5 re-checked and agreed, all presentational.
- Lemma Y: the chaining is sound with the exception `w` on `C`. The mass-4 vertices of `C`
  form a path, consecutive pairs give `y_i = y_{i+1}` along it, so all coincide; the two
  edges at `w` are covered by their mass-4 endpoints' links. `y_1 = y_{k-1}` is therefore
  established, and NO weakening of the conclusion is needed.
- Corollary Y': correct. `k = 4` because a 4-cycle contains no triangle and has only 4
  edges. The word "exactly" IS load-bearing in the C_4+C_4 bullet (it is what exhausts `y`
  and gives the 16-triple count), so keep it.
- Lemma A: identities and the "P' nonzero somewhere" step verified by hand and by brute
  force. Lemma A needs only nonzero integer coefficients, not +-1.
- No silent use of "all coefficients +-1" beyond Lemma 2(d) and the mass = degree identity.

## New findings

### 7. (presentational, round-1 report) a cited computation did not exist
`referee/delta0_out_search.txt` was claimed in round 1 but was never produced;
`delta0_search.py` does not terminate within 15 minutes. Retracted above and replaced.

### 8. (strengthening, optional) both branches can cite a terminating exhaustive search
`referee/delta0_seeded.py` seeds on the link of the exceptional vertex (a step the note
derives itself, and for (6,6,4^9) it enumerates ALL 15 canonical link shapes including the
bowtie, so it does not assume the step under dispute) and completes by DFS:
- **(8,4^10)**: C_8 and C_3+C_5 admit NO completion at all; only C_4+C_4 does, giving 630
  distinct hypergraphs, and all 630 are exactly the glued-octahedra configuration of
  Lemma A (checked by shape). So the note's structural reduction is exactly right and
  Lemma A is genuinely load-bearing: it is the only thing standing between the note and a
  surviving configuration.
- **(6,6,4^9)**: ZERO completions from any of the 15 link shapes. The whole branch,
  bowtie included, is combinatorially empty.

## Verified by computation (round 2)

- `delta0_bowtie.py` -> `delta0_out_bowtie.txt`: with `lambda(v,w) = 4` forced, exactly 6
  local structures survive the pair caps, the partial-link-in-C_4 test and the
  `lambda in {0,2}` parity at the completed mass-6 links; all 6 are bowtie-at-v plus
  bowtie-at-w on the same four vertices with DIFFERENT pairings (the same-pairing cases die
  on the triangle in `link(a_1)`, exactly as round 1's patch says). Forced-closure
  propagation (link(a_1) has a 3-edge path, so the C_4 forces the fourth edge) kills all 6.
  This is round 1's patch argument, machine-checked.
- `delta0_seeded.py` -> `delta0_out_seeded66.txt` and stdout: finding 8 above.
- `delta0_lemmaA.py` re-run, plus an independent brute force over `|alpha|,|beta|,|gamma|
  <= 8`: the eight equations `(+-alpha+-beta+-gamma)^2 = 16` have exactly the six solutions
  `(+-4,0,0), (0,+-4,0), (0,0,+-4)`; all satisfy `alpha*beta = alpha*gamma = beta*gamma = 0`
  and `alpha^2+beta^2+gamma^2 = 16`; none has `beta` and `gamma` both nonzero; `3k^2 = 16`
  has no integer solution. For all 16 sign patterns `c'`, `sum_a P'(a)^2 = 64` and `P'` is
  nonzero at 4 of the 16 points.
- `delta0_links.py` re-run: 2-regular with 8 edges -> exactly {C_8, C_3+C_5, C_4+C_4};
  with 6 edges -> exactly {C_6, C_3+C_3}; 6 edges with one free-degree vertex -> deg in
  {0, 2, 4}, the 4 being the bowtie.

## Bottom line (round 2)

Apply round 1's finding-1 patch and the wording fixes 2-5; then the note is correct and
complete, and is a genuine topology-free replacement. Until the patch lands, the Lean lane
must not treat the (6,6,4^9) branch as written: it needs the extra bowtie lemma and the two
`link(a_i)` contradictions.

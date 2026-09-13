# The case delta = 0 of F(11): the Lean route, in prose

(Fable, 2026-09-13. This is a complete prose rendering of the argument that
`lean/R3/DeltaZero.lean` actually formalises, culminating in `eleven_delta_zero`. It
replaces the topological "Case delta = 0" of `R3_equals_10.md` and the whole of
`lean/DELTA0_TOPOLOGY_FREE.md`. Every step carries the name of the Lean theorem that
certifies it, in brackets. No topology, no cycle classification, no Euler characteristic,
no bowtie case.)

## 0. Setting and notation

Notation is that of `R3_upper_bound.md` and `R3_equals_10.md`, in the finite form frozen in
`lean/R3/Statement.lean`. A *solution on n variables* is an integer vector
(n_S)_{S subset of [n]} supported on sets of size at most 3 such that

* (i) sum_S n_S^2 = 16                                            [`CondI`]
* (ii) for every nonempty U, sum over ordered pairs (S,T) with S xor T = U of n_S n_T = 0
                                                                  [`CondII`]
* (iii) every vertex lies in some set with n_S nonzero            [`CondIII`]

Condition (ii) is exactly "f^2 = 1 has no chi_U term". We write N for the vector,
`IsSol n N` for the conjunction, and `Cubic n N` for "every set with n_S nonzero has
exactly three elements"; delta = 0 is by definition `Cubic 11 N`. A *support triple* is a
3-set S with n_S nonzero; we write {x,y,z} for it. The *mass* of a vertex v is
m_v = sum over S containing v of n_S^2 [`mass`], and `supp n N v` is the set of support
sets containing v.

Throughout, **ordinary** means "of mass 4" and **exceptional** means "possibly of mass
other than 4". In the endgame there are exactly two exceptional vertices v and w.

Two standing facts about an ordinary vertex, both from Lemma 2(a) of `R3_equals_10.md`:

* **(M1)** A vertex of mass 4 lies in exactly four support sets [`mass_four_card`], and
  every coefficient on them is +1 or -1 [`mass_four_pm`]. Consequently, if
  four *distinct* support sets at v are exhibited, they are all of them
  [`supp_eq_quad`], and a fifth is impossible [`no_fifth_supp`].
* **(M2)** For a vertex v of mass 4 with support sets S1, S2, S3, S4 (pairwise distinct),
  S1 xor S2 xor S3 xor S4 = empty and n_{S1} n_{S2} n_{S3} n_{S4} = +1 [`mass_four`].
  The second half is the *sign relation* at v; it is the only place the signs enter, and it
  is what makes the whole route work.

Under `Cubic`, (M1) says the link of an ordinary vertex v (the four sets S minus v) is a
4-cycle of pairs, p-q-r-s-p; we write `LinkIs n N v p q r s` for "the support triples at v
are exactly v together with an edge of that 4-cycle" [`LinkIs`, `Edge`]. In particular
every pair through an ordinary vertex lies in exactly 0 or 2 support triples
[`pair_second`, `pair_not_three`].

## 1. The degree sequence

Under `Cubic`, sum over v of m_v = 3 * 16 = 48 [`cubic_sum_mass`]. By Lemma 1 every mass is
4, 6 or 8 [`mass_cases`] and at most two vertices have mass other than 4
[`card_mass_ne_four_le_two`]. With eleven vertices the excess is
sum_v (m_v - 4) = 48 - 44 = 4, so the degree sequence is (8, 4^10) or (6, 6, 4^9)
[`eleven_degree_split`]. **At most two vertices are exceptional.** This is the only place
n = 11 is used, apart from the final weight count in Step 7.

## 2. The half-octahedron: a support triple with two ordinary ends has an apex

**Lemma H (half-closure).** Let {v, a, b} be a support triple with a, b ordinary and
v, a, b distinct. Then there are vertices a', b', y with

  link(a) = b - v - b' - y  and  link(b) = a - v - a' - y,

with the *same* y; moreover y is distinct from v, a, b, and a', b' are each distinct from
a, b, v and y. [`octa_half`]

*Hypotheses used:* mass 4 at a and at b only. **The mass of v is not used**, and v may be
exceptional.

*Proof.* Since a is ordinary, the pair {a, v} lies in a second support triple {a, v, b'}
with b' distinct from a, b, v [`second_v_triple`, from `pair_second` plus distinctness of
the three vertices of a support triple, `tri_distinct`]. The link of a is a 4-cycle
containing the two edges {v,b} and {v,b'} at v, so it is b - v - b' - y1 for a sixth vertex
y1 not in {a, v, b, b'} [`link_sixth`]. Symmetrically the link of b is a - v - a' - y2.
Reading the edge {y1, b} of link(a) gives the support triple {a, b, y1}; reading the edge
{y2, a} of link(b) gives {a, b, y2}. Together with {a, b, v} the pair {a, b} would then lie
in three distinct support triples if y1 were different from y2, which is impossible at the
ordinary vertex a [`pair_not_three`]. Hence y1 = y2 =: y. QED

Note what Lemma H does *not* give: it says nothing about a' versus b'. Distinctness of a'
and b' is proved separately, each time it is needed, from the absence of a triangle in the
4-cycle link of y (see Step 3).

## 3. The kill: an octahedron with four ordinary vertices contradicts condition (ii)

**Definition.** Say that v, a, b, a', b', y carry the *four octahedron links* if the six
vertices are pairwise distinct [`Dist6`] and

  link(a) = b - v - b' - y,  link(b) = a - v - a' - y,
  link(y) = b - a - b' - a',  link(a') = b - y - b' - v.        [`Octa4`]

(The fifth link, link(b') = v - a - y - a', is what `Octa` adds; it is never used.)

**Lemma K (the kill).** If v, a, b, a', b', y carry the four octahedron links and the four
vertices **a, b, a' and y** are ordinary, then condition (ii) fails. [`octa_kill4`]

*Hypotheses used:* mass 4 at a, b, a', y; pairwise distinctness of all six vertices;
the four links above; conditions (i) and (ii). **The mass of v is not used, the mass of b'
is not used, and the link of b' is not used.** The mirror statement, with the roles of a
and b (and of a' and b') exchanged, needs mass 4 at a, b, b', y and the link of b' instead
of that of a' [`octa_kill4'`, via `linkIs_rev` and `dist6_swap`].

*Proof.* Read off eight support triples from the links:

  at y: {y,a,b}, {y,a,b'}, {y,a',b'}, {y,a',b}      (the four edges of link(y))
  at v: {v,a,b}, {v,a,b'}, {v,a',b'}, {v,a',b}      (from link(a), link(b), link(a'))

The four triples at y are distinct, so by (M1) they exhaust the support of y
[`supp_eq_quad`]. Now apply condition (ii) at the pair U = {v, y}. Because U contains y,
the involution S maps to S xor U pairs each set containing y with a set not containing y,
so the full autocorrelation splits into two equal halves and

  sum over S in supp(y) of n_S * n_{S xor {v,y}} = 0.           [`condII_corr`,
                                                                 `corr_bit_half`,
                                                                 `corr_supp`]

Since a, b, a', b' are all different from v and from y, flipping the apex sends
{y, p, q} to {v, p, q} [`tri_xor_pair`]. So the four terms of that sum are exactly the four
products

  e1 = n_{v a b}  n_{y a b},    e2 = n_{v a b'} n_{y a b'},
  e3 = n_{v a' b'} n_{y a' b'}, e4 = n_{v a' b} n_{y a' b},

and e1 + e2 + e3 + e4 = 0. Each of the eight coefficients is +1 or -1 by (M1) at the
ordinary vertices a, a' and y, so each e_i is +1 or -1 [`pm_mul`].

Finally the sign relation (M2) at three ordinary vertices ties the e_i together. The four
support sets at a are {v,a,b}, {v,a,b'}, {y,a,b'}, {y,a,b} (distinct, hence all of them by
(M1)), so their coefficient product is +1, i.e. **e1 e2 = 1**. The four at b are {v,a,b},
{v,a',b}, {y,a',b}, {y,a,b}, giving **e1 e4 = 1**. The four at a' are {v,a',b'}, {v,a',b},
{y,a',b}, {y,a',b'}, giving **e3 e4 = 1**. Hence e2 = e1, e4 = e1 and e3 = e4 = e1, so
e1 + e2 + e3 + e4 = 4 e1 = plus or minus 4, never 0. Contradiction. [`eps_kill`] QED

This is the entire sign content of the proof. Everything that follows is bookkeeping whose
only purpose is to produce a configuration to which Lemma K applies.

**Lemma C (full closure at a lone exceptional vertex).** If {v, a, b} is a support triple
and *every* vertex other than v is ordinary, then a', b', y from Lemma H are pairwise
distinct from each other and from v, a, b, and all five links other than that of v are the
octahedron links. [`octa_eight`, packaged as `octa_eight'`]

*Proof.* Apply Lemma H. Its links give the support triples {a,v,b'}, {a,b',y}, {a,y,b},
{b,v,a'}, {b,a',y}. If a' = b', then link(y) would contain the three pairs {a',a}, {a',b}
and {a,b}, a triangle, which no 4-cycle contains; y is ordinary, so this is impossible
[`no_triangle_at`]. Given three faces at an ordinary vertex, its 4-cycle link is determined
[`link_of_three_faces`]: from {y,a,b}, {y,a,b'}, {y,b,a'} we get link(y) = b - a - b' - a';
this yields {y,b',a'}, and then from {a',y,b}, {a',y,b'}, {a',b,v} we get
link(a') = b - y - b' - v, which yields {a',b',v}; and from {b',a,v}, {b',a,y},
{b',v,a'} we get link(b') = v - a - y - a'. QED

## 4. The branch (8, 4^10)

**Proposition 1.** If at most one vertex v of a cubic solution on 11 variables is
exceptional, there is no solution. [`eleven_delta_zero_eight`]

*Hypotheses used:* every vertex other than v has mass 4. **The mass of v itself is never
used** -- in particular the value 8 plays no role, and the proposition is strictly stronger
than the (8, 4^10) sub-case.

*Proof.* By (iii) the vertex v lies in some support set [`supp_nonempty`], which by `Cubic`
is a triple {v, a, b} with a, b distinct and different from v [`supp_tri_of_mem`]. Both are
ordinary, so Lemma C closes the octahedron on v, a, b, a', b', y; the four vertices
a, b, a', y are all different from v and hence ordinary, so Lemma K applies. QED

Combining with Step 1: a cubic solution on eleven variables must have degree sequence
(6, 6, 4^9) [`eleven_delta_zero_reduce`].

## 5. The apex of a triple at an exceptional vertex

From here on v and w are the two exceptional vertices and every other vertex is ordinary.
No hypothesis on the values m_v, m_w is used before Step 7.

**Lemma D1.** Let {v, a, b} be a support triple with a and b ordinary. Then the apex y
supplied by Lemma H is the *other* exceptional vertex w:

  link(a) = b - v - b' - w   and   link(b) = a - v - a' - w,

with a', b' different from a, b, v, w. [`apex_other`]

*Hypotheses used:* every vertex other than v and w is ordinary; a, b are neither v nor w;
a, b, v pairwise distinct; {v, a, b} in the support. The masses of v and of w are not used,
and w is not required to be one of the n vertices at all: if it is not, the conclusion
y = w contradicts y < n, so in that situation the lemma just re-derives Proposition 1.

*Proof.* Apply Lemma H, obtaining a', b', y. Suppose y is neither v nor w. Then y is
ordinary, and, exactly as in Lemma C, a' is different from b' (else link(y) contains a
triangle) and link(y) = b - a - b' - a' is forced by the three faces {y,a,b}, {y,a,b'},
{y,b,a'} [`no_triangle_at`, `link_of_three_faces`]. Two cases:

* If a' is not w, then a' is ordinary (it is not v either) and its link is forced to be
  b - y - b' - v by the faces {a',y,b}, {a',y,b'}, {a',b,v}. Now v, a, b, a', b', y carry
  the four octahedron links with a, b, a', y all ordinary, so Lemma K applies:
  contradiction.
* If a' = w, then b' is ordinary (b' is not v, and b' is not a' = w), and its link is
  forced to be a - y - a' - v by the faces {b',y,a}, {b',y,a'}, {b',a,v}. This is the
  mirror configuration, killed by the mirror of Lemma K, which needs mass 4 at a, b, b'
  and y [`octa_kill4'`, applied here in the equivalent form `octa_kill4` after swapping
  a with b and a' with b'].

Either way we contradict condition (ii), so y is v or w; and y is different from v by
Lemma H. Hence y = w. QED

**Lemma D2.** No support triple contains both v and w. [`no_exc_pair`]

*Proof.* Suppose {u, v, w} is a support triple. Then u is neither v nor w, so u is ordinary
and the pair {u, v} lies in a second support triple {u, v, d} with d different from u and
from w [`pair_second`], and d is different from v because the three vertices of a support
triple are distinct [`tri_distinct`]. So d is ordinary, and Lemma D1 applies to the triple
{v, u, d}: link(u) = d - v - b' - w for some b' different from d, u, v and w. In that
4-cycle the two neighbours of v are d and b', so the only support triples containing the
pair {u, v} are {u, v, d} and {u, v, b'} [`link_v_nbrs`]. But {u, v, w} is such a triple and
w is neither d nor b'. Contradiction. QED

## 6. Killing every triple of ordinary vertices

**Lemma D3 (generic apex).** Let {x, a, b} be *any* support triple whose two ends a and b
are ordinary (x is arbitrary: ordinary or exceptional). Then at least one of the four
triples

  {v, a, b},  {w, a, b},  {v, b, x},  {w, b, x}

is in the support. [`apex_gen`]

*Hypotheses used:* every vertex other than v, w is ordinary; a, b not in {v, w};
a, b, x pairwise distinct; {x, a, b} in the support. The mass of x is not used.

*Proof.* Apply Lemma H at the triple {x, a, b}, giving a', b', y with
link(a) = b - x - b' - y and link(b) = a - x - a' - y. Reading link(b) gives the support
triple {b, x, a'}, and reading link(a) gives {a, y, b}. If a' = v or a' = w we are done by
the third or fourth alternative; if y = v or y = w we are done by the first or second. So
assume y and a' are both ordinary. Then, exactly as in Lemma D1, a' is different from b',
link(y) = b - a - b' - a' and link(a') = b - y - b' - x are forced, and x, a, b, a', b', y
carry the four octahedron links with a, b, a', y ordinary. Lemma K gives a contradiction.
QED

**Lemma D4 (no third triple on a pair through an exceptional vertex).** Let e be v or w,
let s and t be ordinary and let {e, s, t} be a support triple. Then no ordinary vertex u
completes the pair {s, t}: {s, t, u} is not in the support. [`kill_pair`]

*Hypotheses used:* e in {v, w}; s, t, u ordinary and pairwise distinct, and distinct from
v and w; **v is not w** (this is the one place the two exceptional vertices must genuinely
be two, and it is inherited by Lemma D5 and by the Theorem).

*Proof.* Write e1 = e and e2 for the other one of v, w. Lemma D1, applied at the triple
{e1, s, t} (both ends ordinary), gives link(s) = t - e1 - t' - e2 for some t' different
from s, t, e1 and e2. In this 4-cycle the two neighbours of t are e1 and e2, so the only
support triples containing the pair {s, t} are {s, t, e1} and {s, t, e2}
[`link_v_nbrs`]. An ordinary u is neither, so {s, t, u} is not in the support. QED

**Lemma D5 (no free triple).** Assume v is not w. Then no support triple has all three
vertices ordinary. [`kill_free_triple`]

*Proof.* Let {p, q, r} be such a triple. Apply Lemma D3 with x = p, a = q, b = r. In the
first two cases {v, q, r} or {w, q, r} is a support triple with q, r ordinary, and
{q, r, p} is a support triple with p ordinary: Lemma D4 (with s = q, t = r, u = p) gives a
contradiction. In the last two cases {v, r, p} or {w, r, p} is a support triple with r, p
ordinary, and {r, p, q} is a support triple with q ordinary: Lemma D4 (with s = r, t = p,
u = q) gives a contradiction. QED

## 7. The endgame

**Lemma D6 (a free set exists).** If m_v = m_w = 6 and no support set contains both v and
w, then some support set contains neither. [`exists_free_set`]

*Hypotheses used:* condition (i) only. `Cubic` is not used.

*Proof.* If every support set met {v, w}, then by disjointness the supports of v and of w
would partition the whole support, so
16 = sum_S n_S^2 = m_v + m_w = 6 + 6 = 12, a contradiction. QED

**Theorem (delta = 0 at n = 11).** There is no solution on eleven variables all of whose
support sets are triples. [`eleven_delta_zero`]

*Proof.* By Steps 1 and 4 the degree sequence is (6, 6, 4^9); let v, w be the two
mass-6 vertices and let every other vertex be ordinary [`eleven_delta_zero_reduce`]. Any
support set containing both v and w would be a triple {u, v, w} with u ordinary, which
Lemma D2 forbids; so the two supports are disjoint. By Lemma D6 there is a support set
containing neither v nor w; by `Cubic` it is a triple {p, q, r}, and all three of p, q, r
are ordinary. Lemma D5 forbids it. QED

## 8. Summary of what each mass hypothesis is for

| Step | needs mass 4 at | never uses |
|---|---|---|
| Lemma H `octa_half` | a, b | mass of v, of a', of b', of y |
| Lemma K `octa_kill4` | a, b, a', y | mass of v, mass of b', link of b' |
| Lemma K mirror `octa_kill4'` | a, b, b', y | mass of v, mass of a', link of a' |
| Lemma C `octa_eight` | every vertex except v | mass of v |
| Prop. 1 `eleven_delta_zero_eight` | every vertex except v | mass of v (so not m_v = 8) |
| D1 `apex_other` | every vertex except v, w | masses of v and w |
| D2 `no_exc_pair` | every vertex except v, w | masses of v and w |
| D3 `apex_gen` | every vertex except v, w | masses of v, w and x |
| D4 `kill_pair` | every vertex except v, w | masses of v and w |
| D5 `kill_free_triple` | every vertex except v, w | masses of v and w |
| D6 `exists_free_set` | -- | `Cubic`; needs m_v = m_w = 6 and (i) |

Nothing in Steps 2 to 6 is special to n = 11 or to the degree sequence: the hypothesis
everywhere is "at most two vertices have mass different from 4". Only Step 1 (the degree
split) and Step 7 (the weight count 6 + 6 < 16) are arithmetic about n = 11.

## 9. Relation to the referee's 630 completions

The independent seeded search in `referee/REPORT_delta0.md` (finding 8) reports that in the
(8, 4^10) branch the link shapes C_8 and C_3 + C_5 admit no combinatorial completion at
all, while C_4 + C_4 admits exactly 630, every one of them the "two octahedra glued at v"
configuration; none is excluded combinatorially, and all 630 die only to the sign argument
of Lemma A. **The Lean route is that sign argument, localised.** Lemma K is condition (ii)
evaluated at the pair U = {v, y}, where v is the apex of the octahedron and y its antipode:
the four surviving terms are the products e_i = n_{v-face} n_{y-face} over the four faces
of the equator, each e_i is a sign because the four vertices a, b, a', y have mass 4, and
the three mass-4 sign relations (M2) at a, b and a' force the four signs to be equal, so
their sum is plus or minus 4 rather than 0. Lemma A's identity sum over a of P'(a)^2 = 64
is the same computation done globally on the glued pair of octahedra; Lemma K does it on
one octahedron only, and it never needs the second one, nor the link of v.

Hence the 630 completions do not contradict anything: they are exactly the configurations
that Lemma K kills, and the Lean route reaches them without ever classifying link(v). Two
consequences worth recording:

* The route never enumerates link shapes, so C_8, C_3 + C_5 and the bowtie are simply
  never named. The referee's bowtie finding (finding 1 of `REPORT_delta0.md`), which was a
  real gap in `DELTA0_TOPOLOGY_FREE.md`, is moot here: the (6, 6, 4^9) branch of this route
  does not classify link(v) or link(w) at all.
* The search's "(6, 6, 4^9) has zero completions from all 15 link shapes" is a purely
  combinatorial statement and is *stronger* than what this route needs; the route instead
  kills that branch with three applications of the same sign argument (inside D1, D3) plus
  the weight count 6 + 6 < 16.

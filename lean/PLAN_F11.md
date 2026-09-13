# Lean plan for F(11)  (written 2026-09-13, after `F_twelve` was certified)

`F_twelve : F 12` is proved and gated.  What follows is the route to `F_eleven : F 11`,
which with `F_twelve` and the CHS lower bound gives `R_3 = 10`.

## What the hand proof (R3_equals_10.md) needs, and what already exists in Lean

| ingredient | hand proof | Lean status |
|---|---|---|
| m_i in {4,6,8}, sum m_i <= 48 | Lemma 1 | `mass_cases`, `sum_mass_le`, `mass_le_eight` — **done** |
| e + delta = 4 for n = 11 | Bookkeeping | `bookkeeping` — **done** (stated as `e + delta = 48 - 4n`) |
| >= 9 vertices of mass 4 | | `nine_mass_four`, `card_mass_ne_four_le_two` — **done** |
| mass-4 link = four ±1 sets, xor 0, sign product 1 | Lemma 2(a) | `mass_four_link`, `mass_four_even_degree` — **done, general n** |
| link types L1..L4 | Lemma 2(a) | **missing** (only L1 = the C_4 is done, and only for n = 12) |
| mass-4 link of *pairs* is a C_4 | L1 | `four_pairs_cycle` — **done, general** |
| octahedron closure from a C_4 link | Part I Step 3 | `octahedron_closure` — done but **hardwired to n = 12** |
| disjoint-sum contradiction | Part I Step 4 | inside `F_twelve` — **hardwired to n = 12** |
| m = 6 links (C_6 / two triangles / bowtie) | Lemma 2(b) | **missing** |
| m = 8 links (2-regular: C_8, C_3+C_5, C_4+C_4) | Lemma 2(c) | **missing** |
| closed-surface Euler argument | Fact T, delta = 0 | **must be replaced, see below** |

## Step 0 (do this first — it is pure refactoring and it unblocks everything)

Two things in the F(12) proof are stated for the literal `12` but are true verbatim for any
`n`, and both are needed again for F(11).  Generalise them *before* touching F(11) itself.

1. **`no_crossing_split`** — pull the tail of `F_twelve` out of `R3/Final.lean` into a lemma:
   ```
   theorem no_crossing_split {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {A : Finset ℕ}
       (hS0 : ∃ S0 < 2 ^ n, N S0 ≠ 0 ∧ ∀ j, S0.testBit j = true → j ∈ A)
       (hT0 : ∃ T0 < 2 ^ n, N T0 ≠ 0 ∧ ∀ j, T0.testBit j = true → j ∉ A)
       (hcross : ∀ S, S < 2 ^ n → N S ≠ 0 →
         (∀ j, S.testBit j = true → j ∈ A) ∨ (∀ j, S.testBit j = true → j ∉ A)) : False
   ```
   The existing proof uses `12` only through `hsol` and `2 ^ 12`; nothing is special.  This is
   *the* workhorse: every "f is a disjoint sum" step of R3_equals_10.md is an instance of it.
2. **`LinkIs` / `twelve_link_struct` / `link_sixth` / `link_of_three_faces` /
   `closure_of_links` / `octahedron_closure` generalised to `n`**, replacing the hypothesis
   "n = 12" (which forced every mass to be 4) by explicit per-vertex hypotheses
   `mass n N w = 4`.  Concretely `twelve_link_struct` becomes
   ```
   theorem link_struct (hsol : IsSol n N) (hv : v < n) (hm : mass n N v = 4)
       (hpairs : <the link of v consists of pairs, i.e. no lower-order term at v>) :
       ∃ p q r s, Cyc' n v p q r s ∧ LinkIs' n N v p q r s
   ```
   and `octahedron_closure` becomes: *if `v` and the five vertices its closure reaches all
   have mass 4 with pair-only links, then those six are closed.*  The proof text does not
   change; only `12` becomes `n` and the four `twelve_link_struct` calls acquire a mass
   hypothesis.  Budget: 3-5 agent-hours, almost all mechanical.

## Step 1: delta = 4 (all masses 4).  Do this case first — it is topology-free already.

Lower-order weight 4 splits as {4}, {2,2}, {3,1}, {2,1,1}, {1,1,1,1}.  All five sub-cases are
finite link-type reasoning plus, twice, `no_crossing_split`.  Prerequisites:
- **`link_types`**: the L1..L4 classification of four distinct sets of size <= 2 with xor 0.
  This is the analogue of `four_pairs_cycle` with the size-<= 2 sets allowed to be smaller.
  Do it the same way: `exists_pair_of_card_two` / card 0 / card 1 case split, then `omega` on
  bitmasks.  Estimate 4-6 hours.  Everything else in delta = 4 is then `omega`-level.
- The `{1,1,1,1}` sub-case additionally needs the counting identity
  `sum_{T in N} |T \ S_0| + 3 M = 28`; that is `sum_mass_le`/`bookkeeping` localised to a
  4-set, and is the one genuinely fiddly piece.
Estimate for the whole of delta = 4: 12-18 agent-hours after Step 0.

## Step 2: delta = 2.  Needs `link_types` plus the m = 6 link classification (Lemma 2(b)):
six distinct pairs with all degrees even = C_6, two triangles, or a bowtie.  Same technique as
`four_pairs_cycle`, one size up; expect it to be the single largest `omega` in the project, so
do it as `edge_nbr`-style small lemmas, never one big case split.  The rest of delta = 2 is the
same "complete the C_4, share the cubic, get a triangle in a C_4" pattern as Part I Step 3, so
`link_of_three_faces` and `no_triangle_at` are reusable almost as they stand.
Estimate 10-15 agent-hours.

## Step 3: delta = 0.  **The Euler-characteristic argument must not be formalised.**

Replacement (topology-free, and it reuses everything above):

In delta = 0 the degree sequence is `(8, 4^10)` or `(6, 6, 4^9)`, so **at most two vertices
have mass ≠ 4** (`card_mass_ne_four_le_two`, already proved).  Every mass-4 vertex has a C_4
link.  The generalised `octahedron_closure` says: starting from a mass-4 vertex `v`, if the
five further vertices it reaches also have mass 4, the six are closed, and
`no_crossing_split` finishes (11 - 6 = 5 vertices remain, so `CondIII` supplies a support
triple outside).  So the whole delta = 0 case reduces to:

> **Pigeonhole lemma to prove:** among the 11 vertices there is a mass-4 vertex whose closure
> six-set contains no exceptional vertex.

This is *not* automatic and is the one real mathematical gap in this plan — the two
exceptional vertices could in principle meet every octahedron.  Two ways out, in order of
preference:
1. Strengthen the closure lemma so it only needs *four* of the six vertices to have mass 4
   (the two exceptional vertices can then be absorbed), by redoing `link_of_three_faces` with
   one of the three faces allowed to be unknown.  If that works, delta = 0 is finished with no
   new machinery.
2. Failing that, enumerate: with the exceptional vertices fixed, the 9 mass-4 vertices carry
   C_4 links, and a `decide` over the (small) list of possible closure patterns rooted at one
   of them settles it — but **the completeness of that list must itself be proved in Lean**,
   never imported from `search/` or `referee/`.  Do not certify a `decide` over a list
   produced by the external search.

Estimate: unknown until route 1 is tried; 15 hours if route 1 works, 30+ if not.

## Order of work for the next agent
1. Step 0.1 (`no_crossing_split`) — 1 hour, immediately shrinks `R3/Final.lean`.
2. Step 0.2 (generalise the closure chain to `n`) — 3-5 hours.
3. `link_types` (L1..L4) — 4-6 hours.  With it, delta = 4 falls.
4. Try route 1 of Step 3 early: it is cheap to test and it decides the shape of the rest.

---

## ANSWER to the Step 3 risk question (task 20, rotation 1, 2026-09-13)

**Question.** Can `octahedron_closure` be weakened so that only *some* (say four) of the six
vertices of `A` need mass 4, letting the two exceptional vertices of the `delta = 0` case be
absorbed into `A`?

**Answer: NO, not as route 1 describes it.  Route 1 is aimed at the wrong half of the lemma.**

Route 1 proposes redoing `link_of_three_faces` with one face unknown.  That lemma is about
*deriving* a link cycle from fewer known faces.  But the obstruction is not in the derivation,
it is in the **conclusion**, and it is visible without any mathematics:

`closure_of_links` concludes `∀ S, N S ≠ 0 → S ⊆ A ∨ S ∩ A = ∅`.  Take an exceptional vertex
`w ∈ A` of mass 6 or 8.  The conclusion asserts, in particular, that every support triple
through `w` lies inside `A`, i.e. that the whole link of `w` (6 or 8 pairs) lives on the five
other vertices of `A`.  Nothing in "the other four vertices have mass 4" constrains the link of
`w` at all, so no amount of rework of `link_of_three_faces` can produce that conclusion.  The
six link hypotheses `Lv … Le` of `closure_of_links` are each used, and each is used exactly to
exclude triples through that one vertex; drop one and the corresponding triples are unbounded.

Note the conclusion is not *false* for an exceptional `w` — a mass-6 link can sit on five
vertices (a bowtie has degree sequence 4,2,2,2,2) — it is simply **underdetermined**.  So this
is a statement-shape obstruction, not a repairable proof gap.

**Consequence for the plan.**  `delta = 0` must go by route 2, or by a genuine pigeonhole.
Record two facts that make the pigeonhole the better target:
- When all six of `v, a, b, c, d, e` have mass 4, the closure is *symmetric*: `A(w) = A(v)` for
  every `w ∈ A(v)`, because each of the six links is the 4-cycle on the other four.  So the
  mass-4 vertices that admit a full closure are partitioned into 6-sets, and the needed
  statement is exactly "some 6-set of the partition misses both exceptional vertices".
- Once such an `A` exists, `no_crossing_split` closes `delta = 0` immediately at `n = 11`:
  `A` has 6 vertices, the other 5 each have mass ≥ 4, and non-crossing forces every triple
  through an outside vertex to be wholly outside, which supplies `hT0`.

**Revised estimate.**  `delta = 0` is the expensive case, not the cheap one: 30+ hours, and the
pigeonhole is still unproved on paper.  **Recommendation: prove `delta = 4` and `delta = 2`
first and leave `delta = 0` to a dedicated run**, and ask the referee lane for a paper proof of
the pigeonhole before any more Lean time is spent on it.


---

## Progress update (task 20, rotation 1, end of run)

**Done and gated this run:**
- Step 0.1 `no_crossing_split` — was already done in task 18.
- **Step 0.2 (generalise the closure chain to `n`) — DONE.**  `R3/Octahedron.lean` now carries
  `Cubic`, `link_cycle`, `link_struct`, `octahedron_closure_gen`, all general in `n` with
  explicit `mass n N w = 4` hypotheses; `twelve_link_struct` / `octahedron_closure` are `n = 12`
  corollaries.
- **Step 1's prerequisite `link_types` (L1..L4) — DONE**, in the new `R3/LinkTypes.lean`,
  together with a reusable parity tool `card_sum_even` (xor 0 ⇒ the four sizes sum to an even
  number) that removes every impossible shape in one line.

**Revised order of work.**  Step 3 route 1 is dead (see the answer above), so:
1. `delta = 4` (Step 1) — now unblocked; the only fiddly piece left is the `{1,1,1,1}`
   counting identity.
2. `delta = 2` (Step 2) — needs the `m = 6` link classification; expect `card_sum_even` and
   `three_pairs_triangle` to carry much of it.
3. `delta = 0` (Step 3) — **blocked on mathematics, not on Lean.**  Get a paper proof of the
   pigeonhole first; do not start it in Lean without one.

## Captain's note on the delta = 0 pigeonhole (2026-09-13 18:00, Fable)

The requested pigeonhole ("some mass-4 vertex has a closure 6-set avoiding both exceptional vertices") is FALSE
in general and must not be pursued as stated. Witness: the C_4 ∪ C_4 sub-case of R3_equals_10.md, two octahedra
glued at the mass-8 vertex v. Every mass-4 vertex lies in one of the two octahedra, and both octahedra contain v,
so every closure 6-set contains the exceptional vertex. The hand proof kills that configuration by a *different*
argument (the glued-octahedra sign-vector / non-constancy check, referee/check_glued_octahedra.py), not by the
disjoint-sum lemma.

Correct topology-free shape for delta = 0 (do this, in order):
 (a) Weak closure at a mass-4 vertex v with link cycle a-b-c-d: `link_types` + `link_cycle` give the 4 triples at v.
     If a, b, c, d and the sixth vertex x all have mass 4, `octahedron_closure_gen` applies -> `no_crossing_split`
     -> contradiction (CondIII gives a nonzero coefficient outside the 6-set since 11 > 6). So WLOG every closure
     attempt from every mass-4 vertex meets an exceptional vertex (mass 6 or 8).
 (b) That residual situation is a small explicit family: an exceptional vertex of mass 8 with link C_8, C_3∪C_5 or
     C_4∪C_4 (the hand proof's three sub-cases), or two mass-6 vertices. Each is a finite structure on 11 vertices
     with all coefficients ±1 (Lemma 2(d): no ±2 at delta = 0). Enumerate the candidate supports as explicit bitmask
     lists (the referee's round2b_out_structures gives 2 iso classes for the analogous n=11 structures) and kill each
     by `decide` on the finite check "no sign vector in {±1}^16 makes CondII hold" — or, cheaper, by evaluating the
     CondII sum at one well-chosen U for each sign pattern. Completeness of the enumeration is the part that must be
     PROVED in Lean (it follows from (a) + the link classification), never imported from the external search.
 (c) The C_8 case and the "two mass-6" cases may close by pure counting (masses/pairs), as in the hand proof's
     Euler-characteristic step recast as: sum over vertices of link edge counts = 3 * (#triples) and every pair lies
     in 0 or 2 triples. Try the counting first; fall back to (b).

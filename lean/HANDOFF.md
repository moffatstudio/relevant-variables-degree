# HANDOFF — Lean R3 certificate (task 18, agent starting 2026-09-13 ~15:00Z)

## State at start of this run
`bash lean/gate.sh` PASS: lake build ok, no laundering, 23 theorems on
[propext, Classical.choice, Quot.sound].  Top theorem `R3.twelve_link_cycle` /
`R3.twelve_link_struct` (the latter lives in R3/Octahedron.lean, which is written but
**not yet imported** by R3.lean and never compiled by a previous agent).

## My decomposition of F(12)  (IMPORTANT — differs from PLAN.md, and is much cheaper)

PLAN.md Step 3 asks for "two vertex-disjoint octahedra".  **Step 4 does not need that.**
Step 4 only needs: *there is a set A of vertices such that no support triple crosses
between A and its complement, and both sides contain a support triple.*

So the chain is:

1. `octahedron_closure` (R3/Octahedron.lean).  Statement:
   ```
   theorem octahedron_closure {N} (hsol : IsSol 12 N) {v} (hv : v < 12) :
     ∃ A : Finset ℕ, A.card = 6 ∧ A ⊆ range 12 ∧ v ∈ A ∧
       ∀ S, S < 2^12 → N S ≠ 0 →
         (∀ j, S.testBit j = true → j ∈ A) ∨ (∀ j, S.testBit j = true → j ∉ A)
   ```
   Proof (topology-free, all on the `Edge`/`LinkIs` relation of Octahedron.lean):
   - link(v) = 4-cycle a-b-c-d  (`twelve_link_struct`).
   - link(a) contains edges b-v and v-d, so it is b-v-d-e (`edge_through`).
   - e ≠ c: else face {a,c,b} exists and link(b) would contain the triangle a-v-c
     (`edge_no_triangle`).
   - link(b): has edges v-a, v-c (from link v) and a-e (from face {a,e,b}); `edge_through`
     gives cycle a-v-c-x and the a-e edge forces x = e.  So link(b) = a-v-c-e.
   - link(d): edges v-c, v-a, a-e  ⇒ link(d) = a-v-c-e.
   - link(c): edges v-b, v-d (link v), b-e (face {b,e,c}) ⇒ link(c) = b-v-d-e.
   - link(e): edges a-d, a-b (faces {a,d,e},{a,e,b}), b-c (face {b,c,e}) ⇒ link(e) = d-a-b-c.
   - A := {v,a,b,c,d,e}; every w ∈ A has a link cycle with all four vertices in A, so every
     support triple meeting A lies inside A.
2. `F_twelve` (R3/Twelve.lean or Octahedron.lean).  Take v = 0, get A.  A.card = 6 < 12 so
   there is w < 12 with w ∉ A; CondIII + `twelve_card_three` give support triples
   S0 ∋ (some vertex of A, via CondIII at v) inside A and T0 ∋ w outside A.
   Put U := S0 ||| T0.  For any S,T < 2^12 with S ^^^ T = U and N S * N T ≠ 0, the closure
   forces {S,T} = {S0,T0} (one side of A each; every vertex of S0 is in U ∩ A and not in T,
   hence in S; card 3 = card 3 gives S = S0).  So CondII at U is `2 * N S0 * N T0 ≠ 0`.
   Sum manipulation: `Finset.sum_subset` (outer, s = {S0,T0}) + `Finset.sum_eq_single_of_mem`
   (inner).

## In progress right now
Writing R3/Octahedron.lean: moving `edge_no_triangle` / `edge_through` from WIP.lean into it
(they compile there with `unfold Edge; omega` after `clear * -`), adding `tri_swap12`,
`tri_rotate`, then `octahedron_closure`.

## Next three concrete steps
1. `lake env lean R3/Octahedron.lean` clean, add `import R3.Octahedron` to R3.lean (root-file
   trap: a file not imported there is NEVER checked).
2. Prove `F_twelve`.
3. Add both to gate.sh's `#print axioms` list and rerun `bash gate.sh`.

## Gotchas (also in TOOLCHAIN_NOTES.md)
- `clear * - h1 h2` before every `omega` on `Edge` goals; omega is exponential in the number
  of disequalities in context.
- `Finset.card_insert_of_notMem` (not `_of_not_mem`).

# HANDOFF — Lean R3 certificate (task 20, rotation 1, 2026-09-13)

## State: GREEN.  **F(12) is machine-checked.**  F(11) is NOT proved.

`bash lean/gate.sh` → GATE: PASS.  Top theorem `R3.F_twelve : F 12` (R_3 ≤ 11), from the
frozen `R3/Statement.lean`, no `sorry`, no `native_decide`, standard axioms only.
The gate's `#print axioms` list is now 42 theorems.  Do not edit `R3/Statement.lean`.

## What THIS run added (three things)

### 1. The Step 3 risk question is answered, and the answer is NO
Full write-up in `PLAN_F11.md` under "ANSWER to the Step 3 risk question".  Route 1 of
PLAN_F11 Step 3 — weaken the closure so only four of the six vertices need mass 4 — **cannot
work**, and the reason is a statement-shape obstruction, not a proof gap.  `closure_of_links`
concludes that *no* support triple crosses out of `A`; for an exceptional vertex `w ∈ A` that
asserts the whole link of `w` sits on the other five vertices of `A`, and mass-4 hypotheses at
the other four vertices say nothing whatever about the link of `w`.  Reworking
`link_of_three_faces` (which is about *deriving* a link) cannot fix this.

**Consequence: `delta = 0` is the expensive case, not the cheap one.**  Do `delta = 4` and
`delta = 2` first.  Before any more Lean time goes into `delta = 0`, ask the referee lane for
a paper proof of the pigeonhole: *some mass-4 vertex has a closure 6-set containing neither
exceptional vertex.*  Two facts that help: when all six of `v,a,b,c,d,e` have mass 4 the
closure is symmetric (`A(w) = A(v)` for every `w ∈ A(v)`), so the closable mass-4 vertices are
partitioned into 6-sets; and once such an `A` exists, `no_crossing_split` finishes `delta = 0`
at `n = 11` immediately, because the other 5 vertices have mass ≥ 4 and non-crossing forces
every triple through an outside vertex to lie wholly outside.

### 2. PLAN_F11 Step 0.2 is DONE — the closure chain is general in `n`
In `R3/Octahedron.lean`.  New: `Cubic n N` (`∀ S < 2^n, N S ≠ 0 → card n S = 3`, the `δ = 0`
hypothesis), `cubic_link_card_two`, **`link_cycle`**, **`link_struct`**, `twelve_cubic`,
**`octahedron_closure_gen`**.  `Cyc` and `LinkIs` now take `n` as their first argument.
`link_sixth`, `link_of_three_faces`, `no_triangle_at`, `closure_of_links` are general in `n`
and carry an explicit `mass n N w = 4` hypothesis at each vertex whose link they read
(`closure_of_links` no longer takes `hsol`, only `Cubic`).  `twelve_link_struct` and
`octahedron_closure` are now one-line `n = 12` corollaries, so `R3/Final.lean` and `F_twelve`
are untouched.

### 3. PLAN_F11 Step 1's prerequisite is DONE — **`link_types` is proved**
New file `R3/LinkTypes.lean` (619 lines, all gated).  The headline theorem is

```
theorem link_types {n T1 T2 T3 T4 : ℕ}
    (b1 : T1 < 2^n) … (c1 : card n T1 ≤ 2) … (d12 : T1 ≠ T2) …
    (hxor : T1 ^^^ T2 ^^^ T3 ^^^ T4 = 0) : LinkType T1 T2 T3 T4
```

`LinkType` is the four-way disjunction L1 (a 4-cycle of pairs, via `four_pairs_cycle`),
L2 (`∅,{a},{b},{a,b}`), L3 (`{a},{b},{a,c},{b,c}`), L4 (`∅,{a,b},{b,c},{a,c}`), each stated as
a predicate holding of all four sets, so it is symmetric; `linkType_swap12/23/34` and
`linkType_rot13/rot14` permute it.  Supporting results worth knowing about:
- `card_le_two_cases` — a mask with ≤ 2 bits is `0`, `2^a` or `pair a b`;
- `three_pairs_triangle` — three distinct pairs with xor 0 are the edges of a triangle,
  returned in the strong ordered form `xy, xz, yz`;
- **`card_sum_even`** — if `A ^^^ B ^^^ C ^^^ D = 0` then `|A|+|B|+|C|+|D|` is even.  This one
  lemma kills every "odd number of singletons" shape in one line and is likely to be reusable
  for the `m = 6` and `m = 8` link classifications of Steps 2 and 3;
- `card_two_pow`, `card_pair_eq`, `pair_xor_pair_ne_two_pow`, `four_two_pow_xor_ne_zero`.

## Next work

**`delta = 4` at `n = 11`** (PLAN_F11 Step 1): all masses are 4, lower-order weight 4 splits as
`{4}, {2,2}, {3,1}, {2,1,1}, {1,1,1,1}`.  `link_types` is now available, `no_crossing_split` is
general, and the closure chain is general.  The remaining genuinely fiddly piece named in the
plan is the `{1,1,1,1}` counting identity `∑_{T∈N} |T \ S₀| + 3M = 28`, i.e. `sum_mass_le` /
`bookkeeping` localised to a 4-set.

To use `link_types` on a link, feed it the four link sets `S ^^^ 2^v` from `mass_four_link`
(which already gives distinctness, `card ≤ 2`, and xor 0) — `link_cycle` shows the pattern for
the all-pairs case.

`R3/WIP.lean` is empty scratch (imports `R3.LinkTypes`, is NOT imported by `R3.lean`).
Keep unfinished proofs there — but note the gate's laundering scan greps it too, so never park
a `sorry` in it.

Remaining-hours estimate: `delta = 4` 10-15 h (down from 12-18, `link_types` is done);
`delta = 2` 10-15 h and it needs the `m = 6` link classification (six distinct pairs, all
degrees even = C₆ / two triangles / bowtie — same technique, `card_sum_even` should help);
`delta = 0` 30+ h **and a paper proof of the pigeonhole that does not yet exist**.

## Discipline notes
- Every new file needs an `import R3.<File>` line in `R3.lean` or `lake build` never checks it.
- Add every new theorem to `gate.sh`'s `#print axioms` list.
- `PROGRESS.log` gets one line the moment a lemma type-checks.
- `lake env lean R3/WIP.lean` is the fast loop (~1.5 min); a full `bash gate.sh` is ~25-30 min,
  so budget one gate run per lemma *group*.  One `lake build` at a time.
- New gotchas from this run are in `TOOLCHAIN_NOTES.md` (the `ac_rfl`-for-xor trick, the
  `rcases … with rfl` variable-elimination trap, and the WIP laundering-scan trap).

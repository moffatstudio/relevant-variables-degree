# HANDOFF — Lean R3 certificate (end of task 18, 2026-09-13)

## State: GREEN.  **F(12) is machine-checked.**

`bash lean/gate.sh` → GATE: PASS.  `lake build` ok (7224 jobs), no laundering constructs,
31 listed theorems all on `[propext, Classical.choice, Quot.sound]`.

Top theorem: **`R3.F_twelve : F 12`** — no coefficient vector satisfies the frozen finite
statement on 12 variables, i.e. no degree-3 Boolean function has 12 relevant variables,
i.e. **R_3 ≤ 11**, from `R3/Statement.lean` (untouched) with no `sorry`, no `native_decide`.

## What this run added

`R3/Octahedron.lean` (Step 3 of R3_upper_bound.md, topology-free):
`card_quad_le`, `edge_symm`, `edge_rot`, `edge_rev`, `edge_mem`, `edge_nbr`,
`edge_no_triangle`, `edge_through`, `twelve_link_struct`, `edge_pq/qr/rs/sp`,
`tri_swap/tri_rotl/tri_rotr`, `link_sixth`, `link_of_three_faces`, `no_triangle_at`,
`closure_of_links`, **`octahedron_closure`**.

`R3/Final.lean` (Step 4): `xor_cancel_left`, **`no_crossing_split`** (general `n`),
**`F_twelve`**.

**Design decision worth keeping.**  PLAN.md's Step 3 asked for "two vertex-disjoint
octahedra".  Step 4 does not need that.  `octahedron_closure` exports only: *every vertex `v`
lies in a 6-set `A` such that no support triple crosses between `A` and its complement.*
The second octahedron is never constructed; the vertex outside `A` needed for Step 4 comes
from `CondIII` plus `A.card = 6 < 12`.  This cut the work roughly in half and the same
statement is what F(11) will reuse.

## Next work: F(11).  Read `lean/PLAN_F11.md` — it is the detailed route.

**First step for the successor (already scoped, ~3-5 h, purely mechanical):**
generalise the closure chain in `R3/Octahedron.lean` from the literal `12` to a general `n`,
replacing the implicit "all masses are 4" (which is what `n = 12` buys) by explicit
`mass n N w = 4` hypotheses on the six vertices involved.  `no_crossing_split` is already
general, so once the closure is general, the delta = 0 case of F(11) reduces to the pigeonhole
question stated in PLAN_F11.md Step 3, and delta = 4 reduces to the L1..L4 link
classification (PLAN_F11.md Step 1).

Remaining-hours estimate: F(12) **done**.  F(11): 30-50 agent-hours, the uncertainty being
whether route 1 of PLAN_F11.md Step 3 (a closure lemma needing only four of the six vertices
to have mass 4) works; if it does not, add 20 more.

## Discipline notes for the successor
- `R3/WIP.lean` is scratch and is NOT imported by `R3.lean`; keep unfinished proofs there.
- Every new file must get an `import R3.<File>` line in `R3.lean` or `lake build` never
  checks it.  Add every new theorem to gate.sh's `#print axioms` list.
- `lean/PROGRESS.log` gets one line the moment a lemma type-checks.
- New gotchas from this run are appended to `TOOLCHAIN_NOTES.md`; the two that cost the most
  time were (a) heartbeats are per *declaration*, so long tactic proofs must be split into
  top-level lemmas, and (b) `omega` is exponential in the number of `≠` hypotheses in
  context, so `clear * - <what it needs>` before every one.

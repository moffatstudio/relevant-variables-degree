# HANDOFF — Lean R3 certificate (task 25, rotation 3, 2026-09-13)

REFACTOR DONE 2026-09-13T20:09Z — the `CubicAt` refactor of `R3/Octahedron.lean` is gated and
`R3.LinkSix` / `R3.DeltaTwo` are merged into `R3.lean` + `gate.sh`.
**DELTA FOUR DONE 2026-09-13T21:55Z — `eleven_delta_four` is gated.**

## State: GREEN.  `bash lean/gate.sh` → GATE: PASS, 97 theorems, no `sorry`, no
`native_decide`, axioms `[propext, Classical.choice, Quot.sound]` only.
**F(12) machine-checked** (`R3.F_twelve`, from the frozen `R3/Statement.lean`).
For F(11): **`δ = 4` is completely closed**; `δ = 2` is partial (the parked lane's two
branches are gated, the one-linear-term branch is open); `δ = 0` is still blocked on paper
mathematics.

## What this run added

### 1. The `CubicAt` refactor (unblocks δ = 2 and δ = 4)
`CubicAt n N v := ∀ S, S < 2 ^ n → N S ≠ 0 → S.testBit v = true → card n S = 3` — cubicity at
one vertex, which is all the link chain ever reads.  `cubicAt_of_cubic`,
`cubicAt_link_card_two`, and the primed chain `link_cycle'`, `link_struct'`, `link_sixth'`,
`link_of_three_faces'`, `no_triangle_at'` (each takes `CubicAt` at the single vertex whose link
it reads).  `closure_of_links'` takes the weak hypothesis
`∀ S, S < 2^n → N S ≠ 0 → card n S = 3 ∨ (∀ j, S.testBit j = true → j ∉ {v,a,b,c,d,e})`, and
`octahedron_closure_gen'` takes `CubicAt` at every vertex plus `N 0 = 0`.
Every global-`Cubic` name is unchanged and is now a one-line corollary, so `R3/DeltaZero.lean`
and `F_twelve` were untouched.

### 2. gate.sh
The laundering scan strips backtick-quoted prose before grepping, so a doc comment naming the
s-word no longer fails the gate (that was the standing GATE: FAIL inherited from rotation 2).
The `#print axioms` list is now 97 entries, including the 15 delta = 2 names.

### 3. `δ = 4`, the `{2,2}` sub-case — `eleven_delta_four`
> `IsSol 11 N → (∀ v < 11, mass 11 N v = 4) → False`

New machinery in `R3/DeltaFour.lean`:
- `link_L4_of_linear` — a mass-4 vertex with a linear term and no quadratic has a triangle
  link, stated as an **iff**: `N (tri v x y) ≠ 0 ↔ x ≠ y ∧ x ∈ {a,b,c} ∧ y ∈ {a,b,c}`.  The
  iff form is what makes every later step one line; copy it for any L-shape classification.
- `two_linear_no_quad`, `cubicAt_of_two_linear` — the `{2,2}` configuration has no quadratic
  at all, and every vertex other than `i`, `j` is `CubicAt`.
- `closure_local` — generic: a vertex set all of whose cubics stay inside it, and which
  contains every non-cubic support set, is closed.  Replaces the bespoke `hcross` block of
  `eleven_cycle_closed`; use it for any future closure argument.
- `linear_not_triangle` — `j ∉ {a,b,c}` (else a mass-4 vertex's 4-cycle link carries a
  triangle, `no_triangle_at'`).
- helpers `pair_mem_of_eq`, `pair_of_triangle`, `mem_of_triangle_eq`.

The route: L4 at `i` gives the triangle `a,b,c`; `j` avoids it; `link_sixth'` at each of
`a,b,c` gives a sixth vertex, all three equal (`Edge` + `omega`); that vertex carries the
triangle `a,b,c`, so it is not cubic, so it is `j`; then `{i,j,a,b,c}` is closed and
`no_crossing_split` finishes.  This follows the `{2,2}` bullet of `R3_equals_10.md` verbatim.

## Next work

1. **δ = 2** (the parked lane, now unblocked).  `eleven_delta_two_quad` and
   `delta_two_linear` are gated; what is missing is the one-linear-term branch, whose big
   piece is `five_pairs_cycle` (five distinct pairs with xor 0 form a C₅, same technique as
   `four_pairs_cycle`).  See `HANDOFF_delta2.md`.  Estimate 10-15 h.
2. **δ = 0** — still blocked on mathematics, not Lean: the pigeonhole step is false
   (the C₄ ∪ C₄ glued-octahedra witness).  See the captain's note at the end of `PLAN_F11.md`.
   Estimate 30+ h after a paper proof exists.
3. Assemble `F_eleven` once δ = 2 and δ = 0 land: `bookkeeping` splits into `e ∈ {0,2,4}`,
   and `eleven_delta_four` is the `e = 0` branch.

## Remaining-hours estimate
| case | hours | blocked? |
|---|---|---|
| δ = 4 | **0 — done** | — |
| δ = 2 | 10-15 | no (refactor delivered) |
| δ = 0 | 30+ | yes, on paper mathematics |

## Discipline notes
- Every new file needs an `import R3.<File>` line in `R3.lean` or `lake build` never checks it.
- Add every new theorem to `gate.sh`'s `#print axioms` list (now 97).
- `lake env lean R3/DeltaFour.lean` is the fast loop (~70 s); a full `bash gate.sh` is 3-6 min
  when the tree is warm.  One Lean worker at a time.
- Heredocs through the Bash tool mangle long Lean blocks — write the block with the Write tool
  to a `.tmp` file and splice it in with a short python script.  Python must open project files
  with `io.open(..., encoding='utf-8')`; the default cp1252 codec throws on the maths symbols.
- `subst h` on `h : w = j` eliminates `j`, not `w`; if later lines name `j`, use
  `rw [h] at ...` instead (this cost one compile cycle).
- A single `omega` over five 3-way disjunctions times out at the default heartbeat budget;
  factor it into a named lemma (`mem_of_triangle_eq`) applied twice.  `eleven_delta_four`
  carries `set_option maxHeartbeats 1000000 in`.
- `R3/WIP.lean` is empty scratch (NOT imported) and must stay free of banned constructs.

# Toolchain notes (Lean 4 on this Windows machine) — appended by every Lean agent

## 2026-09-13 (task 14c)
- Toolchain: `leanprover/lean4:v4.23.0` (lean/lean-toolchain) matches `C:/ml/mathlib/lean-toolchain`
  exactly. `lake` / `lean` on PATH via `C:/Users/moffa/.elan/bin`. Do NOT rebuild Mathlib.
- Lakefile is TOML with `[[require]] name = "mathlib" path = "C:/ml/mathlib"`; the manifest lists
  mathlib as a `path` package and the transitive deps (batteries, aesop, Qq, proofwidgets, ...)
  as git packages that live in `lean/.lake/packages/` and are already built.  A clean
  `lake build` with only Statement.lean imported "succeeds" in ~2 min (7217 jobs, all replayed).
- GOTCHA: `lake build` only builds the modules reachable from the default target `R3`
  (the root file `lean/R3.lean`).  The second agent's `R3.lean` imported only `R3.Statement`,
  so "lake build passes" said nothing about Basic.lean.  Every new file MUST be added as an
  `import R3.<File>` line in `R3.lean` or it is never checked.
- `Finset.card_insert_of_not_mem` is now `Finset.card_insert_of_notMem` in this Mathlib
  (the `not_mem` → `notMem` rename).  `Finset.sum_filter_add_sum_filter_not`,
  `add_sum_erase`, `card_eq_succ`, `card_eq_three` exist (there is no `card_eq_four`).
- Elapsed-time discipline: run at most one `lake build` at a time (RAM); use
  `run_in_background` and tail the log with `grep -vE "^✔|Replayed"` to see only errors.

### Proof-engineering gotchas hit in this run (Lean 4.23 / Mathlib 2025-09)
- Basic.lean (written by the previous agent, never compiled) had 9 errors, all of the same
  kinds: `subst h` renaming the wrong variable (use `subst x` naming the variable to
  eliminate, or `rw [h]`), `rw` closing a goal by `rfl` so a following `simp` errors with
  "no goals", `norm_num at h ⊢` erroring when `h` becomes `False` first (use `revert h;
  norm_num` or `decide`), `simpa using` on `2 ∣ m - 4` vs `2 ∣ m` (use `omega`, it knows
  divisibility by literals), `Nat.pos_pow_of_pos` deprecated (`Nat.two_pow_pos n`),
  `apply lemma _ _` producing goals in a different order than `refine lemma _ ?_ ?_`,
  un-beta-reduced `(fun T => f T) S` after `sum_erase_add` making `omega` see distinct atoms
  (state the `have` with an explicit type), and `rw ... at *` silently rewriting the wrong
  hypothesis.
- `omega` does NOT case-split `if c then 1 else 0` (treats it as an atom): use `split_ifs at h ⊢
  <;> omega`, but never on 8 ifs at once (256 branches x omega = heartbeat timeout).
- `omega` IS exponential in the number of disjunctive hypotheses in context (`a ≠ b` counts as
  one, `¬((p ∧ q) ∨ (r ∧ s))` as two).  Six such hypotheses + four `≠` made a trivial goal
  time out at 200000 heartbeats.  Fix: `clear * - h₁ h₂; omega` (Mathlib `clear * -`) so each
  omega call sees only the 1-5 facts it needs.  After this the whole Cycle.lean compiles in 60 s.
- Heartbeats are per declaration: one slow tactic early in a theorem makes every later tactic in
  the same theorem report "(deterministic) timeout"; only the first error is real.
- `lake env lean R3/File.lean` type-checks one file (needs its imports' .olean from a previous
  `lake build`); ~1-2 min per file here, much faster than a full `lake build` (~3-4 min) for
  iterating.  The final check must still be `lake build` + gate.sh.
- `Bool.eq_iff_iff`, `Nat.testBit_two_pow` (`= decide (n = m)`), `Nat.testBit_or`,
  `Nat.xor_lt_two_pow`, `Nat.lor_comm`, `Finset.card_eq_two/three`, `Finset.card_eq_succ`
  all exist under these names; there is no `Finset.card_eq_four` (proved locally).
- `subst x` (variable form) is deterministic; `subst h` with `h : x = y` and both sides
  variables eliminates one of them and you cannot rely on which.

## 2026-09-13 (task 18, the F(12) run)
- `set_option foo in` and a `/-- doc -/` cannot both precede a declaration in either order:
  `/-- doc -/ set_option x in lemma` is a parse error ("unexpected token 'set_option';
  expected 'lemma'").  Use a plain `--` comment when you need `set_option ... in`.
- **Heartbeats are per declaration, and a long tactic proof shares one budget.**  A 200-line
  `theorem` that calls `tauto`/`omega` twenty times will die at `maxHeartbeats` even though
  every individual call is fast.  The fix is not a bigger limit (4000000 still died) but
  splitting the theorem into top-level lemmas: `octahedron_closure` only compiled after being
  cut into `link_sixth`, `link_of_three_faces`, `no_triangle_at`, `closure_of_links`.
- For an iff between two 8-fold disjunctions of equalities (`Edge p q r s u t ↔
  Edge q p s r u t`) `tauto` succeeds in seconds and `omega` times out at 1000000 heartbeats —
  the opposite of the usual advice.  Prove the two dihedral generators (`edge_rot`, `edge_rev`)
  once with `tauto` and get every other instance by `Iff.trans`, which is free.
- Conversely, for *deriving* a fact from such a disjunction (`edge_nbr`, `edge_no_triangle`)
  `omega` is the right tool, provided you `clear * - <the 5-8 facts it needs>` first.
- `omega` treats each `a ≠ b` as a disjunction and is exponential in their number.  Fifteen
  disequalities in context made `¬(v = a ∨ v = b ∨ v = c ∨ v = d ∨ v = e)` time out; with
  `clear * - n1 n2 n3 n4 n5` it is instant.  Pass pairwise-distinctness into a lemma as ONE
  conjunction and destructure it, so each `omega` can keep exactly the conjuncts it needs.
- Provide small combinatorial witnesses as closed terms, not tactics: `edge_pq p q r s :=
  Or.inl ⟨rfl, rfl⟩` costs nothing, `by simp [Edge]` costs heartbeats every time it is used.
- `lake env lean R3/File.lean` remains the fast iteration loop (~1.5 min/file here).

## 2026-09-13 (task 20, rotation 1 — the F(11) generalisation and `link_types`)
- **`ac_rfl` works for `Nat` xor** and is the right tool for every permutation of an xor
  expression: `example (A B C D : ℕ) : A ^^^ B ^^^ C ^^^ D = C ^^^ A ^^^ D ^^^ B := by ac_rfl`
  succeeds.  `Nat.xor_left_comm` does NOT exist (a locally proved `a ^^^ (b ^^^ c) =
  b ^^^ (a ^^^ c)` added to `simp [Nat.xor_assoc, Nat.xor_comm, _]` also normalises, but
  `ac_rfl` is shorter).  The idiom for a permuted hypothesis is
  `have hx' : <permuted> = 0 := by rw [← hxor]; try ac_rfl` — the `try` is needed because on
  the identity permutation `rw` already closes the goal by `rfl` and a bare `ac_rfl` then
  errors with "No goals to be solved".
- `rcases h with rfl | rfl` on a disjunction of equations between two *variables*
  (`a1 = a2 ∨ a1 = b2`) eliminates whichever variable Lean picks, so later references to the
  other name fail with "Unknown identifier".  Name the equation (`with he | he`) and use
  `rw [he]` in each component instead; it is deterministic.
- `rw [Bool.not_eq_true] at k` fails when `k : e ≠ true` (the `Ne` does not expose the
  `¬ _ = true` pattern to `rw`).  Use `cases hb : e with | false => rfl | true => exact absurd hb k`.
- A lemma whose implicit argument appears only in a hypothesis you postpone with `?_` cannot
  have that implicit inferred: `refine (lemma h1 h2 ?_).elim` fails with "don't know how to
  synthesize implicit argument".  Pass it: `refine (lemma (a := b) h1 h2 ?_).elim`.
- `Finset.card_filter` rewrites `card n T` (a filter card) into `∑ i ∈ range n, if _ then 1 else 0`.
  That turns parity statements into `Finset.dvd_sum` plus a four-way `cases … <;> norm_num`,
  which is how `card_xor_four_parity` is proved in one short block.  This single lemma
  ("with xor 0 the four sizes sum to an even number") removes every "odd number of
  singletons" branch of the L1..L4 classification in one line each.
- **The gate's laundering scan greps all of `R3/`, including `R3/WIP.lean`, even though
  `WIP.lean` is not imported.**  A `sorry` parked in WIP will fail `gate.sh` while `lake build`
  still passes.  Keep WIP free of banned constructs.
- `lake build` + the axiom audit together take ~25-30 min here (the audit re-elaborates
  `import Mathlib`), so budget one gate run per lemma group, not per lemma; iterate with
  `lake env lean R3/WIP.lean` (~1.5 min).

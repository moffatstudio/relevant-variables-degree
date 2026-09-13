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

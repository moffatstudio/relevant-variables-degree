# Toolchain notes from the delta = 2 lane (task 22, 2026-09-13) — merge into TOOLCHAIN_NOTES.md

- **`^^^` on `ℕ` is `infixl`.**  `a ^^^ b ^^^ c` is `(a ^^^ b) ^^^ c`, so a chain built by
  repeated `rw [chi_mul]` already matches the surface syntax and no `ac_rfl` is needed.
  Correspondingly `Nat.xor_lt_two_pow` must be nested to the LEFT:
  `Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ha hb) hc`, not to the right.
- **`push_cast` silently normalises `2 ^ 11` to `2048` inside a hypothesis**, after which
  `linarith`/`omega` see `range 2048` and `range (2 ^ 11)` as different atoms and fail on a
  goal that looks provable.  Two fixes: `rw [show (2:ℕ) ^ 11 = 2048 from by norm_num]` in the
  goal as well, or (better) `set R := <the big sum> with hR` BEFORE `push_cast`, so the sum is
  an opaque variable and every side condition stays linear.
- **Never name a hypothesis `Ne`.**  It shadows `Ne` / `Ne.symm` and `rw [Ne, ...]`, producing
  a shower of "Application type mismatch" and "Invalid rewrite argument: `Ne ?a` is a proof of"
  errors far from the real cause.  Use `ne_eq` in `rw` to unfold `a ≠ b` to `¬ a = b`.
- **Four distinct values drawn from a four-element list**: do NOT `rcases` into 256 branches.
  `{T1,T2,T3,T4} ⊆ {A,B,C,D}`, the left card is 4 (`card_insert_of_notMem` twice +
  `card_pair`), the right card is ≤ 4, then `Finset.eq_of_subset_of_card_le` gives set equality
  and every one of `A,B,C,D` is some `T_i`.  Instant; see `four_distinct_exhaust`.
- `Finset.not_mem_erase` is deprecated in favour of `Finset.notMem_erase`; `ne_of_mem_erase`
  (`a ∈ s.erase b → a ≠ b`) is the clean way to get distinctness out of an `erase`, and
  `rw [hTs]` inside a `have : x ∈ (s.erase b)` goal fails once `b` has been substituted — bind
  the membership facts (`hT1e`, `hT2e`) immediately after `card_eq_two.mp` instead.
- `rw [h]` where `h : S = e` and the goal mentions `S` works; the mirror `rw [← h]` is needed
  when `congrArg` + `simpa` produced the equation the other way round.  Read the direction off
  the error's "target expression" line rather than guessing.
- A 64-way `rcases ... <;> revert h <;> norm_num` (the six-`±1` sign lemma `six_pm_sum`) is
  fine on this machine; no heartbeat bump needed.  Likewise a 128-way
  `cases <bool> <;> ... <;> rfl` for a seven-variable `Bool` xor identity
  (`xor_two_pow_cancel6`) is instant, and is much more robust than fighting xor associativity
  lemmas.
- `lake build R3.<Module>` builds one module and its dependencies only (~90 s here) and is the
  right way to produce the `.olean` for a NEW file so that `lake env lean` on a file importing
  it works.  It is not a full `lake build` and it is RAM-cheap.

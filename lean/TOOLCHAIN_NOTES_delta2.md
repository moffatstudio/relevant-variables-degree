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

## Rotation 2 notes (task 27)

- **Do not write a long Lean chunk inside a bash heredoc.**  A chunk containing `link_sixth'`
  and friends breaks `<<'PY'` quoting on this shell.  Write the Lean text to a scratch file
  with the `Write` tool and splice it in with a one-line `python -c` that reads that file.
- **`Edge` is a bare 8-way disjunction of equalities**, so every "this pair is an edge of that
  4-cycle" goal is discharged by `by unfold Edge; omega` — no need for `edge_pq`/`edge_rs`.
  Likewise `edge_nbr ... E` followed by `clear * - k <the few ne facts>; omega` decides which
  vertex of a 4-cycle a given vertex is.
- **`edge_rot` makes the four "which vertex of the cycle is `v`" cases collapse to one.**  In
  `other_nbr` the case analysis is a single `gen` helper applied to `(p,q,r,s)`, `(q,r,s,p)`,
  `(r,s,p,q)`, `(s,p,q,r)`, transporting the link iff by `(hL ...).trans edge_rot` (chained).
  Writing the four cases out costs four copies of the same 20-line proof.
- **The hand proof's `five_pairs_cycle` is avoidable.**  Degree 2 in the link of `v` is not a
  graph-theoretic fact to be proved from "five pairs with xor 0"; it falls straight out of
  `link_struct'` at the (cubic, mass-4) neighbour — that is `other_nbr`.  Building the actual
  5-cycle is never needed: four faces plus a "the fifth face has nowhere to go" count closes it.
- `tri_ext (fun _ => by omega)` rearranges any `tri` to any permutation of itself; used as
  `rw [show tri a b c = tri b a c from tri_ext (fun _ => by omega)]` dozens of times here.
- `tri_ne_bit` (a triple containing a bit the other triple misses) replaces every ad-hoc
  "these two faces are distinct" argument; feed it the vertex that separates them.
- `set K := {...} with hKdef` then `simp only [hKdef, mem_insert, mem_singleton] at h` is the
  reliable way to case on membership in an explicit `Finset` literal after `set` has abstracted
  it; plain `simp at h` leaves `K`.
- **Cross-lane name collisions break `lake build`, not `lake env lean`.**  `lake env lean
  R3/DeltaTwo.lean` passes happily while `R3.lean` (which imports every lane) dies with
  "environment already contains 'R3.pair_lt' from R3.DeltaTwo".  Before running the gate,
  diff the declaration names of your file against the other lanes' files; generic helper names
  (`pair_lt`, `card_quad_eq`, `tri_of_bit`, ...) are the ones that clash.
- **`ext j; simp only [...]; tauto` on a six-element `Finset` equality hits maximum recursion
  depth.**  `{A,B,C} ∪ {D,E,F} = {A,B,C,D,E,F}` is closed instantly by
  `simp only [insert_union, singleton_union]`.
- **`pgrep` does not exist in this Git Bash.**  `until ! pgrep -f lean; do ...; done` exits at
  once (command not found is a non-zero status), so it silently fails as a wait loop and an
  empty output file then reads as "no errors".  Poll the output file itself, or use a
  `for i in $(seq 1 N); do grep -q ...; sleep 15; done` loop.

# Independent search for F(n) — audit and documentation

## Purpose

`r3search2.c` is an independent, from-scratch complete search for coefficient vectors
`N : {S ⊆ [n], |S| <= 3} -> Z` satisfying the finite statement F(n) in
`../FINITE_STATEMENT.md`:

* (i) `sum_S n_S^2 = 16`
* (ii) `f_N = (1/4) sum_S n_S chi_S` is `{-1,1}`-valued on the cube
* (iii) every variable `i in [n]` is relevant.

`F(11)` true (0 solutions) implies `R_3 <= 10`; the known degree-3 function `Xi_3` with 10
relevant variables (F(10) false, unique orbit) then gives `R_3 = 10`. This search uses only
E1–E3 from `FINITE_STATEMENT.md`, never the link classification in `R3_equals_10.md`.

## r3search.c vs r3search2.c — the bug that was fixed

Both files implement the same orderly-generation algorithm (vertex-by-vertex DFS over
"links", canonical-form symmetry rejection at the end of each link). The only functional
difference is the shape of the scratch buffers `g` and `ellbuf`:

* `r3search.c`: `static int8_t g[MAXN][MAXPTS]`, `ellbuf[MAXN][MAXPTS]` — indexed **only by
  recursion depth `d`**, shared across all vertex-steps `V`.
* `r3search2.c`: `static int8_t g[MAXN][MAXN][MAXPTS]`, `ellbuf[MAXN][MAXN][MAXPTS]` —
  indexed by **`[V][d]`**, i.e. a private buffer per step `V`.

Because `step(V)` recurses into `step(V+1)` (via `do_group`/`ell_dfs`/`finish_link`) while
the *caller's* `g[d]`/`ellbuf[d]` rows are still needed after the callee returns, and the
callee reaches the same depth `d` values again for its own vertex, the shared buffers in
`r3search.c` alias and get overwritten mid-recursion. This silently drops and corrupts
branches (fewer nodes/solutions explored than the true search tree). The logs are direct
evidence: at `n=10`, `r3search.c` reports `solutions=0, leaves=2` (`search/log_n10.txt`)
while `r3search2.c` reports `solutions=1, leaves=120` (`search/log2_n10.txt`) — and the one
solution found by `r3search2` is exactly the known `Xi_3` function (the true answer, since
F(10) is known false with a unique orbit). `r3search.c`'s counts are wrong at every `n`
(compare `log_n*.txt` vs `log2_n*.txt`); it must not be used as evidence for anything.
**All results in this document are from `r3search2.c` only.**

## Algorithm and soundness of every pruning/symmetry rule

Processing vertex `v` fixes every coefficient `n_S` with `v ∈ S`. The **link**
`L_v = 4 D_v f_N = sum_{S ∋ v} n_S chi_{S\v}` is a degree-<=2 polynomial in the other
variables; by E1 it takes values in `{0,±4}` pointwise, and its mass `m_v = sum_{S∋v} n_S^2`
lies in `[4,16]` by E2 (or `m_v=0` if `v` is never used, but such `v` fails (iii)). All rules
below are stated as **necessary conditions implied by E1–E3 on any actual solution**, so
dropping a branch that violates one of them can never discard a genuine solution — each is
justified in one sentence:

* **P1 (budget)** — `used_total + qmass <= 16` and `m_v <= 16`: this is exactly (i),
  `sum n_S^2 = 16`, applied to the partial sum of squares accumulated so far; a true solution
  can never exceed it.
* **P2 (bounded conditional expectations)** — for a partial assignment of a subset `A` of the
  link's variables, the fixed-plus-chosen terms confined to `A` must keep every value of
  `g[x]` (`= L_v` restricted to `x_A`) within `[-4,4]`: this is E1 (`L_v ∈ {0,±4}`) evaluated
  at every completion of `x_A`, so any assignment driving `g` outside `[-4,4]` cannot extend
  to a valid `L_v`.
* **P3 (weighted degree)** — for a link variable `w`, `sum_{T ∋ w} |c_T| <= 4` (checked as
  `wdeg[u] > 4 -> return` and via the `cmax`/`rem` bounds in `ell_dfs`): this is the
  paper's E1 applied one derivative further, `D_w L_v ∈ {0,±2,±4}`, so `|a-b|,|a+b| <= 4`
  forces `|a|+|b| <= 4` for the two "halves" contributed by any single new term, hence the
  running weighted degree of a link variable can never exceed 4 in a genuine solution.
* **P4 (needs)** — `sum_{u not yet processed} max(0, 4 - mass_u) <= 3*(16 - used_total)`
  (checked in `finish_link`): each not-yet-processed vertex needs mass `>= 4` by E2, and any
  future coefficient `n_S` with `|S|<=3` contributes its square to at most 3 vertices, so the
  total remaining "mass debt" can never exceed 3 times the remaining budget in a genuine
  solution.
* **Symmetry / canonical form (E3 only)** — permutations of `[n]`, negation of any single
  variable, and the global sign `N -> -N` all preserve (i)-(iii) exactly (this is E3 as
  stated). The search fixes representatives by: (a) `n_∅ <= 0` (global sign used once, at the
  top, since it commutes with everything else); (b) "fresh" variables (unprocessed, appearing
  in no nonzero fixed term) are introduced in increasing label order (rule R, checked by
  `check_R_perm`); (c) among all images of the current completion under `Sym(fresh used) x
  {variable-negations of fresh vars} x {global negation of the link, when the link's fixed
  part is all-zero}`, the search keeps only the lexicographically-minimal one
  (`is_canonical`/`compare_image`). Every genuine solution has *some* image satisfying (a)-(c)
  simultaneously (composing independent symmetries of a finite group), so rejecting
  non-canonical images (`canon_rejects`) never discards an orbit, only redundant
  representatives of the same orbit — this is why raw `solutions` counts already equal
  **orbit counts**, not raw solution counts.
* **(ii) is never pruned, only checked exactly**: at the last vertex `final_check` evaluates
  `4 f_N(x)` pointwise at all `2^n` points and requires it in `{+4,-4}`; P1–P4 above are used
  only to cut branches early, and the only place a branch is *accepted* as a solution is this
  full, unpruned check.

**No rule here is unjustified** — each is a direct restatement of E1/E2/E3 from
`FINITE_STATEMENT.md`, or (for (ii)) an exact, unpruned check. See "Residual trust" below for
what this does *not* cover (implementation-correctness of the C code itself, independent of
the mathematical argument).

## Sharding of `n=11` (disjoint and exhaustive)

`n=11` is split with `-split 6 I` for `I = 0..5` (`log2_n11_s0.txt` .. `s5.txt`). In
`finish_link`, every canonical top-level link (`V==0`) increments `cand_links[0]` *before*
the split test:

```c
cand_links[V]++;
...
if (V == 0 && splitK > 1 && ((cand_links[0] - 1) % splitK) != splitI) return;
```

So **every shard enumerates the same full set of canonical top-level links** (all 6 logs
report `accepted links per step: 368 ...` — identical first entry), and each shard only
*recurses further* (does the expensive work) for the links whose 1-indexed position `k`
satisfies `(k-1) mod 6 == I`. The map `k -> (k-1) mod 6` partitions `{1,...,368}` into 6
disjoint classes whose union is everything — this is a plain integer partition-by-residue,
manifestly disjoint and exhaustive, and deterministic given the (single-threaded, fixed
iteration order) enumeration. No solution can fall between shards.

## Results table

All runs are `r3search2.exe N` (n<=10) or `r3search2.exe 11 -split 6 I` (n=11), from
`search/log2_n*.txt`. "Solutions" is already an **orbit count** under the search's own
symmetry reduction (see above), not a raw coefficient-vector count.

| n | solutions (orbits) | leaves | nodes | canon_rejects | time |
|---|---|---|---|---|---|
| 3 | 14 | 26 | 1,887 | 176 | 0.00s |
| 4 | 102 | 225 | 24,373 | 2,755 | 0.01s |
| 5 | 809 | 2,329 | 280,282 | 31,155 | 0.15s |
| 6 | 1,773 | 6,538 | 2,986,948 | 187,681 | 2.44s |
| 7 | 1,060 | 11,786 | 23,632,808 | 530,408 | 33.20s |
| 8 | 213 | 4,015 | 77,313,447 | 1,288,595 | 171.77s |
| 10 | **1** | 120 | 44,447,494 | 1,063,032 | 824.60s |
| 11 (6 shards, sum) | **0** | 16 | 96,822,409 | 3,747,449 | ~2.1 CPU-h |

`n=9` was not run (not needed for the F(11)/F(10) claims; the campaign jumped 8 -> 10 -> 11).
`n=10` giving exactly 1 orbit matches the known truth: the unique degree-3 Boolean function
with 10 relevant variables is `Xi_3` (up to the symmetry group), and the recovered solution
(`search/sol2_n10.txt`) is 16 terms of coefficient `±1`, matching `Xi_3`'s description in
`FINITE_STATEMENT.md` exactly. `F(11)` giving 0 across all 6 disjoint shards is the
independent search's verdict that `R_3 <= 10`.

`search/brute56.c` (`log_brute56.txt`) is an older, unrelated brute force over *all* labelled
degree-<=3 Boolean functions (not orbit-reduced, no link/canonical-form machinery) for
`n<=6`; it is a useful independent cross-check of raw counts at small `n` but does not scale
past `n=6` and was not used for the `n=10,11` claims.

## Verification performed

`search/verify_solutions.py` is a from-scratch, independent checker (imports nothing from
`r3search2.c` or `check_solutions.py`) that parses each `SOL` line, evaluates
`f_N = (1/4) sum_S n_S chi_S` by brute force at all `2^n` points, and checks (i) the sum of
squares is 16, (ii) `4 f_N(x) ∈ {+4,-4}` everywhere, and (iii) genuine relevance (some pair of
points differing only in coordinate `i` gives different `f_N` values — not merely "`i`
appears in some nonzero term").

```
$ python verify_solutions.py sol2_n6.txt sol2_n7.txt sol2_n8.txt sol2_n10.txt
sol2_n6.txt: 1773 solutions checked, 0 failed conditions (i)-(iii)
sol2_n7.txt: 1060 solutions checked, 0 failed conditions (i)-(iii)
sol2_n8.txt: 213 solutions checked, 0 failed conditions (i)-(iii)
sol2_n10.txt: 1 solutions checked, 0 failed conditions (i)-(iii)
TOTAL: 3047 checked, 0 failed
```

All 6 `sol2_n11_s*.txt` files are empty (0 bytes), consistent with `solutions=0` in every
`log2_n11_s*.txt` — there is nothing to run the checker on for `n=11` since the claim is
"no solutions exist", not a solution to verify.

## How to rebuild and rerun

```sh
cd search
gcc -O2 -o r3search2.exe r3search2.c        # ~1s to compile
./r3search2.exe 6                            # n<=8: seconds to ~3 minutes
./r3search2.exe 10                           # ~14 minutes (824s observed)
./r3search2.exe 11 -split 6 0                # one n=11 shard, ~21 minutes (do NOT run all 6 serially: ~2 CPU-hours total)
python verify_solutions.py sol2_n6.txt sol2_n7.txt sol2_n8.txt sol2_n10.txt
```

Expected wall-clock times (single core, as observed on this machine): `n<=8` seconds to 3
minutes; `n=10` about 14 minutes; each `n=11` shard about 20-21 minutes (6 shards, ~2
CPU-hours total if run serially — do not rerun this during a routine audit).

## Residual trust caveats

* The soundness argument above is a proof that the *pruning rules* cannot lose a solution,
  given that E1–E3 hold and given that the C code correctly implements the described bounds
  and the canonical-form test. It is **not** an independent proof that the C implementation
  is bug-free line-by-line; it is corroborated, not replaced, by:
  * the `n=10` sanity check recovering exactly 1 orbit, matching the independently known
    unique `Xi_3` solution — this is strong evidence the canonical-form/symmetry machinery
    (the most intricate part of the code) is not silently dropping or duplicating orbits at a
    scale comparable to `n=11`;
  * `verify_solutions.py` independently confirming every emitted solution at `n=6,7,8,10`
    genuinely satisfies (i)-(iii), so no *false positive* solutions are being reported;
  * the demonstrated, understood failure mode of the *un*fixed `r3search.c` (aliased buffers)
    gives a concrete example of the kind of bug this class of search is vulnerable to, and
    `r3search2.c`'s per-step buffers are a structural fix, not a patch, for exactly that
    class of bug.
  * What is **not** independently checked: a false negative at `n=11` specifically (a solution
    silently dropped by a code bug rather than a math error) cannot be ruled out by re-running
    the same binary; an independent second implementation of the full search (not just of the
    verifier) would be the next step to raise confidence further.
* The sharding argument (disjoint/exhaustive residue classes) is sound as pure arithmetic;
  it depends on the enumeration order of canonical top-level links being fixed and
  deterministic across the 6 separate process invocations, which holds since the algorithm is
  single-threaded and depends only on `n` and the (fixed) code — not on machine, timing, or
  randomness.
* No pruning rule was found to be unjustified; P1-P4 and the symmetry/canonical-form rules are
  each direct restatements of E1-E3, and (ii) is checked exactly rather than pruned.

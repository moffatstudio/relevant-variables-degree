# Relevant variables of degree-3 Boolean functions: R_3 = 10, and NS is never tight

**Status 2026-09-13.** `paper/paper.pdf` is the preprint of record for release `v0.9`. Two results:
`R_d <= d 2^{d-1} - 1` for every `d >= 3` (the Nisan–Szegedy bound is never attained), and `R_3 = 10`
exactly. Both hand proofs passed independent referee rounds; the exhaustive search independently
confirms the finite statement behind `R_3 <= 10`. The Lean project certifies the structural half of
the argument, not the two headline theorems.

Campaign `opt-c44-relevant-variables-degree`, 12–13 September 2026. The mathematics was developed
with AI assistance: Claude (Anthropic) agents under the author's direction.

Each claim below is marked **[proof, refereed]**, **[audited computation]**, **[machine-checked in
Lean]** or **[not machine-checked]**.

## 1. Setting

For a Boolean function `f : {-1,1}^n -> {-1,1}` of real multilinear degree `d`, Nisan and Szegedy
proved that the number of relevant variables is at most `d 2^{d-1}`; for `d = 3` this reads
`R_3 <= 12`. The Chiarelli–Hatami–Saks style function

```
Xi_3 = ((s+t)/2) Xi_2(x) + ((s-t)/2) Xi_2(y),    Xi_2(a,b,c,d) = ((a+b)/2) c + ((a-b)/2) d
```

has degree 3 and 10 relevant variables, so `10 <= R_3 <= 12`. The gap is closed here.

## 2. Results

**Theorem A (NS never tight) [proof, refereed] — `proofs/NS_never_tight.md`.** For every `d >= 3`,
`R_d <= d 2^{d-1} - 1`. The engine is Lemma A: in a hypothetical extremal function, a derivative of
minimal influence is a character times the indicator of an affine subspace. Referee verdict PASS
(`referee/REPORT_ns.md`); Lemma A was additionally brute-forced for `m = 2, 3` over 343M instances
(`referee/ns_lemmaA.py`, `referee/out_ns_lemmaA.txt`). Specialised to `d = 3` this gives
`R_3 <= 11` (`proofs/R3_upper_bound.md`, referee verdict PASS in `referee/REPORT_r3.md`).

**Theorem B (R_3 = 10) [proof, refereed] — `proofs/R3_equals_10.md`.** No degree-3 Boolean function
has 11 relevant variables; with `Xi_3`, `R_3 = 10`. The proof works with the vertex masses
`m_v = sum_{S ∋ v} n_S^2` of the integer coefficient vector `N = 4 f^`, shows `m_v ∈ {4,6,8}` for
`n >= 11`, classifies the link of each mass-4 vertex as a 4-cycle, and closes the resulting term
hypergraph. Referee verdict PASS with fixes, all applied (`referee/REPORT_r3_round2c.md`; the full
earlier round is `referee/REPORT_r3_full.md`).

**Independent confirmation [audited computation] — `search/`.** `proofs/FINITE_STATEMENT.md` freezes
the finite statement `F(n)`: no integer coefficient vector on subsets of size `<= 3` satisfies
(i) `sum_S n_S^2 = 16`, (ii) the squared function is identically 1, (iii) every variable is relevant.
`F(11)` is equivalent to `R_3 <= 10`. `search/r3search2.c` is a from-scratch complete orbit-reduced
search that uses only the elementary facts E1–E3 of the frozen statement and never the link
classification of the hand proof. Verdict, across 6 disjoint shards: `F(11)` has **0 solutions**.
Corroboration: `n = 10` returns exactly one orbit, which is `Xi_3`. Every emitted solution at
`n = 3..8, 10` passes the independent checker `search/verify_solutions.py`, which re-evaluates it at
all `2^n` points. `search/README.md` justifies every pruning rule as a restatement of E1–E3, proves
the sharding disjoint and exhaustive, and states the residual trust caveats honestly: the soundness
argument covers the pruning rules, not line-by-line correctness of the C code, and a false negative
at `n = 11` caused by an implementation bug is not ruled out by rerunning the same binary. A second
independent implementation of the full search would be the next step.

| n | orbits | leaves | nodes | time |
|---|---|---|---|---|
| 3 | 14 | 26 | 1,887 | 0.00s |
| 4 | 102 | 225 | 24,373 | 0.01s |
| 5 | 809 | 2,329 | 280,282 | 0.15s |
| 6 | 1,773 | 6,538 | 2,986,948 | 2.44s |
| 7 | 1,060 | 11,786 | 23,632,808 | 33.20s |
| 8 | 213 | 4,015 | 77,313,447 | 171.77s |
| 10 | **1** (= `Xi_3`) | 120 | 44,447,494 | 824.60s |
| 11 (6 shards) | **0** | 16 | 96,822,409 | ~2.1 CPU-h |

`search/r3search.c` is the superseded predecessor, kept deliberately: it shared its scratch buffers
across recursion depths, silently dropping branches, and reported `solutions=0` at `n = 10` where the
truth is 1. Its logs are kept next to the corrected ones so the failure is visible. Nothing in this
repository relies on it.

## 3. Formal verification

`lean/` is a Lake project (Lean 4.23.0, Mathlib `v4.23.0`, commit `37df177a…`) whose statement file
`lean/R3/Statement.lean` is **frozen**: `IsSol n N` and `F n` transcribe `proofs/FINITE_STATEMENT.md`
directly, and every theorem is proved about an arbitrary `IsSol n N`.

**[machine-checked in Lean]** 23 theorems, listed verbatim with their axiom output in
`lean/AXIOMS.txt`, all reporting `[propext, Classical.choice, Quot.sound]` and nothing more. The
substantial ones: `mass_cases` (for `n >= 11` every vertex mass is 4, 6 or 8 — Lemma 1 of the hand
proof), `nine_mass_four` (at `n = 11`, at least nine vertices have mass 4), `bookkeeping` (the mass
identity `e + delta = 48 - 4n`), `mass_four_link` and `mass_four_even_degree` (the link of a mass-4
vertex), `twelve_link` and `twelve_card_three` (at `n = 12` all masses are 4 and all terms cubic —
Step 1), and `twelve_link_cycle` (at `n = 12` every vertex link is a 4-cycle — Step 2), which is the
top certified theorem.

The gate is `bash lean/gate.sh`: `lake build`, a laundering scan over the sources for `sorry`,
`admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` and `@[extern]`, then `#print axioms`
on all 23 declarations. Last run: GATE PASS (`lean/GATE.txt`). The same gate runs in CI.

**[not machine-checked]** `F(12)` and `F(11)` themselves, hence `R_3 <= 11` and `R_3 = 10` as formal
statements; the reduction from degree-3 Boolean functions to `F(n)` (the `2^{1-d}` granularity of the
Fourier coefficients), which is stated in `proofs/FINITE_STATEMENT.md` and used as the bridge, not
formalised; and Theorem A for general `d`. Work on `F(12)` (Steps 3 and 4: closure to two
vertex-disjoint octahedra, then the contradiction from CondII) is **in progress**; `lean/PLAN.md`
gives the route and the estimates. `lean/R3/Octahedron.lean` and `lean/R3/WIP.lean` are that
in-progress work: they are not imported by `R3.lean`, not built by `lake build`, and not covered by
the gate.

## 4. What remains open

- A machine-checked `F(11)`, and with it a fully formal `R_3 = 10`.
- A second, independent implementation of the `n = 11` search, to close the false-negative caveat.
- `R_4`: the Nisan–Szegedy bound gives 32 and Theorem A gives 31; no matching construction is known.
  Branching architectures give exactly `3·2^{d-1} - 2` relevant variables, which is 22 at `d = 4`
  (claim C3 of the campaign, reasoning only, not written up here).

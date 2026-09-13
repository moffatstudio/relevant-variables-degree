# The Nisan–Szegedy bound on relevant variables is never tight, and R_3 = 10

[![verify](https://github.com/moffatstudio/relevant-variables-degree/actions/workflows/verify.yml/badge.svg)](https://github.com/moffatstudio/relevant-variables-degree/actions/workflows/verify.yml) [![lean](https://github.com/moffatstudio/relevant-variables-degree/actions/workflows/lean.yml/badge.svg)](https://github.com/moffatstudio/relevant-variables-degree/actions/workflows/lean.yml)

Andrew Moffat, 13 September 2026. Paper: [`paper/paper.pdf`](paper/paper.pdf) (source [`paper/main.tex`](paper/main.tex), build instructions [`paper/BUILD.md`](paper/BUILD.md)). Preprint, not peer-reviewed. Intended for math.CO (cross-list cs.CC); MSC 06E30, 68Q06, 05D05. Not yet on arXiv.

Let `R_d` be the maximum number of relevant variables of a Boolean function `f : {-1,1}^n -> {-1,1}` of real multilinear degree `d`. Nisan and Szegedy proved `R_d <= d 2^{d-1}`, which gives `R_3 <= 12`. This repository holds everything needed to check two results: that the Nisan–Szegedy bound is **never** attained for `d >= 3`, and that `R_3 = 10` exactly. It contains the paper, the hand proofs, the complete search and every raw log, the reports of the independent referee rounds (including the errors they caught), and a Lean 4 project certifying the structural half of the argument. Nothing was removed to tidy the story.

## Check it in a few minutes

```
python verify.py
```

`verify.py` needs only Python 3.10+ and `gcc`; there are no third-party dependencies. It compiles the audited complete search [`search/r3search2.c`](search/r3search2.c), reruns it for `n = 3..8`, compares the orbit counts it reports against the published table in [`search/README.md`](search/README.md), and then hands every solution the rerun emitted to the independent checker [`search/verify_solutions.py`](search/verify_solutions.py), which re-evaluates each one at all `2^n` points of the cube against conditions (i)–(iii) of the frozen finite statement `F(n)`. About three minutes in total, `n = 8` accounting for most of it. `python verify.py --n10` adds `n = 10` (about 14 minutes) and reproduces the unique solution, the CHS function `Xi_3`. `python verify.py --lean` also runs the Lean gate if `lake` is installed. It exits non-zero on any discrepancy, and the same script runs in CI on every push (badge above).

The `n = 11` search itself, whose verdict `F(11) = 0 solutions` is what gives `R_3 <= 10`, is **not** rerun by `verify.py`: it is 6 shards and about 2 CPU-hours. Its raw logs are `search/log2_n11_s*.txt`, and the disjointness-and-exhaustiveness argument for the sharding is in `search/README.md`.

## What is proved, and at what tier

| Claim | Where | Tier |
|---|---|---|
| **NS never tight.** For every `d >= 3`, `R_d <= d 2^{d-1} - 1`; in particular `R_3 <= 11`. Lemma A: a minimal-influence derivative is a character times the indicator of an affine subspace | `proofs/NS_never_tight.md`, `proofs/R3_upper_bound.md` | **Proof**, refereed (`referee/REPORT_ns.md`, `referee/REPORT_r3.md`). Lemma A additionally brute-forced for `m = 2, 3` (343M instances) |
| **R_3 = 10.** No degree-3 Boolean function has 11 relevant variables; the CHS function `Xi_3` has 10 | `proofs/R3_equals_10.md` | **Proof**, refereed with fixes applied (`referee/REPORT_r3_round2c.md`) |
| **`F(11)` has no solution** — an independent complete search confirming `R_3 <= 10` without using the hand proof's link classification | `search/` | **Audited computation.** Complete orbit-reduced search using only E1–E3 of the frozen statement; every pruning rule justified in `search/README.md`; `n = 10` sanity check recovers `Xi_3` uniquely; residual trust caveats stated there |
| 23 structural theorems on the road to `F(12)` and `F(11)` | `lean/` | **Machine-checked in Lean 4 / Mathlib**, zero `sorry`, standard axioms only, no `native_decide` |
| `F(12)` and `F(11)` themselves in Lean | — | **Not machine-checked.** In progress; see `lean/PLAN.md` |

`R_3 = 10` rests on the hand proof in `proofs/R3_equals_10.md`, refereed by independent agents, and is corroborated by the exhaustive search. It is not yet machine-checked end to end, and this repository does not claim otherwise.

## Formal verification (Lean 4)

[`lean/`](lean/) is a Lake project (Lean 4.23.0, Mathlib pinned at `v4.23.0`, commit `37df177aaa770670452312393d4e84aaad56e7b6`) built on a **frozen** statement of the finite problem. Everything is proved about an arbitrary solution of that statement, so nothing can be laundered through a convenient definition. Verbatim from [`lean/R3/Statement.lean`](lean/R3/Statement.lean):

```lean
/-- number of elements of the subset of [n] encoded by the bitmask `S` -/
def card (n S : ℕ) : ℕ := ((range n).filter fun i => S.testBit i).card

/-- `N` is supported on subsets of size ≤ 3 -/
def IsCoeffVec (n : ℕ) (N : ℕ → ℤ) : Prop :=
  ∀ S, S < 2 ^ n → 3 < card n S → N S = 0

/-- (i)  ∑_S n_S² = 16 -/
def CondI (n : ℕ) (N : ℕ → ℤ) : Prop :=
  ∑ S ∈ range (2 ^ n), (N S) ^ 2 = 16

/-- (ii) for every nonempty U ⊆ [n], ∑_{(S,T) : S Δ T = U} n_S n_T = 0 -/
def CondII (n : ℕ) (N : ℕ → ℤ) : Prop :=
  ∀ U, 0 < U → U < 2 ^ n →
    ∑ S ∈ range (2 ^ n), ∑ T ∈ range (2 ^ n), (if S ^^^ T = U then N S * N T else 0) = 0

/-- (iii) every variable is relevant -/
def CondIII (n : ℕ) (N : ℕ → ℤ) : Prop :=
  ∀ i, i < n → ∃ S, S < 2 ^ n ∧ S.testBit i ∧ N S ≠ 0

/-- a solution of the finite problem on n variables -/
def IsSol (n : ℕ) (N : ℕ → ℤ) : Prop :=
  IsCoeffVec n N ∧ CondI n N ∧ CondII n N ∧ CondIII n N

/-- The finite statement F(n). -/
def F (n : ℕ) : Prop := ¬ ∃ N : ℕ → ℤ, IsSol n N
```

`F(n)` is equivalent to "no degree-3 Boolean function has `n` relevant variables"; the equivalence, a two-line consequence of the standard `2^{1-d}` granularity of the Fourier coefficients, is stated in [`proofs/FINITE_STATEMENT.md`](proofs/FINITE_STATEMENT.md) and is not itself formalised. `F(11)` gives `R_3 <= 10`.

Neither `F(11)` nor `F(12)` is proved in Lean yet. What is certified is the structural road to them — 23 theorems, all about an arbitrary `IsSol n N`. The strongest, verbatim from the sources:

```lean
-- lean/R3/Mass.lean — Lemma 1: at n ≥ 11 every vertex mass is 4, 6 or 8
theorem mass_cases {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hn : 11 ≤ n) {v : ℕ}
    (hv : v < n) : mass n N v = 4 ∨ mass n N v = 6 ∨ mass n N v = 8

-- lean/R3/Mass.lean — at n = 11 at least nine vertices have mass exactly 4
theorem nine_mass_four {N : ℕ → ℤ} (hsol : IsSol 11 N) :
    9 ≤ ((range 11).filter fun v => mass 11 N v = 4).card

-- lean/R3/Twelve.lean — n = 12, Step 1: four cubic support sets of coefficient ±1 per vertex
theorem twelve_link {N : ℕ → ℤ} (hsol : IsSol 12 N) {v : ℕ} (hv : v < 12) :
    ∃ a b c d : ℕ, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      supp 12 N v = {a, b, c, d} ∧
      (∀ S ∈ ({a, b, c, d} : Finset ℕ), S < 2 ^ 12 ∧ S.testBit v = true ∧
          (N S = 1 ∨ N S = -1) ∧ card 12 S = 3 ∧ card 12 (S ^^^ 2 ^ v) = 2) ∧
      (a ^^^ 2 ^ v) ^^^ (b ^^^ 2 ^ v) ^^^ (c ^^^ 2 ^ v) ^^^ (d ^^^ 2 ^ v) = 0 ∧
      N a * N b * N c * N d = 1

-- lean/R3/Cycle.lean — n = 12, Step 2: every vertex link is a 4-cycle (top certified theorem)
theorem twelve_link_cycle {N : ℕ → ℤ} (hsol : IsSol 12 N) {v : ℕ} (hv : v < 12) :
    ∃ p q r s, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
      ∀ S ∈ supp 12 N v, OnCycle p q r s (S ^^^ 2 ^ v)
```

All 23 declarations report

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. nothing beyond Lean's standard three. The full list and the verbatim output are in [`lean/AXIOMS.txt`](lean/AXIOMS.txt) and the dated gate run in [`lean/GATE.txt`](lean/GATE.txt).

**Running the gate.** From a fresh clone (needs network for Mathlib and its `olean` cache):

```bash
cd lean
lake exe cache get
lake build
bash gate.sh
```

`gate.sh` exits `0` only if the build succeeds, no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `@[extern]` occurs anywhere in the sources, and every one of the 23 declarations depends on no axiom beyond the standard three. The same gate runs in GitHub Actions (badge above). See [`lean/README.md`](lean/README.md) for the module map and [`lean/PLAN.md`](lean/PLAN.md) for what remains.

## Layout

```
paper/          main.tex, refs.bib, main.pdf (paper.pdf is a copy), BUILD.md
proofs/         NS_never_tight.md (NS never tight, Lemma A), R3_upper_bound.md (R_3 <= 11),
                R3_equals_10.md (R_3 = 10), FINITE_STATEMENT.md (the frozen statement F(n))
search/         r3search2.c (the audited complete search) and its logs log2_*.txt and
                solutions sol2_*.txt; verify_solutions.py (independent checker);
                r3search.c (the buggy predecessor, kept with its logs log_*.txt and a
                written account of the aliasing bug); brute56.c (small-n cross-check);
                README.md (algorithm, soundness of every pruning rule, results, caveats)
referee/        REPORT_*.md from the independent referee rounds, and every check script
                and output the referees wrote
lean/           Lean 4 / Mathlib project: frozen F(n) plus 23 certified structural theorems;
                gate.sh, GATE.txt, AXIOMS.txt, PLAN.md, HANDOFF.md, TOOLCHAIN_NOTES.md
verify.py       one-command verification of the search
RESULT.md       per-claim result summary with tiers
```

## How this was produced (AI disclosure)

The mathematics was developed with AI assistance: a team of Claude (Anthropic) language-model agents working under the author's direction, who set the goal and the standard of evidence, checked the claims and decided what to publish. Separate agents wrote the search, refereed the manuscript over several rounds, and built the Lean project. Every error a referee caught is documented in `referee/`, and the buggy first search (`search/r3search.c`) is kept in the repository with an account of its failure mode rather than deleted.

## Licence and citation

Code, logs and solution files: MIT. Paper, proofs and reports: CC BY 4.0. See `LICENSE` and `CITATION.cff`.

Corrections are welcome: open an issue, or email the address on the paper.

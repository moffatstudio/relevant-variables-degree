# Machine-checked certificate — F(11) and F(12)

Date: 2026-09-13 (from-scratch gate run 2026-09-13T23:17:45Z).

## What is certified

Two Lean 4 theorems, both closed under the frozen finite statement in `R3/Statement.lean`:

| theorem | file | statement |
|---|---|---|
| `R3.F_eleven` | `R3/Eleven.lean` | `F 11` |
| `R3.F_twelve` | `R3/Final.lean` | `F 12` |
| `R3.F_eleven_and_twelve` | `R3/Eleven.lean` | `F 11 ∧ F 12` |

with (frozen, never edited by any lane)

```lean
def F (n : ℕ) : Prop := ¬ ∃ N : ℕ → ℤ, IsSol n N

def IsSol (n : ℕ) (N : ℕ → ℤ) : Prop :=
  IsCoeffVec n N ∧ CondI n N ∧ CondII n N ∧ CondIII n N
```

`IsCoeffVec n N` : `N` vanishes on bitmasks `S < 2^n` with `card n S > 3`.
`CondI n N`   : `∑_{S < 2^n} (N S)^2 = 16`.
`CondII n N`  : for every `U` with `0 < U < 2^n`, `∑_{S,T < 2^n, S ^^^ T = U} N S * N T = 0`.
`CondIII n N` : every `i < n` lies in some `S < 2^n` with `N S ≠ 0`.

## Structure of the `F 11` proof

`R3.bookkeeping` at `n = 11` gives

```
∑_{v<11} (mass v − 4)  +  ∑_{S<2^11} (3 − |S|) (N S)^2  =  4
```

Both sums are termwise nonnegative: `R3.four_le_mass` for the left one, `IsCoeffVec`
for the right one (`R3.excess_nonneg`). `R3.mass_cases` gives `mass v ∈ {4,6,8}`.
So the mass profile at `n = 11` is one of three, each already closed:

* all masses 4 — `R3.eleven_delta_four`
* one mass 6, the rest 4 — `R3.eleven_delta_two`
* one mass 8, or two masses 6 — then the left sum is ≥ 4, so the excess is 0, so every
  supported set has size exactly 3 (`R3.cubic_of_excess_le_zero`), i.e. `Cubic 11 N` —
  `R3.eleven_delta_zero`

## What is NOT certified

The reduction from the original statement — "a degree-3 Boolean function with 11 relevant
variables" — to `F(11)` is a paper argument (Fourier granularity: the Fourier support of a
degree-3 function, the 16-norm normalisation, and the correlation conditions). It is written
up in `FINITE_STATEMENT.md` and refereed there, not in Lean. Lean certifies only the finite
combinatorial statement `F(n)` above, at `n = 11` and `n = 12`.

## Axioms

Every one of the 158 audited theorems, `F_eleven` and `F_twelve` included, reports

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

which are the three standard Lean/Mathlib axioms. No `sorry`, no `native_decide`, no
`admit`, no user `axiom`, no `unsafe`, no `implemented_by`, no `@[extern]`; the gate scans
for all of these. Independent raw check over every source file:

```
$ grep -rn "sorry\|native_decide\|admit\|axiom " R3/*.lean R3.lean
R3/WIP_delta0.lean:1:/-! Scratch for the delta = 0 lane.  NOT imported by R3.lean.  Keep free of `sorry`. -/
```

The single hit is a prose comment in a scratch file that `R3.lean` does not import.

## Toolchain

| item | version |
|---|---|
| Lean | leanprover/lean4:v4.23.0 |
| Lake | 5.0.0-src+50aaf68 |
| Mathlib | `C:/ml/mathlib` @ 37df177, toolchain v4.23.0 |

## Rerun

```
cd <campaign>/lean
bash gate.sh
```

Wall time 22m10s on the development machine for a from-scratch rebuild of the whole `R3`
library (Mathlib oleans reused); 4m31s incremental.
The gate writes `GATE.txt` and `AXIOMS.txt`, and exits 0 iff `lake build` succeeds, the
laundering scan finds nothing, and all 158 `#print axioms` lines are clean. Last run:
`GATE: PASS`.

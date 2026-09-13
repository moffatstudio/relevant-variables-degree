# Integration instructions for the delta = 2 lane (task 27, rotation 2, 2026-09-13)

## 1. `lean/R3.lean` — already correct, no edit needed

`import R3.LinkSix` and `import R3.DeltaTwo` are already present, and `import R3.DeltaFour`
already precedes `import R3.DeltaTwo`, which is what the new
`import R3.DeltaFour` at the top of `R3/DeltaTwo.lean` requires.

## 2. `lean/gate.sh` — theorem names (done by this lane)

Rotation 1 added 15 names.  Rotation 2 adds these 18:

```
R3.one_linear_no_quad
R3.one_linear_no_const
R3.cubicAt_of_one_linear
R3.tri_link_absurd
R3.common_sixth
R3.supp_tri
R3.pair_tri_xor
R3.tri_ne_of
R3.tri_ne_bit
R3.tri_apex_common
R3.link_nbrs_of_v
R3.eleven_delta_two_lin_four
R3.tri_of_bit
R3.two_pow_ne_tri
R3.other_nbr
R3.tri_degen
R3.eleven_delta_two_lin_six
R3.eleven_delta_two
```

`R3.eleven_delta_two` is the case theorem the top-level `R3 = 10` assembly consumes:

```
theorem eleven_delta_two {N : ℕ → ℤ} (hsol : IsSol 11 N) {v : ℕ} (hv : v < 11)
    (h6 : mass 11 N v = 6) (hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4) : False
```

## 3. Nothing else

`R3/Statement.lean`, `R3/Final.lean`, `R3/Octahedron.lean`, `R3/DeltaFour.lean` and every
other existing file are untouched by this lane.  `R3/WIP_delta2.lean` is not imported and
contains no banned constructs.

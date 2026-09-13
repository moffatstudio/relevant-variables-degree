# Integration instructions for the delta = 2 lane (task 22, 2026-09-13)

## 1. `lean/R3.lean` — add these two import lines (order matters, LinkSix before DeltaTwo)

```
import R3.LinkSix
import R3.DeltaTwo
```

Put them after `import R3.LinkTypes` and after `import R3.Final`
(`R3/DeltaTwo.lean` imports both `R3.LinkSix` and `R3.Final`).

## 2. `lean/gate.sh` — add these theorem names to the `#print axioms` list

From `R3/LinkSix.lean`:

```
R3.mass_six_pm
R3.mass_six_card
R3.mass_six
R3.mass_six_link
R3.card_eq_six
R3.six_pm_sum
R3.xor_two_pow_cancel6
```

From `R3/DeltaTwo.lean`:

```
R3.four_distinct_exhaust
R3.delta_two_weight
R3.three_quadratics_absurd
R3.two_quadratics_at
R3.exists_quadratic
R3.quad_three_of
R3.eleven_delta_two_quad
R3.delta_two_linear
```

(15 new gated theorems, taking the gate list from 42 to 57.)

## 3. Nothing else

`R3/Statement.lean`, `R3/Final.lean`, `R3/Octahedron.lean` and every other existing file are
untouched by this lane.  `R3/WIP_delta2.lean` is NOT imported and contains no banned
constructs, but the gate's laundering scan greps all of `R3/`, so it must stay `sorry`-free.

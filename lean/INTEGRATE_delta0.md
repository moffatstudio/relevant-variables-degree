# INTEGRATE — delta = 0 lane (task 23, rotation 1)

## New file
`lean/R3/DeltaZero.lean` (owned by the delta = 0 lane).  Imports `R3.Final` and
`R3.LinkTypes` only.  No `sorry`, no `native_decide`.  Verified with
`lake env lean R3/DeltaZero.lean` (clean, ~75 s).

## Line for `R3.lean`
Add after the `DeltaFour` import (order does not matter, it only needs `Final`/`LinkTypes`):

    import R3.DeltaZero

## Lines for `gate.sh`'s `#print axioms` list (8 new entries)

    R3.near_self
    R3.closure_near
    R3.closure_kills
    R3.delta_zero_residual
    R3.edge_second
    R3.edge_not_three
    R3.pair_second
    R3.pair_not_three
    R3.eleven_delta_zero_residual

(`Nbr` and `Near` are definitions, not theorems.)

## What is NOT here
`eleven_delta_zero` is **not** proved.  Nothing in `R3.lean` or `gate.sh` depends on this
file, so merging it cannot break the existing `F_twelve` gate.

## Name clashes to check before merging
`Nbr` and `Near` are new top-level names in namespace `R3`; `edge_second` / `edge_not_three` /
`pair_second` / `pair_not_three` likewise.  None of them appear in the modules that existed at
the start of this run (checked by grep over `lean/R3/`), but the delta = 2 and delta = 4 lanes
are editing in parallel — re-grep at merge time.

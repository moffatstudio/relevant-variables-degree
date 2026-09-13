# HANDOFF — delta = 0 lane (task 28, rotation 3, 2026-09-13)

## State: DONE.  `eleven_delta_zero` is proved and accepted.

    theorem eleven_delta_zero {N : ℕ → ℤ} (hsol : IsSol 11 N) (hcub : Cubic 11 N) : False

`lean/R3/DeltaZero.lean` (1388 lines) is accepted by `lake env lean R3/DeltaZero.lean`
(~80 s).  No `sorry`, no `native_decide`, no raised heartbeat limit.  `#print axioms` gives
`propext, Classical.choice, Quot.sound` for every new theorem.  Nothing is left for this
lane; `INTEGRATE_delta0.md` has the import line and the full theorem list.

## The proof that was actually used — and what it replaced

`DELTA0_TOPOLOGY_FREE.md`'s plan for `(6, 6, 4^9)` asked for a six-pair cycle classification
(`C_6` vs `C_3 + C_3`), the referee's bowtie sub-case `deg(w) = 4`, and an 8-set closure
argument.  **None of that was needed.**  The previous rotation estimated 15-25 agent-hours,
almost all of it in the classification; the route below took about three hours.

The whole `(6, 6, 4^9)` branch runs off one observation: `octa_kill` never uses the link of
`b'`, and never uses the mass of the apex `v`.  So the kill fires as soon as the apex `y` of
`octa_half` and *one* of the two second-neighbours `a'`, `b'` are ordinary (mass 4).  With
only two exceptional vertices `v, w` available, that is almost always the case, and the rest
is bookkeeping.

1. **`octa_kill4`** — `octa_kill` restated on the four links `link a`, `link b`, `link y`,
   `link a'` (new `Octa4`); `octa_kill` is now a three-line wrapper.  `octa_kill4'` is the
   mirror (`a ↔ b`, `a' ↔ b'`), obtained from `dist6_swap` and `linkIs_rev`.
2. **`apex_other` (D1)** — if `{v, a, b}` is a support triple with `a, b` ordinary, the
   `octa_half` apex is *the other exceptional vertex* `w`: if it were ordinary, `link y` and
   then `link a'` (or, if `a' = w`, `link b'`) are forced and `octa_kill4` fires.  Returns
   `LinkIs n N a b v b' w` and `LinkIs n N b a v a' w`.
3. **`no_exc_pair` (D2)** — no support triple contains both `v` and `w`.  (The second
   `v`-triple at the third vertex `u` has apex `w` by D1, so `link u = d-v-b'-w` puts `v` and
   `w` opposite on a 4-cycle, and `{u, v, w}` is not a face.)
4. **`apex_gen` (D3)** — the same kill at an **arbitrary** apex `x`: for any support triple
   `{x, a, b}` with `a, b` ordinary, one of `{v,a,b}`, `{w,a,b}`, `{v,b,x}`, `{w,b,x}` is in
   the support (the apex `y` or the second neighbour `a'` must be exceptional).
5. **`kill_pair` (D4)** — if `{e, s, t}` is a support triple with `e` exceptional and `s, t`
   ordinary, then by D1 `link s = t-e-t'-e₂`, so `t`'s only neighbours in `link s` are the
   two exceptional vertices: no ordinary `u` completes the pair `{s, t}`.
6. **`kill_free_triple` (D5)** — D3 + D4: a support triple of three ordinary vertices is
   impossible.
7. **`exists_free_set` (D6)** — by D2 the supports of `v` and `w` are disjoint, so they carry
   `mass v + mass w = 12` of the total weight `16` of `CondI`; some support set contains
   neither.
8. **`eleven_delta_zero`** — D6 gives that set, `Cubic` makes it a triple of ordinary
   vertices, D5 kills it.

## Consequence for the paper / the hand proof

The `(6, 6, 4^9)` section of `DELTA0_TOPOLOGY_FREE.md` should be replaced wholesale by steps
1-8 above.  In particular the referee's bowtie finding (finding 1) is moot: the case never
arises in this route, because the argument never classifies `link(v)` at all.  Nothing in the
argument is special to `n = 11` except the final weight count `6 + 6 < 16`, and nothing is
special to the degree sequence except "at most two vertices of mass ≠ 4".

## Next steps (for the captain, not for this lane)

1. Add `import R3.DeltaZero` to `R3.lean` and re-run `gate.sh` once the delta = 2 lane is
   quiet (RAM).  Check the name-clash list in `INTEGRATE_delta0.md` first.
2. Glue: `F(11)` still needs delta = 2 and delta = 4.  `lean/R3/Glued.lean` is untouched and
   still free for whoever assembles them.
3. Referee pass on the new argument (it is shorter than the refereed plan, so the existing
   `referee/REPORT_delta0.md` no longer covers it).

## Gotchas
See `TOOLCHAIN_NOTES_delta0.md`.
